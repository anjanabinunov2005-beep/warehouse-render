import json, os, threading, time
from collections import deque
from datetime import datetime

import numpy as np
from dash import Dash, Input, Output, State, callback_context, dcc, html, no_update
from dash.exceptions import PreventUpdate
import dash_bootstrap_components as dbc

T1=3.0; T2=5.0; S1=0.8; S2=1.1
T_FIRST_ROW=1.250/S1; T_ROW_STEP=1.050/S1; T_LIFT_LVL=3.000/S2; T_TRANSFER=T1
ANIM_MS=1200; LIFT_MS=1800; MAX_QUEUE=50; PER_PAGE=10; NUM_PAGES=5

DESKTOP=os.path.join(os.path.expanduser("~"),"Desktop")
LOG_FILE=os.path.join(DESKTOP,"warehouse_log.txt")
STATE_FILE=os.path.join(DESKTOP,"warehouse_state.txt")

ROW_LBL={0:"A1",1:"A0",2:"AISLE",3:"B0",4:"B1",5:"B2",6:"B3"}
ACT_CLR={'STORE':'#66BB6A','RETRIEVE':'#42A5F5','RESTORE':'#FFA726'}
QSCLR={'PENDING':'#78909C','RUNNING':'#FFD700','DONE':'#66BB6A','ERROR':'#EF5350','ABORTED':'#FF8A65'}

_lock=threading.Lock()

wh=np.zeros((3,7,7),dtype=float)
registry={}; store_ord=[]
for _lv in range(3):
    wh[_lv,2,:]=-2; wh[_lv,3:7,2]=-1

shuttle=[0,2,6]; loaded=False; view_lvl=0; sel_dock=[1,6]; restore_md=[False]
op_times=dict(col=0.0,row=0.0,lift=0.0,xfer=0.0)
def total_t(): return sum(op_times.values())

cmd_queue=deque(); cmd_log=[]; _cid_ctr=[0]; status_txt=["READY"]; cur_page=[0]
_plan=[]; _executing=[False]; _paused=[False]; _pause_req=[False]
_on_lift=[False]; _cur_cid=[None]; _cmd_accum=[0.0]; _tick_ms=[ANIM_MS]
_last_tick=[time.time()]; _input_mode=["none"]; _pending_cell=[None]
_msg=["Click a cell to begin."]

def _row_time(fr,to): return T_FIRST_ROW if (fr==2 or to==2) else T_ROW_STEP
def _dlbl(dock): return "TOP" if list(dock)==[1,6] else "BOT"

def _plan_move(cl,cr,cc,tl,tr,tc):
    steps=[]; l,r,c=cl,cr,cc
    while r!=2:
        nr=r+(1 if 2>r else -1); steps.append(('row',nr,_row_time(r,nr),"AISLE")); r=nr
    if l!=tl:
        while c!=5:
            nc=c+(1 if 5>c else -1); steps.append(('col_step',nc,f"Col {nc}")); c=nc
        steps.append(('lift_enter',1,T_FIRST_ROW,"LIFT")); r=1
        while l!=tl:
            nl=l+(1 if tl>l else -1); steps.append(('lift',nl,T_LIFT_LVL,f"L{nl}")); l=nl
        steps.append(('lift_exit',2,T_FIRST_ROW,"AISLE")); r=2
    while c!=tc:
        nc=c+(1 if tc>c else -1); steps.append(('col_step',nc,f"Col {nc}")); c=nc
    while r!=tr:
        nr=r+(1 if tr>r else -1); steps.append(('row',nr,_row_time(r,nr),ROW_LBL.get(nr,str(nr)))); r=nr
    return steps

def _plan_store(lvl,r,c,pid,dock):
    dl,dr,dc=0,dock[0],dock[1]; steps=[]
    steps+=_plan_move(shuttle[0],shuttle[1],shuttle[2],dl,dr,dc)
    steps.append(('load',T_TRANSFER))
    steps+=_plan_move(dl,dr,dc,lvl,r,c)
    steps.append(('unload',lvl,r,c,pid))
    steps+=_plan_move(lvl,r,c,lvl,2,c)
    steps.append(('op_done',)); return steps

def _plan_retrieve(lvl,r,c,dock,pid):
    steps=[]; blockers=_get_blockers(lvl,r,c); cur=list(shuttle)
    for br in blockers:
        bpid=registry.get((lvl,br,c),'?'); tgt=_find_empty_slot(lvl,r,c)
        if tgt is None: continue
        el,er,ec=tgt
        steps+=_plan_move(cur[0],cur[1],cur[2],lvl,br,c)
        steps.append(('pickup',lvl,br,c,f"CLEARING {ROW_LBL.get(br,'?')}"))
        steps+=_plan_move(lvl,br,c,el,er,ec)
        steps.append(('unload',el,er,ec,bpid))
        steps+=_plan_move(el,er,ec,el,2,ec); cur=[el,2,ec]
    steps+=_plan_move(cur[0],cur[1],cur[2],lvl,r,c)
    steps.append(('pickup',lvl,r,c,f"PICKUP {pid}"))
    dl,dr,dc=0,dock[0],dock[1]
    steps+=_plan_move(lvl,r,c,dl,dr,dc)
    steps.append(('deliver',T_TRANSFER))
    steps+=_plan_move(dl,dr,dc,dl,2,dc)
    steps.append(('op_done',)); return steps

def _plan_restore(src_lvl,src_r,src_c,pid,dock):
    steps=[]; blockers=_get_blockers(src_lvl,src_r,src_c); cur=list(shuttle)
    for br in blockers:
        bpid=registry.get((src_lvl,br,src_c),'?'); tgt=_find_empty_slot(src_lvl,src_r,src_c)
        if tgt is None: continue
        el,er,ec=tgt
        steps+=_plan_move(cur[0],cur[1],cur[2],src_lvl,br,src_c)
        steps.append(('pickup',src_lvl,br,src_c,f"CLEARING {ROW_LBL.get(br,'?')}"))
        steps+=_plan_move(src_lvl,br,src_c,el,er,ec)
        steps.append(('unload',el,er,ec,bpid))
        steps+=_plan_move(el,er,ec,el,2,ec); cur=[el,2,ec]
    steps+=_plan_move(cur[0],cur[1],cur[2],src_lvl,src_r,src_c)
    steps.append(('pickup',src_lvl,src_r,src_c,f"RESTORE PICKUP {pid}"))
    dl,dr,dc=0,dock[0],dock[1]
    steps+=_plan_move(src_lvl,src_r,src_c,dl,dr,dc)
    steps.append(('deliver',T_TRANSFER))
    steps+=_plan_move(dl,dr,dc,dl,2,dc)
    steps.append(('op_done',)); return steps

def _get_blockers(lvl,r,c):
    bl=[]
    if r==0:
        if wh[lvl,1,c]==1: bl.append(1)
    elif r>2:
        for br in range(3,r):
            if wh[lvl,br,c]==1: bl.append(br)
    return bl

def _find_empty_slot(excl_lvl,excl_r,excl_c):
    reserved=set()
    for cmd in cmd_queue:
        if cmd[0]=='STORE': reserved.add((cmd[1].get('lvl'),cmd[1].get('r'),cmd[1].get('c')))
    for lvl in [excl_lvl]+[l for l in range(3) if l!=excl_lvl]:
        for r in range(7):
            for c in range(5):
                if r==2: continue
                if wh[lvl,r,c] in(-1,-2,1): continue
                if (lvl,r,c)==(excl_lvl,excl_r,excl_c): continue
                if (lvl,r,c) in reserved: continue
                if _store_valid_phys(lvl,r,c): return (lvl,r,c)
    return None

def _store_valid_phys(lvl,r,c):
    if r==1 and wh[lvl,0,c]!=1: return False
    if r==3 and any(wh[lvl,b,c]!=1 for b in[4,5,6]): return False
    if r==4 and any(wh[lvl,b,c]!=1 for b in[5,6]): return False
    if r==5 and wh[lvl,6,c]!=1: return False
    return True

def _store_valid_with_queue(lvl,r,c):
    def fp(tl,tr,tc):
        if wh[tl,tr,tc]==1: return True
        return any(cmd[0]=='STORE' and cmd[1].get('lvl')==tl and cmd[1].get('r')==tr and cmd[1].get('c')==tc for cmd in cmd_queue)
    if r==1 and not fp(lvl,0,c): return False,"Fill A1 (outer) before A0 (inner)."
    if r==3 and any(not fp(lvl,b,c) for b in[4,5,6]): return False,"Fill B3→B2→B1 before B0."
    if r==4 and any(not fp(lvl,b,c) for b in[5,6]): return False,"Fill B3→B2 before B1."
    if r==5 and not fp(lvl,6,c): return False,"Fill B3 before B2."
    return True,""

def _rec(l,r,c):
    if (l,r,c) not in store_ord: store_ord.append((l,r,c))
def _del(l,r,c):
    if (l,r,c) in store_ord: store_ord.remove((l,r,c))

def save_state():
    try:
        lines=["="*60,"WAREHOUSE STATE SNAPSHOT",f"Saved: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}","="*60,""]
        for lvl in range(3):
            lines.append(f"LEVEL {lvl}"); any_p=False
            for r in range(7):
                for c in range(5):
                    if wh[lvl,r,c]==1:
                        pid=registry.get((lvl,r,c),'?')
                        lines.append(f"  PalletID:{pid:<14}  Row:{ROW_LBL.get(r,'?'):<4}  Col:{c}  Level:{lvl}"); any_p=True
            if not any_p: lines.append("  (empty)")
            lines.append("")
        lines.append("MACHINE DATA")
        lines.append(json.dumps([{"l":l,"r":r,"c":c,"p":p} for (l,r,c),p in registry.items()]))
        lines.append("="*60)
        with open(STATE_FILE,'w',encoding='utf-8') as f: f.write('\n'.join(lines)+'\n')
        return True
    except: return False

def load_state():
    if not os.path.exists(STATE_FILE): return
    try:
        txt=open(STATE_FILE,'r',encoding='utf-8').read()
        idx=txt.find("MACHINE DATA")
        if idx==-1: return
        rest=txt[idx+len("MACHINE DATA"):]; bracket=rest.find('[')
        if bracket==-1: return
        end=rest.find('\n',bracket); data=json.loads(rest[bracket:end])
        for e in data:
            l,r,c,p=e['l'],e['r'],e['c'],e['p']
            wh[l,r,c]=1; registry[(l,r,c)]=p; store_ord.append((l,r,c))
    except: pass

def _log_add(action,args):
    cid=_cid_ctr[0]; _cid_ctr[0]+=1
    rk='src_r' if action=='RESTORE' else 'r'; ck='src_c' if action=='RESTORE' else 'c'; lk='src_lvl' if action=='RESTORE' else 'lvl'
    e={'cid':cid,'action':action,'pallet_id':args.get('pallet_id','?'),'lvl':args.get(lk,-1),
       'r':args.get(rk,-1),'c':args.get(ck,-1),'dock':args.get('dock',[1,6]),
       'status':'PENDING','elapsed':None,'ts':datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
    cmd_log.append(e); return cid

def _log_set(cid,st,elapsed=None):
    for e in cmd_log:
        if e['cid']==cid:
            e['status']=st
            if elapsed is not None: e['elapsed']=elapsed
            if st in('DONE','ERROR','ABORTED'): _write_log(e)
            return

def _write_log(e):
    try:
        row=ROW_LBL.get(e.get('r',-1),'?'); dk=_dlbl(e.get('dock',[1,6]))
        ela=e.get('elapsed'); ela_s=f"{ela:.2f}s" if isinstance(ela,float) else '-'
        with open(LOG_FILE,'a',encoding='utf-8') as f:
            f.write(f"[{e.get('ts','')}]  {e['action']:<10}  PalletID:{e.get('pallet_id','?'):<14}  Level:{e.get('lvl','?')}  Row:{row:<4}  Col:{e.get('c','?')}  Dock:{dk}  Status:{e['status']:<8}  Time:{ela_s}\n")
    except: pass

def _log_del(cid):
    for i,e in enumerate(cmd_log):
        if e['cid']==cid: cmd_log.pop(i); return

def do_tick():
    global loaded
    if not _plan: return ANIM_MS
    if _pause_req[0]:
        if shuttle[1]!=2:
            op_times['row']+=_row_time(shuttle[1],2); _cmd_accum[0]+=_row_time(shuttle[1],2)
            shuttle[1]=2; status_txt[0]="PAUSED"
        else:
            _paused[0]=True; _pause_req[0]=False; _executing[0]=False; _plan.clear(); status_txt[0]="PAUSED"
        return ANIM_MS
    step=_plan.pop(0); kind=step[0]
    if kind=='col_step':
        _,nc,msg=step; t=T2 if loaded else T1
        op_times['col']+=t; _cmd_accum[0]+=t; shuttle[2]=nc; status_txt[0]=msg; return ANIM_MS
    elif kind=='row':
        _,nr,t,msg=step; op_times['row']+=t; _cmd_accum[0]+=t; shuttle[1]=nr; status_txt[0]=msg; return ANIM_MS
    elif kind=='lift_enter':
        _,nr,t,msg=step; op_times['row']+=t; _cmd_accum[0]+=t; shuttle[1]=nr; _on_lift[0]=True; status_txt[0]="ENTERING LIFT"; return LIFT_MS
    elif kind=='lift':
        _,nl,t,msg=step; op_times['lift']+=t; _cmd_accum[0]+=t; shuttle[0]=nl; _on_lift[0]=True; status_txt[0]=msg
        return LIFT_MS if (bool(_plan) and _plan[0][0]=='lift') else ANIM_MS
    elif kind=='lift_exit':
        _,nr,t,msg=step; op_times['row']+=t; _cmd_accum[0]+=t; shuttle[1]=nr; _on_lift[0]=False; status_txt[0]="EXITING LIFT"; return ANIM_MS
    elif kind=='load':
        _,t=step; op_times['xfer']+=t; _cmd_accum[0]+=t; loaded=True; status_txt[0]="LOADED"; return ANIM_MS
    elif kind=='unload':
        _,lvl,r,c,pid=step; wh[lvl,r,c]=1; registry[(lvl,r,c)]=pid; _rec(lvl,r,c); loaded=False; status_txt[0]=f"PLACED {pid}"; return ANIM_MS
    elif kind=='pickup':
        _,lvl,r,c,msg=step; wh[lvl,r,c]=0; pid=registry.pop((lvl,r,c),'?'); _del(lvl,r,c); loaded=True; status_txt[0]=msg; return ANIM_MS
    elif kind=='deliver':
        _,t=step; op_times['xfer']+=t; _cmd_accum[0]+=t; loaded=False; status_txt[0]="DELIVERED"; return ANIM_MS
    elif kind=='op_done':
        if _cur_cid[0] is not None: _log_set(_cur_cid[0],'DONE',_cmd_accum[0])
        _load_next(); return ANIM_MS
    return ANIM_MS

def _load_next():
    if not cmd_queue:
        _executing[0]=False; status_txt[0]="ALL DONE"; return
    action,args=cmd_queue.popleft(); cid=args.get('_cid')
    _cur_cid[0]=cid; _cmd_accum[0]=0.0
    if cid is not None: _log_set(cid,'RUNNING')
    if action=='STORE': steps=_plan_store(args['lvl'],args['r'],args['c'],args['pallet_id'],args['dock'])
    elif action=='RETRIEVE': steps=_plan_retrieve(args['lvl'],args['r'],args['c'],args['dock'],args['pallet_id'])
    elif action=='RESTORE': steps=_plan_restore(args['src_lvl'],args['src_r'],args['src_c'],args['pallet_id'],args['dock'])
    else: steps=[('op_done',)]
    _plan.extend(steps)

def make_grid():
    lvl=view_lvl
    col_headers=[html.Th("")]+[html.Th(f"Col {c}",style={'color':'#BBBBBB','fontSize':'11px','textAlign':'center','padding':'4px','minWidth':'70px'}) for c in range(5)]+[html.Th("SERVICE",style={'color':'#BBBBBB','fontSize':'11px','textAlign':'center','padding':'4px','minWidth':'70px'}),html.Th("DOCK LANE",style={'color':'#BBBBBB','fontSize':'11px','textAlign':'center','padding':'4px','minWidth':'70px'})]
    rows=[]
    for r in range(7):
        cells=[html.Td(ROW_LBL.get(r,''),style={'color':'#BBBBBB','fontSize':'11px','padding':'4px 8px','whiteSpace':'nowrap'})]
        for c in range(7):
            v=wh[lvl,r,c]; pid=registry.get((lvl,r,c))
            if r==2:
                cells.append(html.Td("",style={'backgroundColor':'#888888','height':'55px','minWidth':'70px'}))
            elif c>=5:
                if lvl==0 and c==6 and r==1:
                    edge='3px solid #00E5FF' if sel_dock==[1,6] else '3px solid #555'
                    cells.append(html.Td(html.Button("TOP",id={'type':'dock-btn','row':r,'col':c},style={'width':'100%','height':'100%','backgroundColor':'#FFEB3B','border':edge,'fontWeight':'bold','fontSize':'12px','cursor':'pointer'}),style={'height':'55px','minWidth':'70px','padding':'2px'}))
                elif lvl==0 and c==6 and r==3:
                    edge='3px solid #00E5FF' if sel_dock==[3,6] else '3px solid #555'
                    cells.append(html.Td(html.Button("BOT",id={'type':'dock-btn','row':r,'col':c},style={'width':'100%','height':'100%','backgroundColor':'#FFEB3B','border':edge,'fontWeight':'bold','fontSize':'12px','cursor':'pointer'}),style={'height':'55px','minWidth':'70px','padding':'2px'}))
                elif c==5 and r==1:
                    is_lift=_on_lift[0] and shuttle[0]==lvl
                    bg='#FF9800' if is_lift and loaded else '#FFFF00' if is_lift else '#002F33'
                    cells.append(html.Td("LIFT" if not is_lift else "🚚" if loaded else "⬆",style={'backgroundColor':bg,'textAlign':'center','verticalAlign':'middle','color':'#00E5FF' if not is_lift else 'black','fontWeight':'bold','fontSize':'13px','height':'55px','minWidth':'70px'}))
                else:
                    cells.append(html.Td("",style={'backgroundColor':'#303030','height':'55px','minWidth':'70px'}))
            elif v==-1:
                cells.append(html.Td("WALL",style={'backgroundColor':'#2a2a2a','textAlign':'center','color':'#555','fontSize':'10px','height':'55px','minWidth':'70px'}))
            else:
                is_shuttle=(shuttle[0]==lvl and shuttle[1]==r and shuttle[2]==c and not _on_lift[0])
                if is_shuttle:
                    sc='#FF9800' if loaded else '#FFFF00'
                    cells.append(html.Td(html.Button("🚚" if loaded else "●",id={'type':'cell-btn','row':r,'col':c},style={'width':'100%','height':'100%','backgroundColor':sc,'border':'2px solid white','fontSize':'18px','cursor':'pointer'}),style={'height':'55px','minWidth':'70px','padding':'2px'}))
                elif pid:
                    is_rq=any(cmd[0]=='RESTORE' and cmd[1]['src_lvl']==lvl and cmd[1]['src_r']==r and cmd[1]['src_c']==c for cmd in cmd_queue)
                    bg='#FFA726' if is_rq else '#0D47A1'
                    cells.append(html.Td(html.Button(f"{ROW_LBL.get(r,'')}\n{pid}",id={'type':'cell-btn','row':r,'col':c},style={'width':'100%','height':'100%','backgroundColor':bg,'border':'1px solid #fff','color':'white','fontSize':'9px','cursor':'pointer','whiteSpace':'pre-line','fontWeight':'bold'}),style={'height':'55px','minWidth':'70px','padding':'2px'}))
                else:
                    cells.append(html.Td(html.Button(f"{ROW_LBL.get(r,'')}\nOPEN",id={'type':'cell-btn','row':r,'col':c},style={'width':'100%','height':'100%','backgroundColor':'#1a1a2e','border':'1px solid #333','color':'#444','fontSize':'9px','cursor':'pointer','whiteSpace':'pre-line'}),style={'height':'55px','minWidth':'70px','padding':'2px'}))
        rows.append(html.Tr(cells))
    return html.Div([
        html.Div(f"LEVEL {lvl}",style={'color':'#FFD700','fontWeight':'bold','fontSize':'16px','textAlign':'right','padding':'4px 8px','backgroundColor':'#1C1C00','border':'2px solid #FFD700','display':'inline-block','marginBottom':'6px'}),
        html.Table([html.Thead(html.Tr(col_headers)),html.Tbody(rows)],style={'borderCollapse':'collapse','width':'100%'})
    ])

def make_queue_table():
    pg=cur_page[0]; start=pg*PER_PAGE; rows=cmd_log[start:start+PER_PAGE]
    if not rows:
        return html.Div("No commands yet.",style={'color':'#2A4A5A','textAlign':'center','padding':'20px','fontStyle':'italic','fontSize':'12px'})
    header=html.Tr([html.Th(h,style={'color':'#00E5FF','fontSize':'10px','padding':'3px 5px','borderBottom':'1px solid #00BCD4','fontFamily':'monospace'}) for h in['#','ACTION','PALLET ID','DK','LV','ROW','COL','STATUS','TIME']])
    body_rows=[]
    for i,e in enumerate(rows):
        gi=start+i+1; act=e['action']; st=e['status']; ela=e.get('elapsed')
        tt=('-' if ela is None else f"{ela:.1f}s" if ela<60 else f"{int(ela)//60}m{int(ela)%60:02d}s")
        ac=ACT_CLR.get(act,'#FFF')
        if st=='DONE': ac='#2E6B30'
        if st=='ABORTED': ac='#8B5000'
        if st=='ERROR': ac='#8B0000'
        sc=QSCLR.get(st,'#FFF')
        bg='#1A2A00' if st=='RUNNING' else '#061206' if st=='DONE' else '#2A0000' if st=='ERROR' else '#2A1200' if st=='ABORTED' else '#0A1B2A' if i%2==0 else '#071018'
        cells=[str(gi),act,str(e.get('pallet_id','?'))[:10],_dlbl(e.get('dock',[1,6])),str(e.get('lvl','?')),ROW_LBL.get(e.get('r',-1),'?'),str(e.get('c','?')),st,tt]
        clrs=[None,ac,None,None,None,None,None,sc,'#FFA726' if ela is not None else '#546E7A']
        body_rows.append(html.Tr([html.Td(cells[j],style={'color':clrs[j] or '#D0EEF8','fontSize':'10px','padding':'3px 5px','fontFamily':'monospace','fontWeight':'bold' if j in(1,7) else 'normal'}) for j in range(9)],style={'backgroundColor':bg}))
    return html.Table([html.Thead(header),html.Tbody(body_rows)],style={'width':'100%','borderCollapse':'collapse'})

load_state()

app=Dash(__name__,title="Warehouse Control",external_stylesheets=[dbc.themes.SLATE],suppress_callback_exceptions=True)
server=app.server

app.layout=html.Div([
    dcc.Interval(id='tick',interval=ANIM_MS,n_intervals=0),
    dcc.Store(id='store-cell',data=None),
    dcc.Store(id='input-mode',data='none'),

    html.Div("WAREHOUSE SHUTTLE CONTROL SYSTEM",style={'textAlign':'center','color':'#FFD700','fontSize':'20px','fontWeight':'bold','padding':'12px','backgroundColor':'#1C1C00','borderBottom':'2px solid #FFD700','letterSpacing':'2px'}),

    html.Div([
        html.Div([
            html.Div(id='status-bar',style={'backgroundColor':'#040D18','border':'2px solid #0288D1','color':'#00E5FF','padding':'8px 16px','borderRadius':'6px','fontWeight':'bold','fontSize':'13px','textAlign':'center','marginBottom':'8px'}),
            html.Div([
                html.Button(f'LEVEL {i}',id=f'lvl{i}',n_clicks=0,style={'flex':'1','padding':'10px','fontSize':'12px','fontWeight':'bold','color':'white','backgroundColor':['#1A237E','#4A148C','#004D40'][i],'border':'none','borderRadius':'4px','cursor':'pointer','margin':'2px'})
                for i in range(3)
            ],style={'display':'flex','marginBottom':'8px'}),
            html.Div(id='grid-area',style={'overflowX':'auto'}),
            html.Div("Click empty cell → STORE  |  Click filled cell → RETRIEVE  |  Click TOP/BOT dock to select",style={'color':'#546E7A','fontSize':'11px','textAlign':'center','marginTop':'6px'}),
        ],style={'flex':'1','minWidth':'0','paddingRight':'12px'}),

        html.Div([
            html.Div("CONTROL PANEL",style={'color':'#FFD700','fontWeight':'bold','fontSize':'13px','textAlign':'center','padding':'8px','backgroundColor':'#1C1C00','borderRadius':'4px','marginBottom':'8px'}),
            html.Div(id='time-display',style={'backgroundColor':'#1A0000','border':'1px solid #CC0000','color':'#FFD700','padding':'8px','borderRadius':'4px','fontFamily':'monospace','fontSize':'13px','fontWeight':'bold','textAlign':'center','marginBottom':'8px'}),
            html.Button('▶  EXECUTE QUEUE',id='btn-exec',n_clicks=0,style={'width':'100%','padding':'12px','backgroundColor':'#1B5E20','color':'#AAFFAA','fontWeight':'bold','fontSize':'14px','border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}),
            html.Button('⏸  PAUSE',id='btn-pause',n_clicks=0,style={'width':'100%','padding':'10px','backgroundColor':'#4A3800','color':'#FFD700','fontWeight':'bold','fontSize':'13px','border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}),
            html.Button('RESTORE MODE: OFF',id='btn-restore',n_clicks=0,style={'width':'100%','padding':'10px','backgroundColor':'#1A1A2E','color':'#FFA726','fontSize':'12px','border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}),
            html.Button('✕  DELETE COMMAND',id='btn-delete',n_clicks=0,style={'width':'100%','padding':'10px','backgroundColor':'#3A0000','color':'#FF6B6B','fontSize':'12px','border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}),
            html.Button('💾  EXIT & SAVE STATE',id='btn-exit',n_clicks=0,style={'width':'100%','padding':'10px','backgroundColor':'#B71C1C','color':'white','fontSize':'12px','border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'12px'}),
            html.Div(id='msg-box',style={'backgroundColor':'#0A1A0A','border':'1px solid #2E7D32','color':'#AAFFAA','padding':'8px','borderRadius':'4px','fontSize':'11px','minHeight':'40px','marginBottom':'8px','fontFamily':'monospace','whiteSpace':'pre-wrap'}),
            html.Div(id='input-area',style={'marginBottom':'8px'}),
            html.Div([
                html.Div("COMMAND LOG",style={'color':'#FFD700','fontWeight':'bold','fontSize':'12px','textAlign':'center','padding':'6px','backgroundColor':'#050D16','borderBottom':'1px solid #00BCD4'}),
                html.Div(id='queue-table',style={'backgroundColor':'#050D16','maxHeight':'280px','overflowY':'auto','border':'2px solid #00BCD4','borderRadius':'0 0 4px 4px'}),
                html.Div([
                    html.Button('◀',id='pg-prev',n_clicks=0,style={'padding':'4px 10px','backgroundColor':'#0A0A14','color':'#00E5FF','border':'1px solid #00BCD4','borderRadius':'3px','cursor':'pointer','margin':'2px'}),
                    *[html.Button(str(i+1),id=f'pg-{i}',n_clicks=0,style={'padding':'4px 8px','backgroundColor':'#0D1A2A','color':'#00BCD4','border':'1px solid #00BCD4','borderRadius':'3px','cursor':'pointer','margin':'2px'}) for i in range(NUM_PAGES)],
                    html.Button('▶',id='pg-next',n_clicks=0,style={'padding':'4px 10px','backgroundColor':'#0A0A14','color':'#00E5FF','border':'1px solid #00BCD4','borderRadius':'3px','cursor':'pointer','margin':'2px'}),
                ],style={'textAlign':'center','padding':'4px','backgroundColor':'#050D16'}),
            ],style={'border':'2px solid #00BCD4','borderRadius':'4px','overflow':'hidden'}),
        ],style={'width':'340px','flexShrink':'0'}),
    ],style={'display':'flex','padding':'12px','gap':'8px','flex':'1','overflow':'hidden'}),
],style={'margin':'0','padding':'0','backgroundColor':'#0E0E0E','fontFamily':'Arial, sans-serif','minHeight':'100vh'})


@app.callback(
    Output('grid-area','children'),
    Output('status-bar','children'),
    Output('time-display','children'),
    Output('queue-table','children'),
    Output('msg-box','children'),
    Output('input-area','children'),
    Output('input-mode','data'),
    Output('store-cell','data'),
    Output('btn-pause','children'),
    Output('btn-pause','style'),
    Output('btn-restore','children'),
    Output('btn-restore','style'),
    Input('tick','n_intervals'),
    Input('lvl0','n_clicks'), Input('lvl1','n_clicks'), Input('lvl2','n_clicks'),
    Input('btn-exec','n_clicks'), Input('btn-pause','n_clicks'),
    Input('btn-restore','n_clicks'), Input('btn-delete','n_clicks'),
    Input('btn-exit','n_clicks'),
    Input('pg-prev','n_clicks'), Input('pg-next','n_clicks'),
    *[Input(f'pg-{i}','n_clicks') for i in range(NUM_PAGES)],
    Input({'type':'cell-btn','row':0,'col':0},'n_clicks'),
    Input({'type':'dock-btn','row':0,'col':0},'n_clicks'),
    State('input-mode','data'),
    State('store-cell','data'),
    prevent_initial_call=False
)
def main_cb(n_tick,nl0,nl1,nl2,n_exec,n_pause,n_restore,n_delete,n_exit,
            n_prev,n_next,*rest):
    global view_lvl,loaded
    page_clicks=rest[:NUM_PAGES]
    cell_click=rest[NUM_PAGES]
    dock_click=rest[NUM_PAGES+1]
    input_mode=rest[NUM_PAGES+2]
    store_cell=rest[NUM_PAGES+3]

    ctx=callback_context
    trig=ctx.triggered[0]['prop_id'] if ctx.triggered else ''
    msg=no_update; inp=no_update; new_mode=no_update; new_cell=no_update

    with _lock:
        if 'tick' in trig and _executing[0]:
            now=time.time()
            if now-_last_tick[0]>=_tick_ms[0]/1000.0:
                _last_tick[0]=now; _tick_ms[0]=do_tick()

        elif 'lvl0' in trig and not(_executing[0] and not _paused[0]): view_lvl=0
        elif 'lvl1' in trig and not(_executing[0] and not _paused[0]): view_lvl=1
        elif 'lvl2' in trig and not(_executing[0] and not _paused[0]): view_lvl=2

        elif 'btn-exec' in trig:
            if not _executing[0] and cmd_queue:
                _executing[0]=True; _paused[0]=False; _pause_req[0]=False
                _plan.clear(); _last_tick[0]=time.time(); _load_next()
                msg="Execution started."
            elif not cmd_queue: msg="Queue is empty."

        elif 'btn-pause' in trig:
            if _executing[0] and not _paused[0]:
                _pause_req[0]=True; msg="Pausing..."
            elif _paused[0]:
                _paused[0]=False; _pause_req[0]=False; _executing[0]=True
                _last_tick[0]=time.time(); _load_next(); msg="Resumed."
            else: msg="Nothing is executing."

        elif 'btn-restore' in trig:
            restore_md[0]=not restore_md[0]
            msg="RESTORE MODE ON." if restore_md[0] else "RESTORE MODE OFF."

        elif 'btn-delete' in trig:
            new_mode='delete'
            inp=html.Div([
                dcc.Input(id='pid-input',placeholder='Pallet ID to delete...',debounce=False,style={'width':'65%','padding':'6px','backgroundColor':'#1a1a2e','color':'white','border':'1px solid #FF6B6B','borderRadius':'3px','marginRight':'4px'}),
                html.Button('DELETE',id='confirm-btn',n_clicks=0,style={'padding':'6px 10px','backgroundColor':'#6B0000','color':'white','border':'none','borderRadius':'3px','cursor':'pointer'})
            ]); msg="Enter Pallet ID to delete."

        elif 'btn-exit' in trig:
            save_state(); msg=f"State saved to Desktop."

        elif 'pg-prev' in trig:
            if cur_page[0]>0: cur_page[0]-=1
        elif 'pg-next' in trig:
            total=len(cmd_log)
            if cur_page[0]<NUM_PAGES-1 and (cur_page[0]+1)*PER_PAGE<total: cur_page[0]+=1
        elif 'pg-' in trig and 'prev' not in trig and 'next' not in trig:
            try: cur_page[0]=int(trig.split('"')[1].split('-')[1])
            except: pass

        elif 'cell-btn' in trig and cell_click:
            try:
                prop=ctx.triggered[0]['prop_id']
                import re
                r_match=re.search(r'"row":(\d+)',prop); c_match=re.search(r'"col":(\d+)',prop)
                if r_match and c_match:
                    r=int(r_match.group(1)); c=int(c_match.group(1))
                    if not(_executing[0] and not _paused[0]):
                        if len(cmd_queue)>=MAX_QUEUE: msg=f"Queue full ({MAX_QUEUE})."
                        elif restore_md[0]:
                            if wh[view_lvl,r,c]==1:
                                pid=registry.get((view_lvl,r,c),'?')
                                _a={'src_lvl':view_lvl,'src_r':r,'src_c':c,'lvl':0,'r':sel_dock[0],'c':6,'pallet_id':pid,'dock':list(sel_dock)}
                                cid=_log_add('RESTORE',_a); _a['_cid']=cid
                                cmd_queue.append(('RESTORE',_a))
                                cur_page[0]=(len(cmd_log)-1)//PER_PAGE
                                msg=f"RESTORE queued: {pid}"
                            else: msg="Click an OCCUPIED cell."
                        elif wh[view_lvl,r,c]==0:
                            if any(cmd[0]=='STORE' and cmd[1].get('lvl')==view_lvl and cmd[1].get('r')==r and cmd[1].get('c')==c for cmd in cmd_queue):
                                msg="Slot already has pending STORE."
                            else:
                                valid,vmsg=_store_valid_with_queue(view_lvl,r,c)
                                if not valid: msg=f"Store order: {vmsg}"
                                else:
                                    new_mode='store'; new_cell={'lvl':view_lvl,'r':r,'c':c}
                                    inp=html.Div([
                                        html.Div(f"Storing → L{view_lvl} {ROW_LBL.get(r,'?')} Col{c}",style={'color':'#66BB6A','fontSize':'11px','marginBottom':'4px'}),
                                        dcc.Input(id='pid-input',placeholder='Enter unique Pallet ID...',debounce=False,style={'width':'65%','padding':'6px','backgroundColor':'#1a1a2e','color':'white','border':'1px solid #66BB6A','borderRadius':'3px','marginRight':'4px'}),
                                        html.Button('STORE',id='confirm-btn',n_clicks=0,style={'padding':'6px 10px','backgroundColor':'#1B5E20','color':'white','border':'none','borderRadius':'3px','cursor':'pointer'})
                                    ]); msg=f"Enter Pallet ID."
                        else:
                            pid=registry.get((view_lvl,r,c),'?')
                            if any(cmd[0]=='RETRIEVE' and cmd[1].get('lvl')==view_lvl and cmd[1].get('r')==r and cmd[1].get('c')==c for cmd in cmd_queue):
                                msg=f"RETRIEVE for {pid} already queued."
                            else:
                                _a={'lvl':view_lvl,'r':r,'c':c,'pallet_id':pid,'dock':list(sel_dock)}
                                cid=_log_add('RETRIEVE',_a); _a['_cid']=cid
                                cmd_queue.append(('RETRIEVE',_a))
                                cur_page[0]=(len(cmd_log)-1)//PER_PAGE
                                msg=f"RETRIEVE queued: {pid}"
            except Exception as ex: msg=f"Error: {ex}"

        elif 'dock-btn' in trig and dock_click:
            try:
                prop=ctx.triggered[0]['prop_id']
                import re
                r_match=re.search(r'"row":(\d+)',prop)
                if r_match:
                    r=int(r_match.group(1))
                    if r==1: sel_dock[:]=[1,6]; msg="Selected TOP dock."
                    elif r==3: sel_dock[:]=[3,6]; msg="Selected BOT dock."
            except: pass

        tt=total_t(); mm,ss=divmod(int(tt),60)
        time_str=f"TOTAL TIME :  {mm:02d}m  {ss:02d}s  ({tt:.2f}s)"
        pend=sum(1 for e in cmd_log if e['status']=='PENDING')
        done=sum(1 for e in cmd_log if e['status']=='DONE')
        status_str=f"STATUS: {status_txt[0]}   |   LEVEL {view_lvl}   |   QUEUE: {len(cmd_queue)}/{MAX_QUEUE}   |   pending:{pend}  done:{done}"
        pause_lbl='▶  RESUME' if _paused[0] else '⏸  PAUSE'
        pause_style={'width':'100%','padding':'10px','backgroundColor':'#003366' if _paused[0] else '#4A3800','color':'#FFD700','fontWeight':'bold','fontSize':'13px','border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}
        rst_lbl='RESTORE MODE: ON' if restore_md[0] else 'RESTORE MODE: OFF'
        rst_style={'width':'100%','padding':'10px','backgroundColor':'#3E1F00' if restore_md[0] else '#1A1A2E','color':'#FFA726','fontSize':'12px','border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}

        grid=make_grid(); qtable=make_queue_table()

    return (grid,status_str,time_str,qtable,
            msg,inp,new_mode,new_cell,
            pause_lbl,pause_style,rst_lbl,rst_style)


@app.callback(
    Output('msg-box','children',allow_duplicate=True),
    Output('input-area','children',allow_duplicate=True),
    Output('input-mode','data',allow_duplicate=True),
    Output('store-cell','data',allow_duplicate=True),
    Output('queue-table','children',allow_duplicate=True),
    Input('confirm-btn','n_clicks'),
    State('pid-input','value'),
    State('input-mode','data'),
    State('store-cell','data'),
    prevent_initial_call=True
)
def confirm_cb(n,uid,mode,cell):
    if not n or not uid: raise PreventUpdate
    uid=uid.strip()
    with _lock:
        if mode=='store':
            if not uid: return "Pallet ID cannot be empty.",no_update,mode,cell,no_update
            if ' ' in uid: return f"No spaces allowed in Pallet ID.",no_update,mode,cell,no_update
            if uid in registry.values() or any(cmd[1].get('pallet_id')==uid for cmd in cmd_queue):
                return f"'{uid}' already in use.",no_update,mode,cell,no_update
            lvl=cell['lvl']; r=cell['r']; c=cell['c']
            _a={'lvl':lvl,'r':r,'c':c,'pallet_id':uid,'dock':list(sel_dock)}
            cid=_log_add('STORE',_a); _a['_cid']=cid
            cmd_queue.append(('STORE',_a))
            cur_page[0]=(len(cmd_log)-1)//PER_PAGE
            return f"STORE queued: {uid} → L{lvl} {ROW_LBL.get(r,'?')} Col{c}",[],'none',None,make_queue_table()
        elif mode=='delete':
            found=None
            for cmd in list(cmd_queue):
                if cmd[1].get('pallet_id')==uid: found=cmd; break
            if found is None: return f"No pending command for '{uid}'.",no_update,mode,cell,no_update
            cmd_queue.remove(found)
            cid=found[1].get('_cid')
            if cid is not None: _log_del(cid)
            return f"Deleted: '{uid}'.",[],'none',None,make_queue_table()
    raise PreventUpdate


if __name__=='__main__':
    port=int(os.environ.get('PORT',8050))
    app.run(debug=False,host='0.0.0.0',port=port)
