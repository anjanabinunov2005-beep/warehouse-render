import json, os, threading
from collections import deque
from datetime import datetime

import numpy as np
import plotly.graph_objects as go
from dash import Dash, Input, Output, State, callback_context, dcc, html, no_update
from dash.exceptions import PreventUpdate

T1          = 3.0
T2          = 5.0
S1          = 0.8
S2          = 1.1
T_FIRST_ROW = 1.250 / S1
T_ROW_STEP  = 1.050 / S1
T_LIFT_LVL  = 3.000 / S2
T_TRANSFER  = T1
ANIM_MS     = 1200
LIFT_MS     = 1800
MAX_QUEUE   = 50
PER_PAGE    = 10
NUM_PAGES   = 5

DESKTOP    = os.path.join(os.path.expanduser("~"), "Desktop")
LOG_FILE   = os.path.join(DESKTOP, "warehouse_log.txt")
STATE_FILE = os.path.join(DESKTOP, "warehouse_state.txt")

ROW_LBL = {0:"A1",1:"A0",2:"AISLE",3:"B0",4:"B1",5:"B2",6:"B3"}
COL_LBL = {0:"Col 0",1:"Col 1",2:"Col 2",3:"Col 3",4:"Col 4",5:"SERVICE",6:"DOCK LANE"}
ACT_CLR = {'STORE':'#66BB6A','RETRIEVE':'#42A5F5','RESTORE':'#FFA726'}
QSCLR   = {'PENDING':'#78909C','RUNNING':'#FFD700','DONE':'#66BB6A','ERROR':'#EF5350','ABORTED':'#FF8A65'}

_lock = threading.Lock()

wh        = np.zeros((3,7,7), dtype=float)
registry  = {}
store_ord = []
for _lv in range(3):
    wh[_lv,2,:]   = -2
    wh[_lv,3:7,2] = -1

shuttle    = [0,2,6]
loaded     = False
view_lvl   = 0
sel_dock   = [1,6]
restore_md = [False]
op_times   = dict(col=0.0,row=0.0,lift=0.0,xfer=0.0)
def total_t(): return sum(op_times.values())

cmd_queue  = deque()
cmd_log    = []
_cid_ctr   = [0]
status_txt = ["READY"]
cur_page   = [0]

_plan      = []
_executing = [False]
_paused    = [False]
_pause_req = [False]
_on_lift   = [False]
_cur_cid   = [None]
_cmd_accum = [0.0]
_tick_ms   = [ANIM_MS]

def _row_time(fr,to):
    return T_FIRST_ROW if (fr==2 or to==2) else T_ROW_STEP

def _dlbl(dock):
    return "TOP" if list(dock)==[1,6] else "BOT"

def _plan_move(cl,cr,cc,tl,tr,tc):
    steps=[]; l,r,c=cl,cr,cc
    while r!=2:
        nr=r+(1 if 2>r else -1)
        steps.append(('row',nr,_row_time(r,nr),"AISLE")); r=nr
    if l!=tl:
        while c!=5:
            nc=c+(1 if 5>c else -1)
            steps.append(('col_step',nc,f"Col {nc}")); c=nc
        steps.append(('lift_enter',1,T_FIRST_ROW,"LIFT")); r=1
        while l!=tl:
            nl=l+(1 if tl>l else -1)
            steps.append(('lift',nl,T_LIFT_LVL,f"L{nl}")); l=nl
        steps.append(('lift_exit',2,T_FIRST_ROW,"AISLE")); r=2
    while c!=tc:
        nc=c+(1 if tc>c else -1)
        steps.append(('col_step',nc,f"Col {nc}")); c=nc
    while r!=tr:
        nr=r+(1 if tr>r else -1)
        steps.append(('row',nr,_row_time(r,nr),ROW_LBL.get(nr,str(nr)))); r=nr
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
        if cmd[0]=='STORE':
            reserved.add((cmd[1].get('lvl'),cmd[1].get('r'),cmd[1].get('c')))
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
    if r==1 and wh[lvl,0,c]!=1:                        return False
    if r==3 and any(wh[lvl,b,c]!=1 for b in[4,5,6]):  return False
    if r==4 and any(wh[lvl,b,c]!=1 for b in[5,6]):    return False
    if r==5 and wh[lvl,6,c]!=1:                        return False
    return True

def _store_valid_with_queue(lvl,r,c):
    def fp(tl,tr,tc):
        if wh[tl,tr,tc]==1: return True
        return any(cmd[0]=='STORE' and cmd[1].get('lvl')==tl
                   and cmd[1].get('r')==tr and cmd[1].get('c')==tc
                   for cmd in cmd_queue)
    if r==1 and not fp(lvl,0,c): return False,"Fill A1 (outer) before A0 (inner)."
    if r==3 and any(not fp(lvl,b,c) for b in[4,5,6]): return False,"Fill B3→B2→B1 before B0."
    if r==4 and any(not fp(lvl,b,c) for b in[5,6]):   return False,"Fill B3→B2 before B1."
    if r==5 and not fp(lvl,6,c): return False,"Fill B3 before B2."
    return True,""

def _rec(l,r,c):
    if (l,r,c) not in store_ord: store_ord.append((l,r,c))

def _del(l,r,c):
    if (l,r,c) in store_ord: store_ord.remove((l,r,c))

def save_state():
    try:
        lines=["="*60,"WAREHOUSE STATE SNAPSHOT",
               f"Saved: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}","="*60,""]
        for lvl in range(3):
            lines.append(f"LEVEL {lvl}")
            any_p=False
            for r in range(7):
                for c in range(5):
                    if wh[lvl,r,c]==1:
                        pid=registry.get((lvl,r,c),'?')
                        lines.append(f"  PalletID:{pid:<14}  Row:{ROW_LBL.get(r,'?'):<4}  Col:{c}  Level:{lvl}")
                        any_p=True
            if not any_p: lines.append("  (empty)")
            lines.append("")
        lines.append("MACHINE DATA")
        entries=[{"l":l,"r":r,"c":c,"p":p} for (l,r,c),p in registry.items()]
        lines.append(json.dumps(entries))
        lines.append("="*60)
        with open(STATE_FILE,'w',encoding='utf-8') as f:
            f.write('\n'.join(lines)+'\n')
        return True
    except: return False

def load_state():
    if not os.path.exists(STATE_FILE): return
    try:
        txt=open(STATE_FILE,'r',encoding='utf-8').read()
        idx=txt.find("MACHINE DATA")
        if idx==-1: return
        rest=txt[idx+len("MACHINE DATA"):]
        bracket=rest.find('[')
        if bracket==-1: return
        end=rest.find('\n',bracket)
        data=json.loads(rest[bracket:end])
        for e in data:
            l,r,c,p=e['l'],e['r'],e['c'],e['p']
            wh[l,r,c]=1; registry[(l,r,c)]=p; store_ord.append((l,r,c))
    except: pass

def _log_add(action,args):
    cid=_cid_ctr[0]; _cid_ctr[0]+=1
    rk='src_r' if action=='RESTORE' else 'r'
    ck='src_c' if action=='RESTORE' else 'c'
    lk='src_lvl' if action=='RESTORE' else 'lvl'
    e={'cid':cid,'action':action,'pallet_id':args.get('pallet_id','?'),
       'lvl':args.get(lk,-1),'r':args.get(rk,-1),'c':args.get(ck,-1),
       'dock':args.get('dock',[1,6]),'status':'PENDING',
       'elapsed':None,'ts':datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
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
            f.write(f"[{e.get('ts','')}]  {e['action']:<10}  "
                    f"PalletID:{e.get('pallet_id','?'):<14}  "
                    f"Level:{e.get('lvl','?')}  Row:{row:<4}  Col:{e.get('c','?')}  "
                    f"Dock:{dk}  Status:{e['status']:<8}  Time:{ela_s}\n")
    except: pass

def _log_del(cid):
    for i,e in enumerate(cmd_log):
        if e['cid']==cid: cmd_log.pop(i); return

def do_tick():
    global loaded
    with _lock:
        if not _plan: return ANIM_MS

        if _pause_req[0]:
            if shuttle[1]!=2:
                t=_row_time(shuttle[1],2)
                op_times['row']+=t; _cmd_accum[0]+=t
                shuttle[1]=2; status_txt[0]="PAUSED"
            else:
                _paused[0]=True; _pause_req[0]=False
                _executing[0]=False; _plan.clear()
                status_txt[0]="PAUSED"
            return ANIM_MS

        step=_plan.pop(0); kind=step[0]

        if kind=='col_step':
            _,nc,msg=step; t=T2 if loaded else T1
            op_times['col']+=t; _cmd_accum[0]+=t
            shuttle[2]=nc; status_txt[0]=msg
            return ANIM_MS

        elif kind=='row':
            _,nr,t,msg=step
            op_times['row']+=t; _cmd_accum[0]+=t
            shuttle[1]=nr; status_txt[0]=msg
            return ANIM_MS

        elif kind=='lift_enter':
            _,nr,t,msg=step
            op_times['row']+=t; _cmd_accum[0]+=t
            shuttle[1]=nr; _on_lift[0]=True; status_txt[0]="ENTERING LIFT"
            return LIFT_MS

        elif kind=='lift':
            _,nl,t,msg=step
            op_times['lift']+=t; _cmd_accum[0]+=t
            shuttle[0]=nl; _on_lift[0]=True; status_txt[0]=msg
            next_lift=bool(_plan) and _plan[0][0]=='lift'
            return LIFT_MS if next_lift else ANIM_MS

        elif kind=='lift_exit':
            _,nr,t,msg=step
            op_times['row']+=t; _cmd_accum[0]+=t
            shuttle[1]=nr; _on_lift[0]=False; status_txt[0]="EXITING LIFT"
            return ANIM_MS

        elif kind=='load':
            _,t=step; op_times['xfer']+=t; _cmd_accum[0]+=t
            loaded=True; status_txt[0]="LOADED"
            return ANIM_MS

        elif kind=='unload':
            _,lvl,r,c,pid=step
            wh[lvl,r,c]=1; registry[(lvl,r,c)]=pid; _rec(lvl,r,c)
            loaded=False; status_txt[0]=f"PLACED {pid}"
            return ANIM_MS

        elif kind=='pickup':
            _,lvl,r,c,msg=step
            wh[lvl,r,c]=0; pid=registry.pop((lvl,r,c),'?'); _del(lvl,r,c)
            loaded=True; status_txt[0]=msg
            return ANIM_MS

        elif kind=='deliver':
            _,t=step; op_times['xfer']+=t; _cmd_accum[0]+=t
            loaded=False; status_txt[0]="DELIVERED"
            return ANIM_MS

        elif kind=='op_done':
            elapsed=_cmd_accum[0]
            if _cur_cid[0] is not None: _log_set(_cur_cid[0],'DONE',elapsed)
            _load_next()
            return ANIM_MS

        return ANIM_MS

def _load_next():
    if not cmd_queue:
        _executing[0]=False; status_txt[0]="ALL DONE"; return
    action,args=cmd_queue.popleft()
    cid=args.get('_cid'); _cur_cid[0]=cid; _cmd_accum[0]=0.0
    if cid is not None: _log_set(cid,'RUNNING')
    if action=='STORE':
        steps=_plan_store(args['lvl'],args['r'],args['c'],args['pallet_id'],args['dock'])
    elif action=='RETRIEVE':
        steps=_plan_retrieve(args['lvl'],args['r'],args['c'],args['dock'],args['pallet_id'])
    elif action=='RESTORE':
        steps=_plan_restore(args['src_lvl'],args['src_r'],args['src_c'],args['pallet_id'],args['dock'])
    else:
        steps=[('op_done',)]
    _plan.extend(steps)

def make_grid_fig():
    lvl=view_lvl
    fig=go.Figure()
    cell_w=80; cell_h=70
    col_labels=[COL_LBL[i] for i in range(7)]
    row_labels=[ROW_LBL[i] for i in range(7)]

    for r in range(7):
        for c in range(7):
            x0=c*cell_w; x1=x0+cell_w; y0=(6-r)*cell_h; y1=y0+cell_h
            v=wh[lvl,r,c]
            if r==2:
                fill='#888888'
            elif c>=5:
                fill='#303030'
            elif v==-1:
                fill='#2a2a2a'
            elif v==1:
                fill='#0D47A1'
            else:
                fill='#1a1a2e'

            if c==5 and r==1:
                fill='#002F33'

            fig.add_shape(type='rect',x0=x0,y0=y0,x1=x1,y1=y1,
                          fillcolor=fill,line=dict(color='#333',width=1))

            if r==2:
                fig.add_annotation(x=(x0+x1)/2,y=(y0+y1)/2,text="",
                                   showarrow=False,font=dict(color='#ccc',size=9))
            elif c==5 and r==1:
                fig.add_annotation(x=(x0+x1)/2,y=(y0+y1)/2,text="LIFT",
                                   showarrow=False,font=dict(color='#00E5FF',size=11,family='Arial Black'))
            elif c>=5:
                if lvl==0 and c==6 and r==1:
                    edge='#00E5FF' if sel_dock==[1,6] else '#555'
                    fig.add_shape(type='rect',x0=x0+3,y0=y0+3,x1=x1-3,y1=y1-3,
                                  fillcolor='#FFEB3B',line=dict(color=edge,width=3))
                    fig.add_annotation(x=(x0+x1)/2,y=(y0+y1)/2,text="TOP",
                                       showarrow=False,font=dict(color='black',size=10,family='Arial Black'))
                elif lvl==0 and c==6 and r==3:
                    edge='#00E5FF' if sel_dock==[3,6] else '#555'
                    fig.add_shape(type='rect',x0=x0+3,y0=y0+3,x1=x1-3,y1=y1-3,
                                  fillcolor='#FFEB3B',line=dict(color=edge,width=3))
                    fig.add_annotation(x=(x0+x1)/2,y=(y0+y1)/2,text="BOT",
                                       showarrow=False,font=dict(color='black',size=10,family='Arial Black'))
            elif c<5:
                pid=registry.get((lvl,r,c))
                if v==-1:
                    fig.add_annotation(x=(x0+x1)/2,y=(y0+y1)/2,text="WALL",
                                       showarrow=False,font=dict(color='#555',size=8))
                elif pid:
                    is_rq=any(cmd[0]=='RESTORE' and cmd[1]['src_lvl']==lvl
                              and cmd[1]['src_r']==r and cmd[1]['src_c']==c
                              for cmd in cmd_queue)
                    bg='#FFA726' if is_rq else '#0D47A1'
                    fig.add_shape(type='rect',x0=x0+2,y0=y0+2,x1=x1-2,y1=y1-2,
                                  fillcolor=bg,line=dict(color='#fff',width=1))
                    fig.add_annotation(x=(x0+x1)/2,y=(y0+y1)/2,
                                       text=f"<b>{ROW_LBL.get(r,'')}</b><br>{pid}",
                                       showarrow=False,font=dict(color='white',size=8))
                else:
                    fig.add_annotation(x=(x0+x1)/2,y=(y0+y1)/2,
                                       text=f"<span style='color:#444;font-size:8px'>{ROW_LBL.get(r,'')}<br>OPEN</span>",
                                       showarrow=False,font=dict(color='#444',size=8))

    if shuttle[0]==lvl:
        draw_r=1 if _on_lift[0] else shuttle[1]
        sx=shuttle[2]*cell_w+cell_w/2; sy=(6-draw_r)*cell_h+cell_h/2
        sc='#FF9800' if loaded else '#FFFF00'
        fig.add_shape(type='rect',x0=sx-28,y0=sy-22,x1=sx+28,y1=sy+22,
                      fillcolor=sc,line=dict(color='white',width=3))
        fig.add_annotation(x=sx,y=sy,text="🚚" if loaded else "🟡",
                           showarrow=False,font=dict(size=16))

    fig.add_annotation(x=6*cell_w+cell_w/2,y=7*cell_h+18,
                       text=f"<b>LEVEL {lvl}</b>",showarrow=False,
                       font=dict(color='#FFD700',size=16),
                       bgcolor='#1C1C00',bordercolor='#FFD700',borderwidth=2)

    for i,lbl in enumerate(col_labels):
        fig.add_annotation(x=i*cell_w+cell_w/2,y=-22,text=lbl,
                           showarrow=False,font=dict(color='#BBBBBB',size=9))
    for i,lbl in enumerate(row_labels):
        fig.add_annotation(x=-48,y=(6-i)*cell_h+cell_h/2,text=lbl,
                           showarrow=False,font=dict(color='#BBBBBB',size=9),xanchor='right')

    fig.update_layout(
        width=620,height=580,
        margin=dict(l=70,r=10,t=40,b=40),
        paper_bgcolor='#141414',plot_bgcolor='#141414',
        xaxis=dict(visible=False,range=[-55,7*cell_w+10]),
        yaxis=dict(visible=False,range=[-35,7*cell_h+35]),
        showlegend=False
    )
    return fig

def make_queue_table():
    pg=cur_page[0]; start=pg*PER_PAGE
    rows=cmd_log[start:start+PER_PAGE]
    if not rows:
        return html.Div("No commands yet.",
                        style={'color':'#2A4A5A','textAlign':'center','padding':'20px','fontStyle':'italic'})
    header=html.Tr([html.Th(h,style={'color':'#00E5FF','fontSize':'11px','padding':'4px 6px',
                                      'borderBottom':'1px solid #00BCD4','fontFamily':'monospace'})
                    for h in['#','ACTION','PALLET ID','DK','LV','ROW','COL','STATUS','TIME']])
    body_rows=[]
    for i,e in enumerate(rows):
        gi=start+i+1; act=e['action']; st=e['status']
        ela=e.get('elapsed')
        tt=('-' if ela is None else f"{ela:.1f}s" if ela<60
            else f"{int(ela)//60}m{int(ela)%60:02d}s")
        ac=ACT_CLR.get(act,'#FFF')
        if st=='DONE':    ac='#2E6B30'
        if st=='ABORTED': ac='#8B5000'
        if st=='ERROR':   ac='#8B0000'
        sc=QSCLR.get(st,'#FFF')
        bg='#1A2A00' if st=='RUNNING' else '#061206' if st=='DONE' \
           else '#2A0000' if st=='ERROR' else '#2A1200' if st=='ABORTED' \
           else '#0A1B2A' if i%2==0 else '#071018'
        cells=[str(gi),act,str(e.get('pallet_id','?'))[:10],
               _dlbl(e.get('dock',[1,6])),str(e.get('lvl','?')),
               ROW_LBL.get(e.get('r',-1),'?'),str(e.get('c','?')),st,tt]
        clrs=[None,ac,None,None,None,None,None,sc,'#FFA726' if ela is not None else '#546E7A']
        body_rows.append(html.Tr(
            [html.Td(cells[j],style={'color':clrs[j] or '#D0EEF8','fontSize':'11px',
                                      'padding':'4px 6px','fontFamily':'monospace',
                                      'fontWeight':'bold' if j in(1,7) else 'normal'})
             for j in range(9)],
            style={'backgroundColor':bg}))
    return html.Table([html.Thead(header),html.Tbody(body_rows)],
                      style={'width':'100%','borderCollapse':'collapse'})

load_state()

app=Dash(__name__,title="Warehouse Control")
app.layout=html.Div([
    dcc.Interval(id='anim-tick',interval=ANIM_MS,n_intervals=0,disabled=True),
    dcc.Store(id='input-mode',data='none'),
    dcc.Store(id='pending-cell',data=None),

    html.Div([
        html.Div("WAREHOUSE SHUTTLE CONTROL SYSTEM",style={
            'textAlign':'center','color':'#FFD700','fontSize':'20px',
            'fontWeight':'bold','padding':'14px','backgroundColor':'#1C1C00',
            'borderBottom':'2px solid #FFD700','letterSpacing':'2px'}),

        html.Div([
            html.Div([
                html.Div(id='status-bar',style={
                    'backgroundColor':'#040D18','border':'2px solid #0288D1',
                    'color':'#00E5FF','padding':'8px 16px','borderRadius':'6px',
                    'fontWeight':'bold','fontSize':'13px','textAlign':'center','marginBottom':'10px'}),

                html.Div([
                    html.Button(f'LEVEL {i}',id=f'lvl-btn-{i}',n_clicks=0,
                        style={'flex':'1','padding':'10px','fontSize':'12px','fontWeight':'bold',
                               'color':'white','backgroundColor':['#1A237E','#4A148C','#004D40'][i],
                               'border':'none','borderRadius':'4px','cursor':'pointer','margin':'2px'})
                    for i in range(3)
                ],style={'display':'flex','marginBottom':'8px'}),

                dcc.Graph(id='warehouse-grid',figure=make_grid_fig(),
                          config={'displayModeBar':False},
                          style={'cursor':'crosshair'},
                          clear_on_unhover=True),

                html.Div([
                    html.Span("Click empty cell → STORE  |  Click filled cell → RETRIEVE  |  "
                              "Click TOP/BOT dock to select",
                              style={'color':'#546E7A','fontSize':'11px'})
                ],style={'textAlign':'center','marginTop':'4px'}),

            ],style={'flex':'1','minWidth':'0','paddingRight':'12px'}),

            html.Div([
                html.Div("CONTROL PANEL",style={
                    'color':'#FFD700','fontWeight':'bold','fontSize':'13px',
                    'textAlign':'center','padding':'8px',
                    'backgroundColor':'#1C1C00','borderRadius':'4px','marginBottom':'8px'}),

                html.Div(id='total-time-dash',style={
                    'backgroundColor':'#1A0000','border':'1px solid #CC0000',
                    'color':'#FFD700','padding':'8px','borderRadius':'4px',
                    'fontFamily':'monospace','fontSize':'13px','fontWeight':'bold',
                    'textAlign':'center','marginBottom':'8px'}),

                html.Div([
                    html.Button('▶  EXECUTE QUEUE',id='btn-exec',n_clicks=0,style={
                        'width':'100%','padding':'12px','backgroundColor':'#1B5E20',
                        'color':'#AAFFAA','fontWeight':'bold','fontSize':'14px',
                        'border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}),
                    html.Button('⏸  PAUSE',id='btn-pause',n_clicks=0,style={
                        'width':'100%','padding':'10px','backgroundColor':'#4A3800',
                        'color':'#FFD700','fontWeight':'bold','fontSize':'13px',
                        'border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}),
                    html.Button('RESTORE MODE: OFF',id='btn-restore',n_clicks=0,style={
                        'width':'100%','padding':'10px','backgroundColor':'#1A1A2E',
                        'color':'#FFA726','fontSize':'12px',
                        'border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}),
                    html.Button('✕  DELETE COMMAND',id='btn-delete',n_clicks=0,style={
                        'width':'100%','padding':'10px','backgroundColor':'#3A0000',
                        'color':'#FF6B6B','fontSize':'12px',
                        'border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}),
                    html.Button('💾  EXIT & SAVE STATE',id='btn-exit',n_clicks=0,style={
                        'width':'100%','padding':'10px','backgroundColor':'#B71C1C',
                        'color':'white','fontSize':'12px',
                        'border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'12px'}),
                ]),

                html.Div(id='msg-box',style={
                    'backgroundColor':'#0A1A0A','border':'1px solid #2E7D32',
                    'color':'#AAFFAA','padding':'8px','borderRadius':'4px',
                    'fontSize':'11px','minHeight':'40px','marginBottom':'8px',
                    'fontFamily':'monospace','whiteSpace':'pre-wrap'}),

                html.Div(id='input-area',children=[],style={'marginBottom':'8px'}),

                html.Div([
                    html.Div("COMMAND LOG",style={
                        'color':'#FFD700','fontWeight':'bold','fontSize':'12px',
                        'textAlign':'center','padding':'6px',
                        'backgroundColor':'#050D16','borderBottom':'1px solid #00BCD4'}),
                    html.Div(id='queue-table',style={
                        'backgroundColor':'#050D16','maxHeight':'260px',
                        'overflowY':'auto','border':'2px solid #00BCD4','borderRadius':'4px'}),
                    html.Div([
                        html.Button('◀',id='page-prev',n_clicks=0,style={
                            'padding':'4px 10px','backgroundColor':'#0A0A14','color':'#00E5FF',
                            'border':'1px solid #00BCD4','borderRadius':'3px','cursor':'pointer','margin':'2px'}),
                        *[html.Button(str(i+1),id=f'page-{i}',n_clicks=0,style={
                            'padding':'4px 8px','backgroundColor':'#0D1A2A','color':'#00BCD4',
                            'border':'1px solid #00BCD4','borderRadius':'3px','cursor':'pointer','margin':'2px'})
                          for i in range(NUM_PAGES)],
                        html.Button('▶',id='page-next',n_clicks=0,style={
                            'padding':'4px 10px','backgroundColor':'#0A0A14','color':'#00E5FF',
                            'border':'1px solid #00BCD4','borderRadius':'3px','cursor':'pointer','margin':'2px'}),
                    ],style={'textAlign':'center','padding':'4px','backgroundColor':'#050D16'}),
                ],style={'border':'2px solid #00BCD4','borderRadius':'4px','overflow':'hidden'}),

            ],style={'width':'340px','flexShrink':'0'}),
        ],style={'display':'flex','padding':'12px','gap':'8px','flex':'1','overflow':'hidden'}),
    ],style={'display':'flex','flexDirection':'column','height':'100vh',
             'backgroundColor':'#0E0E0E','fontFamily':'Arial, sans-serif'}),
],style={'margin':'0','padding':'0'})


@app.callback(
    Output('warehouse-grid','figure'),
    Output('status-bar','children'),
    Output('total-time-dash','children'),
    Output('queue-table','children'),
    Output('anim-tick','disabled'),
    Output('anim-tick','interval'),
    Output('btn-pause','children'),
    Output('btn-pause','style'),
    Output('btn-restore','children'),
    Output('btn-restore','style'),
    Output('msg-box','children'),
    Output('input-area','children'),
    Output('input-mode','data'),
    Output('pending-cell','data'),
    Input('anim-tick','n_intervals'),
    Input('warehouse-grid','clickData'),
    Input('btn-exec','n_clicks'),
    Input('btn-pause','n_clicks'),
    Input('btn-restore','n_clicks'),
    Input('btn-delete','n_clicks'),
    Input('btn-exit','n_clicks'),
    Input('lvl-btn-0','n_clicks'),
    Input('lvl-btn-1','n_clicks'),
    Input('lvl-btn-2','n_clicks'),
    Input('page-prev','n_clicks'),
    Input('page-next','n_clicks'),
    *[Input(f'page-{i}','n_clicks') for i in range(NUM_PAGES)],
    State('input-mode','data'),
    State('pending-cell','data'),
    prevent_initial_call=False
)
def master_cb(n_tick,click_data,n_exec,n_pause,n_restore,n_delete,n_exit,
              n_l0,n_l1,n_l2,n_prev,n_next,*page_and_states):
    global view_lvl,loaded

    page_clicks = page_and_states[:NUM_PAGES]
    input_mode  = page_and_states[NUM_PAGES]
    pending_cell= page_and_states[NUM_PAGES+1]

    ctx   = callback_context
    trig  = ctx.triggered[0]['prop_id'].split('.')[0] if ctx.triggered else ''
    msg   = no_update
    inp_area = no_update
    new_mode = no_update
    new_cell = no_update

    with _lock:
        if trig=='anim-tick' and _executing[0]:
            new_interval=do_tick()
            _tick_ms[0]=new_interval

        elif trig=='lvl-btn-0' and not (_executing[0] and not _paused[0]):
            view_lvl=0
        elif trig=='lvl-btn-1' and not (_executing[0] and not _paused[0]):
            view_lvl=1
        elif trig=='lvl-btn-2' and not (_executing[0] and not _paused[0]):
            view_lvl=2

        elif trig=='btn-exec':
            if not _executing[0] and cmd_queue:
                _executing[0]=True; _paused[0]=False; _pause_req[0]=False
                _plan.clear(); _load_next()
                msg="Execution started."
            elif not cmd_queue:
                msg="Queue is empty — add commands first."

        elif trig=='btn-pause':
            if _executing[0] and not _paused[0]:
                _pause_req[0]=True; msg="Pausing — shuttle returning to aisle..."
            elif _paused[0]:
                _paused[0]=False; _pause_req[0]=False; _executing[0]=True
                _load_next(); msg="Resumed."
            else:
                msg="Nothing is executing."

        elif trig=='btn-restore':
            restore_md[0]=not restore_md[0]
            msg="RESTORE MODE ON — click a stored pallet." if restore_md[0] else "RESTORE MODE OFF."

        elif trig=='btn-delete':
            new_mode='delete'
            inp_area=html.Div([
                dcc.Input(id='pallet-input',placeholder='Enter Pallet ID to delete...',
                          debounce=True,style={'width':'70%','padding':'6px','backgroundColor':'#1a1a2e',
                                               'color':'white','border':'1px solid #FF6B6B',
                                               'borderRadius':'3px','marginRight':'6px'}),
                html.Button('CONFIRM DELETE',id='confirm-input',n_clicks=0,
                            style={'padding':'6px 12px','backgroundColor':'#6B0000','color':'white',
                                   'border':'none','borderRadius':'3px','cursor':'pointer'})
            ])
            msg="Enter the Pallet ID to delete from queue."

        elif trig=='btn-exit':
            save_state()
            msg=f"State saved to Desktop.\nFile: warehouse_state.txt"

        elif trig=='page-prev':
            if cur_page[0]>0: cur_page[0]-=1
        elif trig=='page-next':
            total=len(cmd_log)
            if cur_page[0]<NUM_PAGES-1 and (cur_page[0]+1)*PER_PAGE<total:
                cur_page[0]+=1
        elif trig.startswith('page-') and trig!='page-prev' and trig!='page-next':
            try:
                pg=int(trig.split('-')[1]); cur_page[0]=pg
            except: pass

        elif trig=='warehouse-grid' and click_data and not (_executing[0] and not _paused[0]):
            pt=click_data['points'][0]
            px=pt.get('x',0); py=pt.get('y',0)
            cell_w=80; cell_h=70
            c=int(px//cell_w); r=6-int(py//cell_h)
            if 0<=c<=6 and 0<=r<=6:
                if view_lvl==0 and c==6:
                    if r==1:   sel_dock[:]=[1,6]; msg="Selected TOP dock."
                    elif r==3: sel_dock[:]=[3,6]; msg="Selected BOT dock."
                elif c<=4 and r!=2 and wh[view_lvl,r,c] not in(-1,-2):
                    if len(cmd_queue)>=MAX_QUEUE:
                        msg=f"Queue full ({MAX_QUEUE} max). Execute first."
                    elif restore_md[0]:
                        if wh[view_lvl,r,c]==1:
                            pid=registry.get((view_lvl,r,c),'?')
                            _a={'src_lvl':view_lvl,'src_r':r,'src_c':c,
                                'lvl':0,'r':sel_dock[0],'c':6,'pallet_id':pid,'dock':list(sel_dock)}
                            cid=_log_add('RESTORE',_a); _a['_cid']=cid
                            cmd_queue.append(('RESTORE',_a))
                            cur_page[0]=(len(cmd_log)-1)//PER_PAGE
                            msg=f"RESTORE queued: {pid}"
                        else:
                            msg="Click an OCCUPIED cell in restore mode."
                    elif wh[view_lvl,r,c]==0:
                        if any(cmd[0]=='STORE' and cmd[1].get('lvl')==view_lvl
                               and cmd[1].get('r')==r and cmd[1].get('c')==c
                               for cmd in cmd_queue):
                            msg="Slot already has a pending STORE."
                        else:
                            valid,vmsg=_store_valid_with_queue(view_lvl,r,c)
                            if not valid:
                                msg=f"Store order error: {vmsg}"
                            else:
                                new_mode='store'
                                new_cell={'lvl':view_lvl,'r':r,'c':c}
                                inp_area=html.Div([
                                    html.Div(f"Storing → Level {view_lvl} | Row {ROW_LBL.get(r,'?')} | Col {c}",
                                             style={'color':'#66BB6A','fontSize':'11px','marginBottom':'4px'}),
                                    dcc.Input(id='pallet-input',placeholder='Enter unique Pallet ID...',
                                              debounce=True,
                                              style={'width':'70%','padding':'6px','backgroundColor':'#1a1a2e',
                                                     'color':'white','border':'1px solid #66BB6A',
                                                     'borderRadius':'3px','marginRight':'6px'}),
                                    html.Button('CONFIRM STORE',id='confirm-input',n_clicks=0,
                                                style={'padding':'6px 12px','backgroundColor':'#1B5E20',
                                                       'color':'white','border':'none',
                                                       'borderRadius':'3px','cursor':'pointer'})
                                ])
                                msg=f"Enter Pallet ID for Level {view_lvl}, Row {ROW_LBL.get(r,'?')}, Col {c}."
                    else:
                        pid=registry.get((view_lvl,r,c),'?')
                        if any(cmd[0]=='RETRIEVE' and cmd[1].get('lvl')==view_lvl
                               and cmd[1].get('r')==r and cmd[1].get('c')==c
                               for cmd in cmd_queue):
                            msg=f"RETRIEVE for {pid} already queued."
                        else:
                            _a={'lvl':view_lvl,'r':r,'c':c,'pallet_id':pid,'dock':list(sel_dock)}
                            cid=_log_add('RETRIEVE',_a); _a['_cid']=cid
                            cmd_queue.append(('RETRIEVE',_a))
                            cur_page[0]=(len(cmd_log)-1)//PER_PAGE
                            msg=f"RETRIEVE queued: {pid}"

        tt=total_t(); mm,ss=divmod(int(tt),60)
        time_str=f"TOTAL TIME :  {mm:02d}m  {ss:02d}s  ({tt:.2f}s)"

        pend=sum(1 for e in cmd_log if e['status']=='PENDING')
        done=sum(1 for e in cmd_log if e['status']=='DONE')
        status_str=(f"STATUS: {status_txt[0]}   |   LEVEL {view_lvl}   |   "
                    f"QUEUE: {len(cmd_queue)}/{MAX_QUEUE}   |   "
                    f"pending:{pend}  done:{done}")

        pause_lbl='▶  RESUME' if _paused[0] else '⏸  PAUSE'
        pause_style={'width':'100%','padding':'10px',
                     'backgroundColor':'#003366' if _paused[0] else '#4A3800',
                     'color':'#FFD700','fontWeight':'bold','fontSize':'13px',
                     'border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}

        rst_lbl='RESTORE MODE: ON' if restore_md[0] else 'RESTORE MODE: OFF'
        rst_style={'width':'100%','padding':'10px',
                   'backgroundColor':'#3E1F00' if restore_md[0] else '#1A1A2E',
                   'color':'#FFA726','fontSize':'12px',
                   'border':'none','borderRadius':'4px','cursor':'pointer','marginBottom':'6px'}

        tick_disabled = not _executing[0]
        tick_interval = _tick_ms[0]

        fig=make_grid_fig()
        qtable=make_queue_table()

    return (fig, status_str, time_str, qtable,
            tick_disabled, tick_interval,
            pause_lbl, pause_style,
            rst_lbl, rst_style,
            msg, inp_area, new_mode, new_cell)


@app.callback(
    Output('msg-box','children',allow_duplicate=True),
    Output('input-area','children',allow_duplicate=True),
    Output('input-mode','data',allow_duplicate=True),
    Output('pending-cell','data',allow_duplicate=True),
    Output('queue-table','children',allow_duplicate=True),
    Input('confirm-input','n_clicks'),
    State('pallet-input','value'),
    State('input-mode','data'),
    State('pending-cell','data'),
    prevent_initial_call=True
)
def handle_confirm(n,uid,mode,cell):
    if not n or not uid: raise PreventUpdate
    uid=uid.strip()
    with _lock:
        if mode=='store':
            if not uid:
                return "Pallet ID cannot be empty.",[],mode,cell,no_update
            if ' ' in uid:
                return f"'{uid}' has spaces — use PLT001 style.",[],mode,cell,no_update
            if uid in registry.values() or any(cmd[1].get('pallet_id')==uid for cmd in cmd_queue):
                return f"'{uid}' already in use.",[],mode,cell,no_update
            lvl=cell['lvl']; r=cell['r']; c=cell['c']
            _a={'lvl':lvl,'r':r,'c':c,'pallet_id':uid,'dock':list(sel_dock)}
            cid=_log_add('STORE',_a); _a['_cid']=cid
            cmd_queue.append(('STORE',_a))
            cur_page[0]=(len(cmd_log)-1)//PER_PAGE
            return f"STORE queued: {uid}  →  L{lvl} {ROW_LBL.get(r,'?')} Col{c}",[],'none',None,make_queue_table()

        elif mode=='delete':
            found=None
            for cmd in list(cmd_queue):
                if cmd[1].get('pallet_id')==uid: found=cmd; break
            if found is None:
                return f"No pending command for '{uid}'.",[],mode,cell,no_update
            cmd_queue.remove(found)
            cid=found[1].get('_cid')
            if cid is not None: _log_del(cid)
            return f"Deleted command for '{uid}'.",[],'none',None,make_queue_table()

    raise PreventUpdate


if __name__=='__main__':
    port=int(os.environ.get('PORT',8050))
    app.run(debug=False,host='0.0.0.0',port=port)
