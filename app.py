import json, os, threading
from collections import deque
from datetime import datetime
from flask import Flask, jsonify, request

# ── Timing ─────────────────────────────────────────────────────────────────────
T_LIFT     = 3.0
T_TRAVEL   = 5.0
T_ACTION   = 3.0
T_LIFT_LVL = 3.0 / 1.1
STEP_MS    = 350
LIFT_MS    = 800
MAX_QUEUE  = 50

DESKTOP    = os.path.join(os.path.expanduser("~"), "Desktop")
STATE_FILE = os.path.join(DESKTOP, "warehouse_state.txt")
LOG_FILE   = os.path.join(DESKTOP, "warehouse_log.txt")

ROW_LBL = {0:"A1",1:"A0",2:"AISLE",3:"B0",4:"B1",5:"B2",6:"B3"}

# ── Warehouse state ─────────────────────────────────────────────────────────────
import numpy as np
wh         = np.zeros((3,7,7), dtype=float)
registry   = {}
store_ord  = []
for _lv in range(3):
    wh[_lv,2,:]   = -2
    wh[_lv,3:7,2] = -1

shuttle    = [0, 2, 6]
loaded     = False
sel_dock   = [1, 6]
restore_md = False
total_time = 0.0
status_txt = "READY"
cmd_queue  = deque()
cmd_log    = []
cid_ctr    = [0]
_lock      = threading.Lock()

def _dlbl(d): return "TOP" if list(d)==[1,6] else "BOT"

# ── Plan builder ────────────────────────────────────────────────────────────────
def plan_move(cl, cr, cc, tl, tr, tc):
    frames = []; l,r,c = cl,cr,cc
    while r != 2:
        nr = r + (1 if 2>r else -1)
        frames.append({'type':'move','l':l,'r':nr,'c':c,'msg':'→ AISLE','t':T_TRAVEL,'ms':STEP_MS})
        r = nr
    if l != tl:
        while c != 5:
            nc = c + (1 if 5>c else -1)
            frames.append({'type':'move','l':l,'r':r,'c':nc,'msg':f'→ Col {nc}','t':T_TRAVEL,'ms':STEP_MS})
            c = nc
        frames.append({'type':'move','l':l,'r':1,'c':c,'msg':'ENTERING LIFT','t':T_TRAVEL,'ms':LIFT_MS,'on_lift':True})
        r = 1
        while l != tl:
            nl = l + (1 if tl>l else -1)
            frames.append({'type':'move','l':nl,'r':r,'c':c,'msg':f'LIFT L{l}→L{nl}','t':T_LIFT_LVL,'ms':LIFT_MS,'on_lift':True})
            l = nl
        frames.append({'type':'move','l':l,'r':2,'c':c,'msg':'EXITING LIFT','t':T_TRAVEL,'ms':STEP_MS,'on_lift':False})
        r = 2
    while c != tc:
        nc = c + (1 if tc>c else -1)
        frames.append({'type':'move','l':l,'r':r,'c':nc,'msg':f'→ Col {nc}','t':T_TRAVEL,'ms':STEP_MS})
        c = nc
    while r != tr:
        nr = r + (1 if tr>r else -1)
        frames.append({'type':'move','l':l,'r':nr,'c':c,'msg':f'→ {ROW_LBL.get(nr,str(nr))}','t':T_TRAVEL,'ms':STEP_MS})
        r = nr
    return frames

def build_store(lvl, r, c, pid, dock):
    dl,dr,dc = 0,dock[0],dock[1]; f=[]
    f += plan_move(shuttle[0],shuttle[1],shuttle[2],dl,dr,dc)
    f.append({'type':'status','msg':'LIFTING AT DOCK','t':T_LIFT,'ms':STEP_MS})
    f.append({'type':'load','msg':'LOADING','t':T_ACTION,'ms':STEP_MS})
    f += plan_move(dl,dr,dc,lvl,r,c)
    f.append({'type':'status','msg':'LIFTING AT SLOT','t':T_LIFT,'ms':STEP_MS})
    f.append({'type':'place','lvl':lvl,'r':r,'c':c,'pid':pid,'t':T_ACTION,'ms':STEP_MS})
    f += plan_move(lvl,r,c,lvl,2,c)
    f.append({'type':'done'})
    return f

def build_retrieve(lvl, r, c, dock, pid):
    f=[]; blockers=get_blockers(lvl,r,c); cur=list(shuttle)
    for br in blockers:
        bpid = registry.get((lvl,br,c),'?')
        tgt  = find_empty(lvl,r,c)
        if tgt is None: continue
        el,er,ec = tgt
        f += plan_move(cur[0],cur[1],cur[2],lvl,br,c)
        f.append({'type':'status','msg':f'LIFTING BLOCKER {ROW_LBL.get(br,"?")}','t':T_LIFT,'ms':STEP_MS})
        f.append({'type':'pick','lvl':lvl,'r':br,'c':c,'msg':f'CLEARING','t':T_ACTION,'ms':STEP_MS})
        f += plan_move(lvl,br,c,el,er,ec)
        f.append({'type':'status','msg':'PLACING BLOCKER','t':T_LIFT,'ms':STEP_MS})
        f.append({'type':'place','lvl':el,'r':er,'c':ec,'pid':bpid,'t':T_ACTION,'ms':STEP_MS})
        f += plan_move(el,er,ec,el,2,ec); cur=[el,2,ec]
    f += plan_move(cur[0],cur[1],cur[2],lvl,r,c)
    f.append({'type':'status','msg':f'LIFTING {pid}','t':T_LIFT,'ms':STEP_MS})
    f.append({'type':'pick','lvl':lvl,'r':r,'c':c,'msg':f'PICKUP {pid}','t':T_ACTION,'ms':STEP_MS})
    dl,dr,dc = 0,dock[0],dock[1]
    f += plan_move(lvl,r,c,dl,dr,dc)
    f.append({'type':'status','msg':'PLACING AT DOCK','t':T_LIFT,'ms':STEP_MS})
    f.append({'type':'deliver','t':T_ACTION,'ms':STEP_MS})
    f += plan_move(dl,dr,dc,dl,2,dc)
    f.append({'type':'done'})
    return f

def build_restore(src_lvl, src_r, src_c, pid, dock):
    f=[]; blockers=get_blockers(src_lvl,src_r,src_c); cur=list(shuttle)
    for br in blockers:
        bpid = registry.get((src_lvl,br,src_c),'?')
        tgt  = find_empty(src_lvl,src_r,src_c)
        if tgt is None: continue
        el,er,ec = tgt
        f += plan_move(cur[0],cur[1],cur[2],src_lvl,br,src_c)
        f.append({'type':'status','msg':'LIFTING BLOCKER','t':T_LIFT,'ms':STEP_MS})
        f.append({'type':'pick','lvl':src_lvl,'r':br,'c':src_c,'msg':'CLEARING','t':T_ACTION,'ms':STEP_MS})
        f += plan_move(src_lvl,br,src_c,el,er,ec)
        f.append({'type':'status','msg':'PLACING BLOCKER','t':T_LIFT,'ms':STEP_MS})
        f.append({'type':'place','lvl':el,'r':er,'c':ec,'pid':bpid,'t':T_ACTION,'ms':STEP_MS})
        f += plan_move(el,er,ec,el,2,ec); cur=[el,2,ec]
    f += plan_move(cur[0],cur[1],cur[2],src_lvl,src_r,src_c)
    f.append({'type':'status','msg':f'LIFTING {pid}','t':T_LIFT,'ms':STEP_MS})
    f.append({'type':'pick','lvl':src_lvl,'r':src_r,'c':src_c,'msg':f'RESTORE {pid}','t':T_ACTION,'ms':STEP_MS})
    dl,dr,dc = 0,dock[0],dock[1]
    f += plan_move(src_lvl,src_r,src_c,dl,dr,dc)
    f.append({'type':'status','msg':'PLACING AT DOCK','t':T_LIFT,'ms':STEP_MS})
    f.append({'type':'deliver','t':T_ACTION,'ms':STEP_MS})
    f += plan_move(dl,dr,dc,dl,2,dc)
    f.append({'type':'done'})
    return f

def get_blockers(lvl,r,c):
    bl=[]
    if r==0:
        if wh[lvl,1,c]==1: bl.append(1)
    elif r>2:
        for br in range(3,r):
            if wh[lvl,br,c]==1: bl.append(br)
    return bl

def find_empty(excl_lvl,excl_r,excl_c):
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
                if store_valid_phys(lvl,r,c): return (lvl,r,c)
    return None

def store_valid_phys(lvl,r,c):
    if r==1 and wh[lvl,0,c]!=1: return False
    if r==3 and any(wh[lvl,b,c]!=1 for b in[4,5,6]): return False
    if r==4 and any(wh[lvl,b,c]!=1 for b in[5,6]): return False
    if r==5 and wh[lvl,6,c]!=1: return False
    return True

def store_valid_queue(lvl,r,c):
    def fp(tl,tr,tc):
        if wh[tl,tr,tc]==1: return True
        return any(cmd[0]=='STORE' and cmd[1].get('lvl')==tl
                   and cmd[1].get('r')==tr and cmd[1].get('c')==tc for cmd in cmd_queue)
    if r==1 and not fp(lvl,0,c): return False,"Fill A1 before A0."
    if r==3 and any(not fp(lvl,b,c) for b in[4,5,6]): return False,"Fill B3→B2→B1 before B0."
    if r==4 and any(not fp(lvl,b,c) for b in[5,6]): return False,"Fill B3→B2 before B1."
    if r==5 and not fp(lvl,6,c): return False,"Fill B3 before B2."
    return True,""

def rec(l,r,c):
    if (l,r,c) not in store_ord: store_ord.append((l,r,c))
def rem(l,r,c):
    if (l,r,c) in store_ord: store_ord.remove((l,r,c))

def apply_plan(frames):
    global loaded, total_time
    t=0.0
    for f in frames:
        t += f.get('t',0)
        ft = f['type']
        if ft=='move':
            shuttle[0]=f['l']; shuttle[1]=f['r']; shuttle[2]=f['c']
        elif ft=='load':
            loaded=True
        elif ft=='place':
            wh[f['lvl'],f['r'],f['c']]=1
            registry[(f['lvl'],f['r'],f['c'])]=f['pid']
            rec(f['lvl'],f['r'],f['c']); loaded=False
        elif ft=='pick':
            wh[f['lvl'],f['r'],f['c']]=0
            registry.pop((f['lvl'],f['r'],f['c']),None)
            rem(f['lvl'],f['r'],f['c']); loaded=True
        elif ft=='deliver':
            loaded=False
    total_time += t
    shuttle[1]=2   # rest at aisle

def log_add(action,args):
    cid=cid_ctr[0]; cid_ctr[0]+=1
    rk='src_r' if action=='RESTORE' else 'r'
    lk='src_lvl' if action=='RESTORE' else 'lvl'
    ck='src_c' if action=='RESTORE' else 'c'
    e={'cid':cid,'action':action,'pallet_id':args.get('pallet_id','?'),
       'lvl':args.get(lk,-1),'r':args.get(rk,-1),'c':args.get(ck,-1),
       'dock':args.get('dock',[1,6]),'status':'PENDING',
       'elapsed':None,'ts':datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
    cmd_log.append(e); return cid

def log_set(cid,st,elapsed=None):
    for e in cmd_log:
        if e['cid']==cid:
            e['status']=st
            if elapsed is not None: e['elapsed']=elapsed
            if st in('DONE','ERROR'):
                try:
                    row=ROW_LBL.get(e.get('r',-1),'?')
                    dk=_dlbl(e.get('dock',[1,6]))
                    ela=e.get('elapsed')
                    ela_s=f"{ela:.2f}s" if isinstance(ela,float) else '-'
                    with open(LOG_FILE,'a',encoding='utf-8') as f:
                        f.write(f"[{e.get('ts','')}]  {e['action']:<10}  "
                                f"PalletID:{e.get('pallet_id','?'):<14}  "
                                f"Level:{e.get('lvl','?')}  Row:{row:<4}  "
                                f"Col:{e.get('c','?')}  Dock:{dk}  "
                                f"Status:{e['status']:<8}  Time:{ela_s}\n")
                except: pass
            return

def save_state():
    try:
        lines=["="*60,"WAREHOUSE STATE SNAPSHOT",
               f"Saved: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}","="*60,""]
        for lvl in range(3):
            lines.append(f"LEVEL {lvl}"); any_p=False
            for r in range(7):
                for c in range(5):
                    if wh[lvl,r,c]==1:
                        pid=registry.get((lvl,r,c),'?')
                        lines.append(f"  PalletID:{pid:<14}  Row:{ROW_LBL.get(r,'?'):<4}  Col:{c}  Level:{lvl}")
                        any_p=True
            if not any_p: lines.append("  (empty)")
            lines.append("")
        lines.append("MACHINE DATA")
        lines.append(json.dumps([{"l":l,"r":r,"c":c,"p":p} for (l,r,c),p in registry.items()]))
        lines.append("="*60)
        with open(STATE_FILE,'w',encoding='utf-8') as f: f.write('\n'.join(lines)+'\n')
    except: pass

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

def wh_state_json(lvl):
    cells=[]
    for r in range(7):
        for c in range(7):
            v=wh[lvl,r,c]; pid=registry.get((lvl,r,c))
            cells.append({'r':r,'c':c,'v':float(v),'pid':pid or ''})
    return cells

# ── Flask app ───────────────────────────────────────────────────────────────────
app = Flask(__name__, static_folder='static')

@app.route('/')
def index():
    return HTML_PAGE

HTML_PAGE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Warehouse Control</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{background:#0E0E0E;color:white;font-family:Arial,sans-serif;min-height:100vh}
#header{background:#1C1C00;border-bottom:2px solid #FFD700;text-align:center;padding:12px;color:#FFD700;font-size:20px;font-weight:bold;letter-spacing:2px}
#main{display:flex;padding:10px;gap:10px;flex-wrap:wrap}
#left{flex:1;min-width:300px}
#right{width:320px;flex-shrink:0}
#status-bar{background:#040D18;border:2px solid #0288D1;color:#00E5FF;padding:8px 16px;border-radius:6px;font-weight:bold;font-size:12px;text-align:center;margin-bottom:8px;font-family:monospace}
#level-btns{display:flex;margin-bottom:8px;gap:4px}
.lvl-btn{flex:1;padding:10px;font-size:12px;font-weight:bold;color:white;border:none;border-radius:4px;cursor:pointer}
#canvas-wrap{position:relative;display:inline-block}
canvas{background:#141414;border-radius:6px;display:block}
#grid-overlay{position:absolute;top:0;left:0;width:100%;height:100%}
#hint{color:#546E7A;font-size:11px;text-align:center;margin-top:6px}
#panel-title{color:#FFD700;font-weight:bold;font-size:13px;text-align:center;padding:8px;background:#1C1C00;border-radius:4px;margin-bottom:8px}
#time-box{background:#1A0000;border:1px solid #CC0000;color:#FFD700;padding:8px;border-radius:4px;font-family:monospace;font-size:12px;font-weight:bold;text-align:center;margin-bottom:8px}
.ctrl-btn{width:100%;padding:10px;font-weight:bold;font-size:13px;border:none;border-radius:4px;cursor:pointer;margin-bottom:6px;display:block}
#msg-box{background:#0A1A0A;border:1px solid #2E7D32;color:#AAFFAA;padding:8px;border-radius:4px;font-size:11px;min-height:36px;margin-bottom:8px;font-family:monospace;white-space:pre-wrap}
#input-area{margin-bottom:8px}
#input-area input{width:62%;padding:6px;background:#1a1a2e;color:white;border:1px solid #66BB6A;border-radius:3px;margin-right:4px;font-size:12px}
#input-area.delete-mode input{border-color:#FF6B6B}
#input-area button{padding:6px 10px;border:none;border-radius:3px;cursor:pointer;font-size:12px;font-weight:bold}
#log-wrap{border:2px solid #00BCD4;border-radius:4px;overflow:hidden}
#log-title{color:#FFD700;font-weight:bold;font-size:12px;text-align:center;padding:5px;background:#050D16;border-bottom:1px solid #00BCD4}
#log-body{background:#050D16;max-height:240px;overflow-y:auto}
#log-body table{width:100%;border-collapse:collapse;font-family:monospace;font-size:10px}
#log-body th{color:#00E5FF;padding:3px 4px;border-bottom:1px solid #00BCD4;background:#030B14;font-size:9px}
#log-body td{padding:3px 4px;color:#D0EEF8}
#page-nav{text-align:center;padding:3px;background:#050D16}
#page-nav button{padding:3px 7px;background:#0A0A14;color:#00E5FF;border:1px solid #00BCD4;border-radius:3px;cursor:pointer;margin:2px;font-size:11px}
#page-nav button.active{background:#003366;color:#FFD700;font-weight:bold}
#pid-modal{display:none;position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(0,0,0,.7);z-index:100;align-items:center;justify-content:center}
#pid-modal.show{display:flex}
#pid-box{background:#0D1B2A;border:2px solid #00BCD4;border-radius:8px;padding:24px;min-width:300px;text-align:center}
#pid-box h3{color:#FFD700;margin-bottom:12px;font-size:14px}
#pid-box p{color:#AAA;font-size:12px;margin-bottom:12px}
#pid-input{width:100%;padding:8px;background:#1a1a2e;color:white;border:1px solid #66BB6A;border-radius:4px;font-size:13px;margin-bottom:10px;text-align:center}
#pid-box .btn-row{display:flex;gap:8px}
#pid-box .btn-row button{flex:1;padding:8px;border:none;border-radius:4px;cursor:pointer;font-weight:bold;font-size:13px}
#confirm-store-btn{background:#1B5E20;color:#AAFFAA}
#cancel-store-btn{background:#3A0000;color:#FF6B6B}
</style>
</head>
<body>
<div id="header">WAREHOUSE SHUTTLE CONTROL SYSTEM</div>
<div id="main">
  <div id="left">
    <div id="status-bar">STATUS: READY</div>
    <div id="level-btns">
      <button class="lvl-btn" style="background:#1A237E" onclick="setLevel(0)">LEVEL 0</button>
      <button class="lvl-btn" style="background:#4A148C" onclick="setLevel(1)">LEVEL 1</button>
      <button class="lvl-btn" style="background:#004D40" onclick="setLevel(2)">LEVEL 2</button>
    </div>
    <div id="canvas-wrap">
      <canvas id="wh" width="610" height="430"></canvas>
      <canvas id="overlay" width="610" height="430" style="position:absolute;top:0;left:0;cursor:crosshair" onclick="onCanvasClick(event)"></canvas>
    </div>
    <div id="hint">Click empty cell → STORE &nbsp;|&nbsp; Filled cell → RETRIEVE &nbsp;|&nbsp; TOP/BOT dock → select</div>
  </div>
  <div id="right">
    <div id="panel-title">CONTROL PANEL</div>
    <div id="time-box">TOTAL TIME : 00m 00s (0.0s)</div>
    <button class="ctrl-btn" style="background:#1B5E20;color:#AAFFAA;font-size:14px" onclick="doExecute()">▶  EXECUTE QUEUE</button>
    <button class="ctrl-btn" id="pause-btn" style="background:#4A3800;color:#FFD700" onclick="doPause()">⏸  PAUSE</button>
    <button class="ctrl-btn" id="restore-btn" style="background:#1A1A2E;color:#FFA726;font-size:12px" onclick="doRestore()">RESTORE MODE: OFF</button>
    <button class="ctrl-btn" style="background:#3A0000;color:#FF6B6B;font-size:12px" onclick="doDeletePrompt()">✕  DELETE COMMAND</button>
    <button class="ctrl-btn" style="background:#7B1C1C;color:white;font-size:12px" onclick="doSave()">💾  SAVE STATE</button>
    <div id="msg-box">Click a cell to begin.</div>
    <div id="input-area"></div>
    <div id="log-wrap">
      <div id="log-title">COMMAND LOG &nbsp; <span id="log-stats" style="font-weight:normal;font-size:11px;color:#AAA"></span></div>
      <div id="log-body"><table><thead><tr><th>#</th><th>ACTION</th><th>PALLET ID</th><th>DK</th><th>LV</th><th>ROW</th><th>COL</th><th>STATUS</th><th>TIME</th></tr></thead><tbody id="log-rows"></tbody></table></div>
      <div id="page-nav" id="page-nav"></div>
    </div>
  </div>
</div>

<!-- Pallet ID Modal -->
<div id="pid-modal">
  <div id="pid-box">
    <h3 id="modal-title">Enter Pallet ID</h3>
    <p id="modal-desc"></p>
    <input type="text" id="pid-input" placeholder="e.g. PLT001" autocomplete="off">
    <div class="btn-row">
      <button id="confirm-store-btn" onclick="confirmStore()">STORE</button>
      <button id="cancel-store-btn" onclick="closeModal()">CANCEL</button>
    </div>
  </div>
</div>

<script>
// ── Constants ───────────────────────────────────────────────────────────────────
const CW=78, CH=56, OX=60, OY=30;
const ROWS=7, COLS=7;
const ROW_LBL=['A1','A0','AISLE','B0','B1','B2','B3'];
const COL_LBL=['Col 0','Col 1','Col 2','Col 3','Col 4','SERVICE','DOCK LANE'];
const SCLR={'PENDING':'#78909C','RUNNING':'#FFD700','DONE':'#66BB6A','ERROR':'#EF5350','ABORTED':'#FF8A65'};
const ACLR={'STORE':'#66BB6A','RETRIEVE':'#42A5F5','RESTORE':'#FFA726'};

// ── State ───────────────────────────────────────────────────────────────────────
let viewLvl=0, selDock=[1,6], restoreMode=false;
let executing=false, paused=false;
let animQueue=[];       // queue of plan arrays to animate
let currentPlan=null;   // current plan being animated
let planIdx=0;
let animTimer=null;
let shuttle={l:0,r:2,c:6,on_lift:false};
let loaded=false;
let serverCells=[];     // last known cell state from server
let localCells=[];      // cells being updated during animation
let curPage=0;
let pendingStore=null;  // {lvl,r,c} waiting for pallet ID
let deleteMode=false;
let logData=[];

// ── Canvas ──────────────────────────────────────────────────────────────────────
const cv  = document.getElementById('wh');
const ctx = cv.getContext('2d');

function cellAt(cells, r, c) {
  return cells.find(cl=>cl.r===r&&cl.c===c) || {r,c,v:0,pid:''};
}

function drawGrid(cells, sh, ld, sl_dock, restore) {
  ctx.clearRect(0,0,cv.width,cv.height);

  for(let r=0;r<ROWS;r++) {
    for(let c=0;c<COLS;c++) {
      const x=c*CW+OX, y=r*CH+OY;
      const cell=cellAt(cells,r,c);
      const v=cell.v, pid=cell.pid;

      // Background colour
      let bg='#12122a';
      if(r===2)         bg='#777';
      else if(c>=5)     bg='#252525';
      else if(v===-1)   bg='#1a1a1a';
      else if(v===1)    bg='#0D47A1';

      if(c===5&&r===1)  bg='#002F33';   // LIFT box

      ctx.fillStyle=bg;
      ctx.fillRect(x,y,CW-1,CH-1);
      ctx.strokeStyle='#1a1a2e'; ctx.lineWidth=1;
      ctx.strokeRect(x,y,CW-1,CH-1);

      ctx.textAlign='center'; ctx.textBaseline='middle';

      if(c===5&&r===1) {
        ctx.fillStyle='#00E5FF'; ctx.font='bold 11px Arial';
        ctx.fillText('LIFT',x+CW/2,y+CH/2);
      } else if(c===6&&r===1&&viewLvl===0) {
        const sel=(sl_dock[0]===1&&sl_dock[1]===6);
        ctx.fillStyle='#FFEB3B'; ctx.fillRect(x,y,CW-1,CH-1);
        ctx.strokeStyle=sel?'#00E5FF':'#555'; ctx.lineWidth=sel?3:1;
        ctx.strokeRect(x,y,CW-1,CH-1); ctx.lineWidth=1;
        ctx.fillStyle='black'; ctx.font='bold 12px Arial';
        ctx.fillText('TOP',x+CW/2,y+CH/2);
      } else if(c===6&&r===3&&viewLvl===0) {
        const sel=(sl_dock[0]===3&&sl_dock[1]===6);
        ctx.fillStyle='#FFEB3B'; ctx.fillRect(x,y,CW-1,CH-1);
        ctx.strokeStyle=sel?'#00E5FF':'#555'; ctx.lineWidth=sel?3:1;
        ctx.strokeRect(x,y,CW-1,CH-1); ctx.lineWidth=1;
        ctx.fillStyle='black'; ctx.font='bold 12px Arial';
        ctx.fillText('BOT',x+CW/2,y+CH/2);
      } else if(c>=5) {
        // other service/dock cells — empty
      } else if(v===-1) {
        ctx.fillStyle='#444'; ctx.font='9px Arial';
        ctx.fillText('WALL',x+CW/2,y+CH/2);
      } else if(pid) {
        const isRq=false; // restore highlight handled separately
        ctx.fillStyle=restore&&v===1?'#FFA72644':'transparent';
        if(restore&&v===1){ctx.fillRect(x,y,CW-1,CH-1);}
        ctx.fillStyle='white'; ctx.font='bold 8px Arial';
        ctx.fillText(ROW_LBL[r],x+CW/2,y+CH/2-7);
        ctx.fillText(pid.substring(0,10),x+CW/2,y+CH/2+6);
      } else {
        ctx.fillStyle='#444'; ctx.font='8px Arial';
        ctx.fillText(ROW_LBL[r],x+CW/2,y+CH/2-5);
        ctx.fillText('OPEN',x+CW/2,y+CH/2+5);
      }
    }
  }

  // Row labels
  ctx.fillStyle='#BBBBBB'; ctx.font='bold 11px Arial';
  ctx.textAlign='right'; ctx.textBaseline='middle';
  for(let r=0;r<ROWS;r++) ctx.fillText(ROW_LBL[r],OX-6,r*CH+OY+CH/2);

  // Col labels
  ctx.textAlign='center'; ctx.textBaseline='bottom';
  ctx.font='10px Arial';
  for(let c=0;c<COLS;c++) ctx.fillText(COL_LBL[c],c*CW+OX+CW/2,OY-3);

  // Level badge
  ctx.fillStyle='#1C1C00';
  ctx.fillRect(cv.width-95,2,90,22);
  ctx.strokeStyle='#FFD700'; ctx.lineWidth=2;
  ctx.strokeRect(cv.width-95,2,90,22); ctx.lineWidth=1;
  ctx.fillStyle='#FFD700'; ctx.font='bold 13px Arial';
  ctx.textAlign='center'; ctx.textBaseline='middle';
  ctx.fillText('LEVEL '+viewLvl,cv.width-50,13);

  // Shuttle
  const onLift=sh.on_lift||(sh.c===5&&sh.r===1);
  const dr=onLift?1:sh.r;
  if(sh.l===viewLvl) {
    const sx=sh.c*CW+OX, sy=dr*CH+OY;
    ctx.fillStyle=ld?'#FF9800':'#FFFF00';
    ctx.fillRect(sx+3,sy+3,CW-7,CH-7);
    ctx.strokeStyle='white'; ctx.lineWidth=2;
    ctx.strokeRect(sx+3,sy+3,CW-7,CH-7); ctx.lineWidth=1;
    ctx.fillStyle='black'; ctx.font='bold 16px Arial';
    ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText(ld?'🚚':'●',sx+CW/2,sy+CH/2);
  }
}

function redraw() {
  drawGrid(localCells.length?localCells:serverCells, shuttle, loaded, selDock, restoreMode);
}

// ── Animation engine ─────────────────────────────────────────────────────────────
function startAnimation(plans) {
  // plans = array of frame arrays, one per command
  animQueue = plans.slice();
  localCells = JSON.parse(JSON.stringify(serverCells));
  shuttle = {l:0,r:2,c:6,on_lift:false};
  loaded  = false;
  nextCommand();
}

function nextCommand() {
  if(!animQueue.length) {
    executing=false; paused=false;
    setStatus('ALL DONE ✓');
    fetchState(); // refresh from server
    return;
  }
  currentPlan = animQueue.shift();
  planIdx=0;
  stepAnim();
}

function stepAnim() {
  if(paused) return;
  if(planIdx>=currentPlan.length) {
    nextCommand(); return;
  }
  const frame=currentPlan[planIdx++];
  const ms=frame.ms||350;

  // Apply frame
  if(frame.type==='move') {
    shuttle={l:frame.l,r:frame.r,c:frame.c,on_lift:!!frame.on_lift};
    viewLvl=frame.l;
    setStatus(frame.msg||'MOVING');
  } else if(frame.type==='load') {
    loaded=true; setStatus('LOADING');
  } else if(frame.type==='place') {
    const cell=localCells.find(cl=>cl.r===frame.r&&cl.c===frame.c);
    if(cell){cell.v=1;cell.pid=frame.pid;}
    loaded=false; setStatus('PLACED '+frame.pid);
  } else if(frame.type==='pick') {
    const cell=localCells.find(cl=>cl.r===frame.r&&cl.c===frame.c);
    if(cell){cell.v=0;cell.pid='';}
    loaded=true; setStatus(frame.msg||'PICKED');
  } else if(frame.type==='deliver') {
    loaded=false; setStatus('DELIVERED');
  } else if(frame.type==='status') {
    setStatus(frame.msg||'');
  } else if(frame.type==='done') {
    nextCommand(); return;
  }

  redraw();
  animTimer=setTimeout(stepAnim,ms);
}

// ── Level switch ─────────────────────────────────────────────────────────────────
function setLevel(lvl) {
  if(executing&&!paused) return;
  viewLvl=lvl;
  fetchState();
}

// ── Status bar ────────────────────────────────────────────────────────────────────
function setStatus(txt) {
  document.getElementById('status-bar').textContent=
    'STATUS: '+txt+'   |   LEVEL '+viewLvl+'   |   QUEUE: ?/'+50;
}

// ── Fetch state from server ───────────────────────────────────────────────────────
function fetchState() {
  fetch('/api/state?lvl='+viewLvl)
    .then(r=>r.json())
    .then(data=>{
      serverCells=data.cells;
      if(!executing) {
        localCells=[]; shuttle=data.shuttle; loaded=data.loaded;
        selDock=data.sel_dock; restoreMode=data.restore;
      }
      document.getElementById('status-bar').textContent=
        'STATUS: '+data.status+'   |   LEVEL '+viewLvl+
        '   |   QUEUE: '+data.queue_len+'/'+50+
        '   |   pending:'+data.pending+'  done:'+data.done;
      document.getElementById('time-box').textContent=
        'TOTAL TIME :  '+data.total_time;
      document.getElementById('restore-btn').textContent=
        restoreMode?'RESTORE MODE: ON':'RESTORE MODE: OFF';
      document.getElementById('restore-btn').style.background=
        restoreMode?'#3E1F00':'#1A1A2E';
      logData=data.log||[];
      renderLog();
      redraw();
    }).catch(()=>{});
}

// ── Canvas click ──────────────────────────────────────────────────────────────────
function onCanvasClick(evt) {
  if(executing&&!paused) {showMsg('Pause before adding commands.'); return;}
  const rect=document.getElementById('overlay').getBoundingClientRect();
  const x=evt.clientX-rect.left, y=evt.clientY-rect.top;
  const c=Math.floor((x-OX)/CW), r=Math.floor((y-OY)/CH);
  if(c<0||c>=COLS||r<0||r>=ROWS) return;

  // Dock selection
  if(viewLvl===0&&c===6&&(r===1||r===3)) {
    fetch('/api/select_dock',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({r,c:6})})
      .then(res=>res.json()).then(d=>{selDock=d.sel_dock;fetchState();
        showMsg(r===1?'Selected TOP dock.':'Selected BOT dock.');});
    return;
  }
  if(c>=5||r===2) return;

  // Get cell from current cells
  const cells=localCells.length?localCells:serverCells;
  const cell=cellAt(cells,r,c);

  if(restoreMode) {
    if(cell.v!==1){showMsg('Click an OCCUPIED cell in Restore Mode.');return;}
    fetch('/api/queue_restore',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({lvl:viewLvl,r,c})})
      .then(res=>res.json()).then(d=>{showMsg(d.msg);fetchState();});
    return;
  }

  if(cell.v===0) {
    // STORE
    pendingStore={lvl:viewLvl,r,c};
    document.getElementById('modal-title').textContent='Store Pallet';
    document.getElementById('modal-desc').textContent=
      `Level ${viewLvl}  |  Row ${ROW_LBL[r]}  |  Col ${c}`;
    document.getElementById('pid-input').value='';
    document.getElementById('pid-modal').classList.add('show');
    setTimeout(()=>document.getElementById('pid-input').focus(),100);
  } else {
    // RETRIEVE
    fetch('/api/queue_retrieve',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({lvl:viewLvl,r,c})})
      .then(res=>res.json()).then(d=>{showMsg(d.msg);fetchState();});
  }
}

// ── Pallet ID modal ───────────────────────────────────────────────────────────────
document.getElementById('pid-input').addEventListener('keydown',e=>{
  if(e.key==='Enter') confirmStore();
  if(e.key==='Escape') closeModal();
});

function confirmStore() {
  const pid=document.getElementById('pid-input').value.trim();
  if(!pid){showMsg('Pallet ID cannot be empty.'); return;}
  closeModal();
  fetch('/api/queue_store',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({lvl:pendingStore.lvl,r:pendingStore.r,c:pendingStore.c,pid})})
    .then(res=>res.json()).then(d=>{showMsg(d.msg);fetchState();});
}

function closeModal() {
  document.getElementById('pid-modal').classList.remove('show');
  pendingStore=null;
}

// ── Buttons ───────────────────────────────────────────────────────────────────────
function doExecute() {
  if(executing){showMsg('Already executing.'); return;}
  fetch('/api/execute',{method:'POST'})
    .then(r=>r.json())
    .then(data=>{
      if(!data.ok){showMsg(data.msg); return;}
      executing=true; paused=false;
      document.getElementById('pause-btn').textContent='⏸  PAUSE';
      document.getElementById('pause-btn').style.background='#4A3800';
      showMsg('Executing — watch the shuttle move!');
      const plans=data.plans.map(p=>p.frames);
      startAnimation(plans);
    });
}

function doPause() {
  if(!executing&&!paused){showMsg('Nothing executing.'); return;}
  if(paused) {
    paused=false;
    document.getElementById('pause-btn').textContent='⏸  PAUSE';
    document.getElementById('pause-btn').style.background='#4A3800';
    showMsg('Resumed.');
    stepAnim();
  } else {
    paused=true;
    if(animTimer) clearTimeout(animTimer);
    document.getElementById('pause-btn').textContent='▶  RESUME';
    document.getElementById('pause-btn').style.background='#003366';
    showMsg('Paused.');
  }
}

function doRestore() {
  fetch('/api/toggle_restore',{method:'POST'})
    .then(r=>r.json()).then(d=>{
      restoreMode=d.restore;
      document.getElementById('restore-btn').textContent=
        restoreMode?'RESTORE MODE: ON':'RESTORE MODE: OFF';
      document.getElementById('restore-btn').style.background=
        restoreMode?'#3E1F00':'#1A1A2E';
      showMsg(restoreMode?'RESTORE MODE ON — click a stored pallet.':'RESTORE MODE OFF.');
    });
}

function doDeletePrompt() {
  const area=document.getElementById('input-area');
  area.className='delete-mode';
  area.innerHTML=`
    <input type="text" id="del-input" placeholder="Enter Pallet ID to delete..." style="width:62%;padding:6px;background:#1a1a2e;color:white;border:1px solid #FF6B6B;border-radius:3px;margin-right:4px;font-size:12px">
    <button onclick="doDeleteConfirm()" style="padding:6px 10px;background:#6B0000;color:white;border:none;border-radius:3px;cursor:pointer;font-size:12px;font-weight:bold">DELETE</button>
  `;
  document.getElementById('del-input').addEventListener('keydown',e=>{
    if(e.key==='Enter') doDeleteConfirm();
  });
  showMsg('Enter Pallet ID to delete from queue.');
  setTimeout(()=>document.getElementById('del-input').focus(),100);
}

function doDeleteConfirm() {
  const pid=document.getElementById('del-input').value.trim();
  if(!pid){showMsg('Enter a Pallet ID.'); return;}
  fetch('/api/delete_command',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({pid})})
    .then(r=>r.json()).then(d=>{
      showMsg(d.msg);
      document.getElementById('input-area').innerHTML='';
      fetchState();
    });
}

function doSave() {
  fetch('/api/save_state',{method:'POST'})
    .then(r=>r.json()).then(d=>showMsg(d.msg));
}

function showMsg(txt) {
  document.getElementById('msg-box').textContent=txt;
}

// ── Command log ───────────────────────────────────────────────────────────────────
const PER_PAGE=10, NUM_PAGES=5;
let curLogPage=0;

function renderLog() {
  const pend=logData.filter(e=>e.status==='PENDING').length;
  const done=logData.filter(e=>e.status==='DONE').length;
  document.getElementById('log-stats').textContent=
    `pending:${pend}  done:${done}  total:${logData.length}`;

  const start=curLogPage*PER_PAGE;
  const rows=logData.slice(start,start+PER_PAGE);
  const tbody=document.getElementById('log-rows');
  tbody.innerHTML='';
  const bgMap={RUNNING:'#1A2A00',DONE:'#061206',ERROR:'#2A0000',ABORTED:'#2A1200'};
  const acMap={STORE:'#66BB6A',RETRIEVE:'#42A5F5',RESTORE:'#FFA726',DONE:'#2E6B30',ABORTED:'#8B5000',ERROR:'#8B0000'};
  rows.forEach((e,i)=>{
    const bg=bgMap[e.status]||(i%2===0?'#0A1B2A':'#071018');
    const ac=e.status==='DONE'?acMap.DONE:e.status==='ABORTED'?acMap.ABORTED:e.status==='ERROR'?acMap.ERROR:(acMap[e.action]||'#FFF');
    const sc=SCLR[e.status]||'#FFF';
    const tr=document.createElement('tr');
    tr.style.background=bg;
    const cells=[
      {v:String(start+i+1),c:'#D0EEF8'},
      {v:e.action,c:ac,bold:true},
      {v:e.pid,c:'#D0EEF8'},
      {v:e.dock,c:'#D0EEF8'},
      {v:e.lvl,c:'#D0EEF8'},
      {v:e.row,c:'#D0EEF8'},
      {v:e.col,c:'#D0EEF8'},
      {v:e.status,c:sc,bold:true},
      {v:e.time,c:e.time!=='-'?'#FFA726':'#546E7A'},
    ];
    cells.forEach(({v,c,bold})=>{
      const td=document.createElement('td');
      td.textContent=v; td.style.color=c;
      if(bold) td.style.fontWeight='bold';
      tr.appendChild(td);
    });
    tbody.appendChild(tr);
  });

  // Page nav
  const nav=document.getElementById('page-nav');
  nav.innerHTML='';
  const mkBtn=(lbl,pg,active)=>{
    const b=document.createElement('button');
    b.textContent=lbl; if(active) b.className='active';
    b.onclick=()=>{curLogPage=pg;renderLog();};
    nav.appendChild(b);
  };
  mkBtn('◀',Math.max(0,curLogPage-1),false);
  for(let i=0;i<NUM_PAGES;i++) mkBtn(String(i+1),i,i===curLogPage);
  mkBtn('▶',Math.min(NUM_PAGES-1,curLogPage+1),false);
}

// ── Init ──────────────────────────────────────────────────────────────────────────
fetchState();
setInterval(()=>{if(!executing) fetchState();},3000);
</script>
</body>
</html>
"""

@app.route('/api/state')
def api_state():
    with _lock:
        lvl=request.args.get('lvl',0,type=int)
        tt=total_time; mm,ss=divmod(int(tt),60)
        pend=sum(1 for e in cmd_log if e['status']=='PENDING')
        done=sum(1 for e in cmd_log if e['status']=='DONE')
        log_rows=[]
        for i,e in enumerate(cmd_log):
            ela=e.get('elapsed')
            tt2=('-' if ela is None else f"{ela:.1f}s" if ela<60
                 else f"{int(ela)//60}m{int(ela)%60:02d}s")
            log_rows.append({'i':i+1,'action':e['action'],
                             'pid':str(e.get('pallet_id','?'))[:12],
                             'dock':_dlbl(e.get('dock',[1,6])),
                             'lvl':str(e.get('lvl','?')),
                             'row':ROW_LBL.get(e.get('r',-1),'?'),
                             'col':str(e.get('c','?')),
                             'status':e['status'],'time':tt2})
        return jsonify({
            'cells':     wh_state_json(lvl),
            'shuttle':   {'l':shuttle[0],'r':shuttle[1],'c':shuttle[2]},
            'loaded':    loaded,
            'sel_dock':  list(sel_dock),
            'restore':   restore_md,
            'status':    status_txt,
            'total_time':f"{mm:02d}m {ss:02d}s ({tt:.1f}s)",
            'queue_len': len(cmd_queue),
            'log':       log_rows,
            'pending':   pend,
            'done':      done,
        })

@app.route('/api/execute', methods=['POST'])
def api_execute():
    global status_txt
    with _lock:
        if not cmd_queue:
            return jsonify({'ok':False,'msg':'Queue is empty.'})
        plans=[]
        while cmd_queue:
            action,args=cmd_queue.popleft()
            cid=args.get('_cid')
            if action=='STORE':
                f=build_store(args['lvl'],args['r'],args['c'],args['pallet_id'],args['dock'])
            elif action=='RETRIEVE':
                f=build_retrieve(args['lvl'],args['r'],args['c'],args['dock'],args['pallet_id'])
            elif action=='RESTORE':
                f=build_restore(args['src_lvl'],args['src_r'],args['src_c'],args['pallet_id'],args['dock'])
            else: f=[]
            elapsed=sum(x.get('t',0) for x in f)
            apply_plan(f)
            if cid is not None: log_set(cid,'DONE',elapsed)
            plans.append({'cid':cid,'frames':f})
        status_txt="ALL DONE"
        return jsonify({'ok':True,'plans':plans})

@app.route('/api/select_dock', methods=['POST'])
def api_select_dock():
    with _lock:
        d=request.json; sel_dock[:]=[d['r'],d['c']]
        return jsonify({'ok':True,'sel_dock':list(sel_dock)})

@app.route('/api/toggle_restore', methods=['POST'])
def api_toggle_restore():
    global restore_md
    with _lock:
        restore_md=not restore_md
        return jsonify({'ok':True,'restore':restore_md})

@app.route('/api/queue_store', methods=['POST'])
def api_queue_store():
    global status_txt
    with _lock:
        d=request.json
        lvl=d['lvl']; r=d['r']; c=d['c']; pid=d['pid']
        if len(cmd_queue)>=MAX_QUEUE:
            return jsonify({'ok':False,'msg':f'Queue full ({MAX_QUEUE}).'})
        if not pid or not pid.strip():
            return jsonify({'ok':False,'msg':'Pallet ID cannot be empty.'})
        pid=pid.strip()
        if ' ' in pid:
            return jsonify({'ok':False,'msg':'No spaces in Pallet ID.'})
        if pid in registry.values() or any(cmd[1].get('pallet_id')==pid for cmd in cmd_queue):
            return jsonify({'ok':False,'msg':f"'{pid}' already in use."})
        if any(cmd[0]=='STORE' and cmd[1].get('lvl')==lvl
               and cmd[1].get('r')==r and cmd[1].get('c')==c for cmd in cmd_queue):
            return jsonify({'ok':False,'msg':'Slot already has a pending STORE.'})
        ok,msg=store_valid_queue(lvl,r,c)
        if not ok: return jsonify({'ok':False,'msg':msg})
        args={'lvl':lvl,'r':r,'c':c,'pallet_id':pid,'dock':list(sel_dock)}
        cid=log_add('STORE',args); args['_cid']=cid
        cmd_queue.append(('STORE',args))
        status_txt=f"Queued STORE: {pid}"
        return jsonify({'ok':True,'msg':f'STORE queued: {pid}'})

@app.route('/api/queue_retrieve', methods=['POST'])
def api_queue_retrieve():
    global status_txt
    with _lock:
        d=request.json
        lvl=d['lvl']; r=d['r']; c=d['c']
        pid=registry.get((lvl,r,c),'?')
        if len(cmd_queue)>=MAX_QUEUE:
            return jsonify({'ok':False,'msg':f'Queue full ({MAX_QUEUE}).'})
        if any(cmd[0]=='RETRIEVE' and cmd[1].get('lvl')==lvl
               and cmd[1].get('r')==r and cmd[1].get('c')==c for cmd in cmd_queue):
            return jsonify({'ok':False,'msg':f'RETRIEVE for {pid} already queued.'})
        args={'lvl':lvl,'r':r,'c':c,'pallet_id':pid,'dock':list(sel_dock)}
        cid=log_add('RETRIEVE',args); args['_cid']=cid
        cmd_queue.append(('RETRIEVE',args))
        status_txt=f"Queued RETRIEVE: {pid}"
        return jsonify({'ok':True,'msg':f'RETRIEVE queued: {pid}'})

@app.route('/api/queue_restore', methods=['POST'])
def api_queue_restore():
    global status_txt
    with _lock:
        d=request.json
        lvl=d['lvl']; r=d['r']; c=d['c']
        pid=registry.get((lvl,r,c),'?')
        if wh[lvl,r,c]!=1:
            return jsonify({'ok':False,'msg':'Click an OCCUPIED cell.'})
        if any(cmd[0]=='RESTORE' and cmd[1]['src_lvl']==lvl
               and cmd[1]['src_r']==r and cmd[1]['src_c']==c for cmd in cmd_queue):
            return jsonify({'ok':False,'msg':f'{pid} already queued for restore.'})
        args={'src_lvl':lvl,'src_r':r,'src_c':c,'lvl':0,
              'r':sel_dock[0],'c':6,'pallet_id':pid,'dock':list(sel_dock)}
        cid=log_add('RESTORE',args); args['_cid']=cid
        cmd_queue.append(('RESTORE',args))
        status_txt=f"Queued RESTORE: {pid}"
        return jsonify({'ok':True,'msg':f'RESTORE queued: {pid}'})

@app.route('/api/delete_command', methods=['POST'])
def api_delete_command():
    with _lock:
        d=request.json; pid=d.get('pid','').strip()
        found=None
        for cmd in list(cmd_queue):
            if cmd[1].get('pallet_id')==pid: found=cmd; break
        if found is None:
            return jsonify({'ok':False,'msg':f"No pending command for '{pid}'."})
        cmd_queue.remove(found)
        cid=found[1].get('_cid')
        if cid is not None:
            for i,e in enumerate(cmd_log):
                if e['cid']==cid: cmd_log.pop(i); break
        return jsonify({'ok':True,'msg':f"Deleted command for '{pid}'."})

@app.route('/api/save_state', methods=['POST'])
def api_save_state():
    with _lock:
        save_state()
        return jsonify({'ok':True,'msg':'State saved to Desktop.'})

load_state()

if __name__=='__main__':
    port=int(os.environ.get('PORT',8050))
    app.run(debug=False, host='0.0.0.0', port=port)
