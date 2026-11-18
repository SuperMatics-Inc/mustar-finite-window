"""Replay all computations included in the note; capture true subprocess exits."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
here = Path(__file__).resolve().parent
logs = here.parent/'logs'
logs.mkdir(exist_ok=True)
env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
commands = [
    ['certify_cx.py'],
    ['certify_threshold.py'],
    ['certify_physical.py','1','5','13','100','0.01'],
    ['certify_physical.py','2','5','13','100','0.01'],
    ['certify_physical.py','4','10','1','5','0.01'],
    ['certify_physical.py','8','5','13','100','0.01'],
    ['scope_values.py'],
    ['certify_fixed_omega.py'],
    ['certify_deeper.py'],
    ['verify_independent.py'],
]
records = []
for args in commands:
    cmd = [sys.executable,*args]
    proc = subprocess.run(cmd,cwd=here,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    name = '_'.join(args).replace('.py','')+'.log'
    (logs/name).write_text(proc.stdout,encoding='utf-8')
    records.append(dict(command=cmd,cwd=str(here),exit_code=proc.returncode,log='logs/'+name))
    print(args,'EXIT',proc.returncode,flush=True)
    if proc.returncode:
        print(proc.stdout)
        break
(logs/'calculation_receipts.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
raise SystemExit(0 if len(records)==len(commands) and all(r['exit_code']==0 for r in records) else 1)
