#!/usr/bin/env python3
"""Rebuild all project proofs in a prepared, bounded Azure mathlib checkout.

No compiled project theorem is reused: every dependency is compiled in order.
External mathlib dependencies use the pinned toolchain's ordinary cache.
"""
import argparse,hashlib,json,os,pathlib,re,subprocess,time
p=argparse.ArgumentParser()
p.add_argument('--project',type=pathlib.Path,default=pathlib.Path.cwd())
p.add_argument('--plan-only',action='store_true')
a=p.parse_args();root=a.project.resolve()
project_prefixes=('MathIsEasy.','Geometry.')
project_roots={'Algebra','Polygon','Facet','Coordinates','Plane','Parameters','Positions',
 'Embedding','ColouringTransfer','Final','FoundationAudit','Audit','PositiveControlSAT'}
order=[];seen=set();visiting=set()
def visit(name):
 if not (name in project_roots or name.startswith(project_prefixes)):return
 if name in seen:return
 if name in visiting:raise RuntimeError('Import cycle: '+name)
 visiting.add(name)
 source=root/(name.replace('.','/')+'.lean')
 if not source.is_file():raise RuntimeError('Missing project source: '+str(source))
 for dependency in re.findall(r'^import (\S+)',source.read_text(),re.M):visit(dependency)
 visiting.remove(name);seen.add(name);order.append(name)
visit('Audit');visit('PositiveControlSAT')
controls={'NegativeControl':'Tactic `decide` proved that the proposition',
 'NegativeControlSAT':'LRAT step 0, clause 2: no refutation',
 'NegativeKernel':'(kernel) declaration type mismatch'}
if a.plan_only:
 print(json.dumps({'modules':order,'expected_failures':controls},indent=2));raise SystemExit
if not pathlib.Path('/run/mathiseasy-azure-verified').is_file():
 raise SystemExit('Full builds are Azure-only. Use the bounded Azure controller.')
# The parent job must bound the entire process tree, not just individual Lean commands.
parts=[line.split(':',2) for line in pathlib.Path('/proc/self/cgroup').read_text().splitlines()]
cgroup=next(path for hierarchy,controllers,path in parts if hierarchy=='0')
cap=(pathlib.Path('/sys/fs/cgroup')/cgroup.lstrip('/')/'memory.max').read_text().strip()
if cap=='max' or int(cap)>24*1024**3:raise SystemExit('A whole-job memory limit of at most 24 GiB is required')
commit=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip()
if commit!='5ed2965256430c3649e86755f9576b54eca72435':raise SystemExit('Wrong mathlib commit')
version=subprocess.check_output(['lake','env','lean','--version'],cwd=root,text=True).strip()
if not version.startswith('Lean (version 4.34.0,'):raise SystemExit('Wrong Lean version')
started=time.monotonic();records=[]
def save(status):
 (root/'rebuild-report.json').write_text(json.dumps({'status':status,'lean':version,
  'mathlib':commit,'seconds':round(time.monotonic()-started,3),'records':records},indent=2)+'\n')
def compile_module(name,expected_error=None):
 source=name.replace('.','/')+'.lean'
 remaining=6600-(time.monotonic()-started)
 if remaining<=0:raise RuntimeError('Whole-build time limit reached')
 cmd=['lake','env','lean','-j1','-M18000','-DElab.async=false']
 if not name.startswith('MathIsEasy.'):cmd+=['-DwarningAsError=true']
 cmd+=['-o',name.replace('.','/')+'.olean',source]
 begin=time.monotonic()
 try:
  run=subprocess.run(cmd,cwd=root,env=dict(os.environ,LEAN_PATH=str(root)),
   stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=min(900,remaining))
  code,log=run.returncode,run.stdout
 except subprocess.TimeoutExpired:
  code,log=124,'Compilation timeout'
 record={'module':name,'source_sha256':hashlib.sha256((root/source).read_bytes()).hexdigest(),
  'exit_code':code,'seconds':round(time.monotonic()-begin,3),'log':log,
  'expected_failure':expected_error is not None}
 records.append(record)
 ok=(code==0) if expected_error is None else (code!=0 and code!=124 and expected_error in log)
 save('IN_PROGRESS' if ok else 'FAILED')
 print(name+': '+('PASS' if ok else 'FAIL'),flush=True)
 if name in ('Audit','PositiveControlSAT') or expected_error is not None or not ok: print(log,flush=True)
 if not ok:raise RuntimeError('Verification failed: '+name)
for module in order:compile_module(module)
for module,diagnostic in controls.items():compile_module(module,diagnostic)
save('VERIFIED')
