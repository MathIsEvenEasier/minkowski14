#!/usr/bin/env python3
"""Lightweight integrity and publication correspondence checks; never run Lean."""
import gzip,hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[1]
def read(path):return json.loads((root/path).read_text())
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1024**2),b''):h.update(b)
 return h.hexdigest()
report=read('evidence/verification-final.json');assert report['status']=='VERIFIED'
assert report['cleanup']['all_deleted'] and report['geometry_development_cleanup']['all_deleted']
for m in report['modules']:
 p=root/'formal'/(m['module'].replace('.','/')+'.lean')
 assert sha(p)==m['source_sha256'],str(p)
for c in report['negative_controls']:
 assert c['rejected'] and sha(root/'formal'/(c['module']+'.lean'))==c['source_sha256']
manifest=read('evidence/proof-source-manifest.json')
for n in ['artifacts/minkowski14_final_graph.json','artifacts/minkowski14_final_4color.cnf']:
 assert sha(root/'formal'/n)==manifest[n]
h=hashlib.sha256()
with gzip.open(root/'formal/artifacts/minkowski14_final_4color.lrat.gz','rb') as f:
 for b in iter(lambda:f.read(1024**2),b''):h.update(b)
assert h.hexdigest()==manifest['artifacts/minkowski14_final_4color.lrat']
for name,value in report['generation_reproduction']['files'].items():assert sha(root/'formal'/name)==value
assert sha(root/'formal/generate_geometry.py')==report['generation_reproduction']['generator_sha256']
g=read('formal/artifacts/minkowski14_final_graph.json');browser=read('docs/graph.json')
assert browser['coordinates']==g['vertices_power_basis']
assert browser['parameters']==read('formal/geometry-generation.json')['parameters']
w=[]
for i in range(1,29):
 s=(root/f'formal/Geometry/Chunk{i:03d}.lean').read_text().split('theorem edge_list')[0]
 w.extend([list(map(int,m)) for m in re.findall(r'\((\d+), (\d+), (\d+)\)',s)])
assert browser['witnesses']==w and len(w)==13755
assert sorted([e[:2] for e in w])==sorted(g['edges'])
assert len(browser['coordinates'])==1540
for n in re.findall(r"path:'([^']+)'",(root/'docs/app.mjs').read_text()):
 assert (root/'formal'/n.split('#')[0]).is_file(),n
for n in re.findall(r'https://github.com/MathIsEvenEasier/minkowski14/blob/main/([^"<>\s]+)',(root/'docs/index.html').read_text()):
 assert (root/n.split('#')[0]).is_file(),n
print(json.dumps({'status':'PASS_PUBLIC_PACKET','verified_module_hashes':len(report['modules']),
 'negative_controls':len(report['negative_controls']),'browser_witnesses':len(w),
 'lrat_decompressed_sha256':h.hexdigest(),'all_cloud_resources_deleted':True},indent=2))
