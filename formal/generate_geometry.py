"""Azure-only exact witness generation. All output claims are rechecked by Lean."""
import json,pathlib,functools,re,argparse
assert pathlib.Path('/run/mathiseasy-azure-verified').is_file()
parser=argparse.ArgumentParser();parser.add_argument('--root',type=pathlib.Path,default=pathlib.Path('/opt/minkowski14-proof'))
root=parser.parse_args().root
graph=json.loads((root/'artifacts/minkowski14_final_graph.json').read_text())
verts=[tuple(v) for v in graph['vertices_power_basis']]
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def rot(a):
 x=a[5];return (-x,a[0]+x,a[1]-x,a[2]+x,a[3]-x,a[4]+x)
def mul(a,b):
 r=(0,)*6
 for x in b:r=add(r,tuple(x*y for y in a));a=rot(a)
 return r
one=(1,0,0,0,0,0);inv=(0,-1,0,-1,0,-1)
from fractions import Fraction
lo=Fraction(1246979603717467,10**15);hi=lo+Fraction(1,10**15)
def interval(a,b,c):
 lower=a+min(b*lo,b*hi)+min(c*lo*lo,c*hi*hi)
 upper=a+max(b*lo,b*hi)+max(c*lo*lo,c*hi*hi)
 return lower>=0 and upper<=1
@functools.lru_cache(None)
def witness(d):
 for j in range(14):
  dr=d
  for _ in range((-j)%14):dr=rot(dr)
  p=mul(sub(dr,one),inv)
  a,b,c=p[0]+2*p[3],p[2],-p[3]
  if p==(a+2*c,0,b,-c,c,-b) and interval(a,b,c):return j,(a,b,c)
 raise ValueError('No boundary certificate: '+repr(d))
# Read the exact edge order used by the Lean graph, and cross-check the JSON edge set.
chunks=[]
for i in range(1,29):
 text=(root/f'MathIsEasy/Minkowski14/GraphData/Chunk{i:03d}.lean').read_text()
 edges=[tuple(map(int,m)) for m in re.findall(r'\((\d+), (\d+)\)',text)]
 chunks.append(edges)
assert sorted(sum(chunks,[]))==sorted(tuple(e) for e in graph['edges'])
ws={d:witness(d) for edges in chunks for u,v in edges for d in [sub(verts[u],verts[v])]}
params=sorted(set(p for j,p in ws.values()))
def integer(x):return str(x) if x>=0 else '('+str(x)+')'
def coord(v):return '⟨'+', '.join(map(integer,v))+'⟩'
out=root/'Geometry';out.mkdir(exist_ok=True)
(root/'Parameters.lean').write_text('''import Coordinates
set_option linter.unusedSimpArgs false
noncomputable section
namespace Minkowski14

def parameter : Nat → ℤ × ℤ × ℤ
'''+''.join(f'  | {i} => ({integer(a)}, {integer(b)}, {integer(c)})\n' for i,(a,b,c) in enumerate(params))+'''  | _ => (0,0,0)

theorem parameter_bounds (n : Nat) :
    0 ≤ parameterValue (parameter n) ∧ parameterValue (parameter n) ≤ 1 := by
  have h0 := rho_lower
  have h1 := rho_upper
  have h2 : (1246979603717467 / 1000000000000000 : ℝ)^2 < rho^2 := by nlinarith [rho_gt_one]
  have h3 : rho^2 < (1246979603717468 / 1000000000000000 : ℝ)^2 := by nlinarith [rho_gt_one]
  have hr : 0 < rho := by linarith [rho_gt_one]
  unfold parameter parameterValue
  split <;> norm_num [abs_of_pos hr] <;> constructor <;> nlinarith

def unitCoordinate (k : Nat) : Coordinate :=
  Coordinate.rotate (k % 14) (sideCoordinate (parameter (k / 14)))

theorem unitCoordinate_norm (k : Nat) : polygonNorm (Coordinate.eval (unitCoordinate k)) = 1 := by
  rw [unitCoordinate, Coordinate.eval_rotate, eval_sideCoordinate]
  apply rotated_side_unit
  · rw [← pow_mul, Nat.mul_comm, pow_mul, zeta_primitive.pow_eq_one, one_pow]
  · exact (parameter_bounds (k/14)).1
  · exact (parameter_bounds (k/14)).2

end Minkowski14
''')
def tree(lo,hi):
 if hi-lo==1:return '.leaf '+coord(verts[lo])
 m=(lo+hi)//2
 return f'.branch {m} ({tree(lo,m)}) ({tree(m,hi)})'
(root/'Positions.lean').write_text('''import Parameters
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Minkowski14

inductive CoordinateTree where
  | leaf : Coordinate → CoordinateTree
  | branch : Nat → CoordinateTree → CoordinateTree → CoordinateTree

def CoordinateTree.lookup : CoordinateTree → Nat → Coordinate
  | .leaf value, _ => value
  | .branch cutoff left right, n =>
      if n < cutoff then left.lookup n else right.lookup n

def positions : CoordinateTree :=
  '''+tree(0,len(verts))+'''

def coordinate (n : Nat) : Coordinate :=
  if n < 1540 then positions.lookup n else default
noncomputable def point (n : Nat) : ℂ := Coordinate.eval (coordinate n)
end Minkowski14
''')
for i,edges in enumerate(chunks,1):
 cases=[]
 for u,v in edges:
  j,p=ws[sub(verts[u],verts[v])];code=14*params.index(p)+j
  cases.append((u,v,code))
 source=f'''import Positions
import MathIsEasy.Minkowski14.GraphData.Chunk{i:03d}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Minkowski14.Geometry{i:03d}
open MathIsEasy.Minkowski14.FinalGraph.Data

def witnesses : List (Nat × Nat × Nat) := [
'''+',\n'.join(f'  ({u}, {v}, {c})' for u,v,c in cases)+f''']

theorem edge_list : witnesses.map (fun e => (e.1, e.2.1)) = edgeChunk{i:03d} := rfl

theorem checked : witnesses.all (fun e =>
    decide (Coordinate.sub (coordinate e.1) (coordinate e.2.1) = unitCoordinate e.2.2)) = true := by
  decide

theorem edge_unit (u v : Nat) (h : (u,v) ∈ edgeChunk{i:03d}) :
    polygonNorm (point u - point v) = 1 := by
  rw [← edge_list] at h
  obtain ⟨⟨u',v',k⟩, hm, he⟩ := List.mem_map.mp h
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  have hc := (List.all_eq_true.mp checked) (u',v',k) hm
  have heq : Coordinate.sub (coordinate u') (coordinate v') = unitCoordinate k := of_decide_eq_true hc
  rw [point, point, ← Coordinate.eval_sub, heq]
  exact unitCoordinate_norm k
end Minkowski14.Geometry{i:03d}
'''
 (out/f'Chunk{i:03d}.lean').write_text(source)
summary={'vertices':len(verts),'edges':sum(map(len,chunks)),'unique_directions':len(ws),'parameters':params}
(root/'geometry-generation.json').write_text(json.dumps(summary,indent=2))
print(summary,flush=True)
