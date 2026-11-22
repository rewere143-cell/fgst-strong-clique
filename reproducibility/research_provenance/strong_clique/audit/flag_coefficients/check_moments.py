"""Independent integer blowup-moment tests: no orbit lookup or product routine used to compute q or target Gram."""
import sys,itertools as it,json,time
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'flags'))
from rooted_order6 import build
OUT=Path(__file__).parent
E=lambda n:list(it.combinations(range(n),2))
def mat(c,n):
 a=np.zeros((n,n),dtype=np.int8)
 for (i,j),v in zip(E(n),c):a[i,j]=a[j,i]=v
 return a
def pattern(a,t):return tuple(int(a[t[i],t[j]]) for i,j in E(len(t)))
def valid(c,n):
 a=mat(c,n)
 for z in it.combinations(range(n),4):
  for j in (1,2,3):
   x,y=z[0],z[j];u,v=[z[k] for k in (1,2,3) if k!=j]
   if a[x,y]==a[u,v]==2 and not any(a[i,k] for i in (x,y) for k in (u,v)):return False
 seen={0};old=set()
 while seen!=old:
  old=seen.copy();seen|={v for u in old for v in range(n) if a[u,v]}
 return len(seen)==n
start=time.time();p=build(True)
raw={n:[(2,)+t for t in it.product(range(3),repeat=n*(n-1)//2-1) if valid((2,)+t,n)] for n in (3,4,5)}
bases=[]
for k in (2,3):
 for typ in ([(2,)] if k==2 else raw[3]):
  bases.append((k,typ,[(k,typ)]+[(k+1,c) for c in raw[k+1] if pattern(mat(c,k+1),range(k))==typ]))
requests=[(2,(2,),[2,3,4])]+[(4,c,[4,5]) for n,c in p['variables'] if n==4]
for k,typ,sizes in requests:
 fl=[]
 for n in sizes:
  if n==k:fl.append((n,typ));continue
  seen=set()
  for c in raw[n]:
   a=mat(c,n)
   if pattern(a,range(k))!=typ:continue
   canon=min(pattern(a,tuple(range(k))+perm) for perm in it.permutations(range(k,n)))
   if canon not in seen:seen.add(canon);fl.append((n,canon))
 bases.append((k,typ,fl))
assert len(bases)==len(p['blocks'])
def check(name,H):
 t=len(H);d=int(np.count_nonzero(H[0]));assert all(np.count_nonzero(r)==d for r in H)
 roots=[(i,j) for i in range(t) for j in range(t) if H[i,j]==2];R=len(roots);L=R*d**4
 # Enumerate all template maps independently; a map is a leading-order ordered embedding in a balanced blowup.
 counts={}
 for n in (3,4,5,6):
  cnt={}
  for root in roots:
   for tail in it.product(range(t),repeat=n-2):
    c=pattern(H,root+tail);cnt[c]=cnt.get(c,0)+1
  counts[n]=cnt
 X=np.array([counts[n].get(c,0)*d**(6-n) for n,c in p['variables']],dtype=np.int64)
 assert np.array_equal(p['A'].astype(np.int64)@X,L*p['rhs'].astype(np.int64))
 comparisons=0
 for (k,typ,flags),(btyp,m,K,D) in zip(bases,p['blocks']):
  assert btyp==typ and len(flags)==m
  M=np.zeros((m,m),dtype=np.int64)
  for root in roots:
   for middle in it.product(range(t),repeat=k-2):
    z=root+middle
    if pattern(H,z)!=typ:continue
    v=[]
    for n,c in flags:
     v.append(sum(pattern(H,z+tail)==c for tail in it.product(range(t),repeat=n-k)))
    for i,(ni,_) in enumerate(flags):
     for j,(nj,_) in enumerate(flags):M[i,j]+=v[i]*v[j]*d**(6-ni-nj+k)
  actual=L*K.astype(np.int64)+(D.astype(np.int64)@X).reshape(m,m)
  assert np.array_equal(actual,M),(name,k,typ,np.max(abs(actual-M)))
  comparisons+=m*m
 objnum=int(np.rint(2*p['obj']).astype(np.int64)@X)
 assert objnum*d*d==R*L,(name,objnum,R,L)
 return dict(template=name,order=t,degree=d,ordered_marked_edges=R,common_denominator=L,degree_equations=len(p['rhs']),gram_entries=comparisons,all_exact=True)
cases=[]
H=np.zeros((5,5),dtype=np.int8)
for i in range(5):H[i,(i+1)%5]=H[(i+1)%5,i]=2
cases.append(('C5 all marked',H.copy()))
H[0,1]=H[1,0]=1;H[2,3]=H[3,2]=1;cases.append(('C5 three marked edges',H.copy()))
H=np.ones((4,4),dtype=np.int8)-np.eye(4,dtype=np.int8);H[0,1]=H[1,0]=H[2,3]=H[3,2]=2;cases.append(('K4 marked matching',H))
H=np.zeros((6,6),dtype=np.int8);H[:3,3:]=H[3:,:3]=1
for i in range(3):H[i,i+3]=H[i+3,i]=2
cases.append(('K33 marked matching',H))
results=[]
for name,H in cases:
 result=check(name,H);results.append(result);print(json.dumps(result),flush=True)
(OUT/'moment_results.json').write_text(json.dumps(dict(results=results,seconds=time.time()-start),indent=2)+'\n')
