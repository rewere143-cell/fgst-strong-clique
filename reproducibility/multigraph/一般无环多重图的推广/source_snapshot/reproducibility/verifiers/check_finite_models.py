#!/usr/bin/env python3
"""Standalone exact finite-map moment falsification, Python standard library only.
Reads audited sparse exports and indexes; never imports a production builder.
"""
from pathlib import Path
from itertools import combinations,product
from collections import Counter,defaultdict
from array import array
from fractions import Fraction
import hashlib,json,sys,time
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'data';start=time.time()
import argparse
parser=argparse.ArgumentParser();parser.add_argument('--output',required=True);args=parser.parse_args()
if not __debug__:raise RuntimeError('Assertions must be enabled')
def binary(path,kind):
 a=array(kind);a.frombytes(path.read_bytes())
 if sys.byteorder!='little':a.byteswap()
 return a
E={n:list(combinations(range(n),2)) for n in range(2,7)}
indexes={n:binary(P/f'idx{n}.bin' if n<6 else P/'order6_orbit_index.bin','i') for n in range(3,7)}
reps={}
for n,idx in indexes.items():
 offset=728 if n==6 else 0
 for code,q in enumerate(idx):
  if q>=0:reps.setdefault(q+offset,(n,code))
assert len(reps)==23789
lines=iter((P/'basis.txt').read_text().splitlines());N,B=map(int,next(lines).split());blocks=[];offset=0
for b in range(B):
 k,t,m=map(int,next(lines).split());flags=[tuple(map(int,next(lines).split())) for _ in range(m)]
 blocks.append((k,t,m,flags,offset));offset+=m*m
GROWS=offset
keys=binary(P/'keys.bin','q');values=binary(P/'values.bin','i')
dkeys=binary(P/'degree_keys.bin','q');dvalues=binary(P/'degree_values.bin','i')
lines=iter((P/'degree.txt').read_text().splitlines());Arows=int(next(lines));degree_rows=[tuple(map(int,next(lines).split())) for _ in range(Arows)]
assert len(keys)==len(values)==1895405 and len(dkeys)==len(dvalues)==433899
# Independent twice-objective coefficients from all labeled order-four patterns.
obj2=Counter()
for c,q in enumerate(indexes[4]):
 if q>=0 and (c//3**4)%3==2:obj2[q]+=1

def check(name,H):
 begin=time.time();t=len(H);degrees=[sum(v>0 for v in row) for row in H];assert len(set(degrees))==1;d=degrees[0]
 roots=[(i,j) for i in range(t) for j in range(t) if H[i][j]==2];R=len(roots);assert R and d
 assert all(H[i][i]==0 for i in range(t))
 assert all(H[i][j]==H[j][i] for i in range(t) for j in range(t))
 marked=[(i,j) for i,j in E.get(t,list(combinations(range(t),2))) if H[i][j]==2]
 for a,b in combinations(marked,2):assert len(set(a+b))<4 or any(H[i][j]>0 for i in a for j in b)
 def code(z):
  result=0;power=1
  for i,j in E[len(z)][1:]:result+=H[z[i]][z[j]]*power;power*=3
  return result
 counts={n:Counter(code(root+tail) for root in roots for tail in product(range(t),repeat=n-2)) for n in range(3,7)}
 L=R*d**4;X=[0]*N
 for q,(n,c) in reps.items():X[q]=counts[n].get(c,0)*d**(6-n)
 assert all(0<=v<=L for v in X),(name,'coordinate bound')
 # Every alias of every orbit must have the same individual ordered map count.
 aliases_checked=0
 for n,idx in indexes.items():
  off=728 if n==6 else 0;scale=d**(6-n)
  for c,q in enumerate(idx):
   if q>=0:assert counts[n].get(c,0)*scale==X[q+off],(name,n,c,'orbit density mismatch');aliases_checked+=1
 actual_A=[0]*Arows
 for key,v in zip(dkeys,dvalues):row,q=divmod(key,N);actual_A[row]+=v*X[q]
 for i,(k,c,u) in enumerate(degree_rows):assert actual_A[i]==(L if k==2 else 0),(name,i,'degree equation')
 actual=[0]*GROWS
 for key,v in zip(keys,values):row,q=divmod(key,N);actual[row]+=v*X[q]
 for k,typ,m,flags,off in blocks:
  if k==2:actual[off]+=L
 direct=[0]*GROWS;type_maps={}
 for k in (2,3,4):
  groups=defaultdict(list)
  for root in roots:
   for tail in product(range(t),repeat=k-2):z=root+tail;groups[code(z)].append(z)
  type_maps[k]=groups
 for b,(k,typ,m,flags,off) in enumerate(blocks):
  lookup=defaultdict(dict)
  for i,(n,c) in enumerate(flags):lookup[n][c]=i
  for z in type_maps[k].get(typ,[]):
   nonzero=[]
   for n,by_code in lookup.items():
    for c,v in Counter(code(z+tail) for tail in product(range(t),repeat=n-k)).items():
     if c in by_code:nonzero.append((by_code[c],n,v))
   for i,ni,vi in nonzero:
    for j,nj,vj in nonzero:direct[off+i*m+j]+=vi*vj*d**(6-ni-nj+k)
  assert actual[off:off+m*m]==direct[off:off+m*m],(name,b,'conditional Gram mismatch')
 objective=Fraction(sum(v*X[q] for q,v in obj2.items()),2*L);expected=Fraction(R,2*d*d);assert objective==expected
 result=dict(graph=name,vertices=t,degree=d,marked_edges=R//2,q_common_denominator=L,positive_coordinates=sum(x>0 for x in X),all_orbit_alias_counts_verified=aliases_checked,degree_rows_verified=Arows,gram_blocks_verified=B,gram_entries_verified=GROWS,objective=str(objective),all_exact_checks_passed=True,seconds=time.time()-begin)
 print(json.dumps(result),flush=True);return result

def host(n,edges,marks):
 H=[[0]*n for _ in range(n)];marks={tuple(sorted(e)) for e in marks}
 for u,v in edges:H[u][v]=H[v][u]=2 if tuple(sorted((u,v))) in marks else 1
 return H
cases=[]
cases.append(('K2 marked edge',host(2,[(0,1)],[(0,1)])))
cases.append(('Triangle all marked',host(3,E[3],E[3])))
c5=[(i,(i+1)%5) for i in range(5)];cases.append(('C5 all marked',host(5,c5,c5)))
cases.append(('K4 marked matching',host(4,E[4],[(0,1),(2,3)])))
k33=[(i,j) for i in range(3) for j in range(3,6)];cases.append(('K33 marked matching',host(6,k33,[(i,i+3) for i in range(3)])))
# P4 has marked end edges and essential unmarked middle cross edge. Doubling and
# joining deficient corresponding endpoints gives a finite 2-regular C8 host.
p4=[(0,1),(1,2),(2,3)];regularized=p4+[(i+4,j+4) for i,j in p4]+[(0,4),(3,7)]
H=host(8,regularized,[(0,1),(2,3)])
assert [(i,j) for i in (0,1) for j in (2,3) if H[i][j]]==[(1,2)] and H[1][2]==1
cases.append(('Regularized P4 with essential unmarked witness',H))
results=[check(name,H) for name,H in cases]
paths=[P/x for x in ('basis.txt','degree.txt','keys.bin','values.bin','degree_keys.bin','degree_values.bin','idx3.bin','idx4.bin','idx5.bin')]+[P/'order6_orbit_index.bin']
out=dict(standard_library_only=True,production_builder_imported=False,input_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},results=results,seconds=time.time()-start)
Path(args.output).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(all_six_graphs_pass=True,seconds=out['seconds']),indent=2))
