#!/usr/bin/env python3
"""A small marked-edge rooted flag LP; numerical exploration, exact data."""
import itertools as it, json, sys
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

def pairs(n): return list(it.combinations(range(n),2))
def matrix(c,n):
 a=np.zeros((n,n),dtype=int)
 for (u,v),x in zip(pairs(n),c):a[u,v]=a[v,u]=x
 return a

def valid(a):
 n=len(a)
 # Every two disjoint marked edges must have a host cross-edge.
 for u,v in pairs(n):
  if a[u,v]!=2:continue
  for x,y in pairs(n):
   if a[x,y]!=2 or len({u,v,x,y})<4:continue
   if not any(a[i,j]>0 for i in (u,v) for j in (x,y)):return False
 # Connectedness to the marked root gives uniform degree-locality.
 seen={0,1}
 while True:
  more=seen|{v for u in seen for v in range(n) if a[u,v]>0}
  if more==seen:break
  seen=more
 return len(seen)==n

def generate(n):
 return [c for tail in it.product(range(3),repeat=n*(n-1)//2-1)
         if valid(matrix(c:=(2,)+tail,n))]

def encode(a,perm):return tuple(int(a[u,v]) for u,v in pairs(len(perm)) for u,v in [(perm[u],perm[v])])

def build():
 fs={n:generate(n) for n in [3,4]}
 variables=[(n,c) for n in [3,4] for c in fs[n]]
 index={v:i for i,v in enumerate(variables)};N=len(index)
 eq=[];eq_names=[]; ub=[];rhs=[];names=[]
 def equality(row,name):
  if any(row):eq.append(row);eq_names.append(name)
 def inequal(row,r,name):ub.append(row);rhs.append(r);names.append(name)
 # Root reorientation, unlabeled permutations, and re-rooting to any marked edge.
 seen=set()
 for n,c in variables:
  a=matrix(c,n)
  for perm in it.permutations(range(n)):
   if a[perm[0],perm[1]]!=2:continue
   c2=encode(a,perm);i=index[n,c];j=index[n,c2]
   key=tuple(sorted((i,j)))
   if i!=j and key not in seen:
    seen.add(key);r=np.zeros(N);r[i]=1;r[j]=-1;equality(r,f'reroot_{n}_{i}_{j}')
 # Degree constraints on root labels.
 for u in [0,1]:
  r=np.zeros(N)
  for c in fs[3]:
   if matrix(c,3)[u,2]>0:r[index[3,c]]=1
  inequal(r,1,f'root_degree_{u}')
 # Multiply each root-connected 3-flag by degree bound on any of its vertices.
 for c in fs[3]:
  for u in range(3):
   r=np.zeros(N);r[index[3,c]]=-1
   for d in fs[4]:
    a=matrix(d,4)
    if encode(a,[0,1,2])==c and a[u,3]>0:r[index[4,d]]=1
   inequal(r,0,f'extension_{c}_{u}')
 obj=np.zeros(N)
 for c in fs[4]:
  if matrix(c,4)[2,3]==2:obj[index[4,c]]=0.5
 return dict(fs=fs,variables=variables,index=index,N=N,Aeq=np.array(eq),beq=np.zeros(len(eq)),Aub=np.array(ub),bub=np.array(rhs),names=names,eq_names=eq_names,obj=obj)

def gram_data(p):
 # [1, x_F for rooted order-3 types], averaged over roots.
 fl=p['fs'][3];m=1+len(fl);C=np.zeros((m,m,p['N']));K=np.zeros((m,m));K[0,0]=1
 for i,c in enumerate(fl,1):C[0,i,p['index'][3,c]]=C[i,0,p['index'][3,c]]=1
 for i,c in enumerate(fl,1):
  for j,d in enumerate(fl,1):
   for h in p['fs'][4]:
    a=matrix(h,4)
    if encode(a,[0,1,2])==c and encode(a,[0,1,3])==d:C[i,j,p['index'][4,h]]=1
 return K,C

def solve(psd=False,rounds=100):
 p=build();A=list(p['Aub']);b=list(p['bub']);cuts=[];K,C=gram_data(p)
 for step in range(rounds if psd else 1):
  r=linprog(-p['obj'],A_ub=np.array(A),b_ub=np.array(b),A_eq=p['Aeq'],b_eq=p['beq'],bounds=(0,None),method='highs')
  if not r.success:raise RuntimeError(r.message)
  M=K+np.einsum('ijk,k->ij',C,r.x);w,V=np.linalg.eigh(M)
  print(f'step={step} objective={-r.fun:.12g} min_eig={min(w):.3g}',flush=True)
  if not psd or min(w)>=-1e-8:break
  for j in np.flatnonzero(w < -1e-8):
   v=V[:,j];coef=np.einsum('i,j,ijk->k',v,v,C);const=v@K@v
   A.append(-coef);b.append(const);cuts.append(v.tolist())
 out={'variables':len(p['variables']),'order3_flags':len(p['fs'][3]),'order4_flags':len(p['fs'][4]),'objective':-r.fun,'gram_min_eigenvalue':min(w),'status':r.message,'psd_cut_count':len(cuts),'iterations':step+1,'nonzero_primal':[{ 'order':n,'colors':list(c),'value':r.x[i]} for i,(n,c) in enumerate(p['variables']) if r.x[i]>1e-9], 'degree_duals':dict(zip(p['names'],r.ineqlin.marginals[:len(p['names'])])), 'psd_cuts':cuts}
 path=Path(__file__).with_name('order4_psd_result.json' if psd else 'order4_lp_result.json');path.write_text(json.dumps(out,indent=2)+'\n')
 return p,r,out
if __name__=='__main__':solve('--psd' in sys.argv,300)
