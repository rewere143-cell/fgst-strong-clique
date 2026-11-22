#!/usr/bin/env python3
"""Root-averaged marked-graph flags through order 5, LP/PSD-cut exploration.
All coefficients before PSD cuts are integers or half-integers.
"""
import sys,itertools as it,json,time
from pathlib import Path
import numpy as np
from scipy.sparse import csr_matrix,vstack
from scipy.optimize import linprog
from rooted_order4 import pairs,matrix,valid,encode,generate

def orbits(n):
 fs=generate(n);remaining=set(fs);rep={};reps=[]
 perms=list(it.permutations(range(n)))
 while remaining:
  c=min(remaining);reps.append(c);a=matrix(c,n)
  orbit={encode(a,p) for p in perms if a[p[0],p[1]]==2}
  for d in orbit:rep[d]=c
  remaining-=orbit
 return fs,reps,rep

def build():
 data={};variables=[];lookup={}
 for n in [3,4,5]:
  fs,reps,rep=orbits(n);data[n]=(fs,reps,rep)
  for c in reps:lookup[n,c]=len(variables);variables.append((n,c))
  print(n,'raw',len(fs),'orbits',len(reps),flush=True)
 N=len(variables)
 def ix(n,c):return lookup[n,data[n][2][c]]
 rows=[];rhs=[];names=[]
 # Degree extension: sum over all induced color patterns for the new
 # vertex, provided it neighbors vertex u. No regularity assumed.
 for k in [2,3,4]:
  bases=[(2,)] if k==2 else data[k][0]
  for c in bases:
   a=matrix(c,k)
   for u in range(k):
    row={};
    if k>2:row[ix(k,c)]=-1
    for ext in it.product(range(3),repeat=k):
     if not ext[u]:continue
     aa=np.zeros((k+1,k+1),dtype=int);aa[:k,:k]=a;aa[k,:k]=aa[:k,k]=ext
     d=encode(aa,list(range(k+1)))
     if d in data[k+1][2]:row[ix(k+1,d)]=row.get(ix(k+1,d),0)+1
    rows.append(row);rhs.append(1 if k==2 else 0);names.append(f'degree_{k}_{c}_{u}')
 # Remove duplicate linear inequalities.
 unique={}
 for r,b,nam in zip(rows,rhs,names):unique[(tuple(sorted(r.items())),b)]=nam
 rows=[dict(k[0]) for k in unique];rhs=[k[1] for k in unique];names=list(unique.values())
 ri=[];ci=[];val=[]
 for i,row in enumerate(rows):
  for j,v in row.items():ri.append(i);ci.append(j);val.append(v)
 A=csr_matrix((val,(ri,ci)),shape=(len(rows),N));obj=np.zeros(N)
 for c in data[4][0]:
  if matrix(c,4)[2,3]==2:obj[ix(4,c)]+=0.5
 blocks=[]
 # Root2 Gram with unit and all rooted order3 extensions.
 for k in [2,3]:
  types=[(2,)] if k==2 else data[k][0]
  for typ in types:
   af=matrix(typ,k)
   flags=[c for c in data[k+1][0] if encode(matrix(c,k+1),list(range(k)))==typ]
   m=1+len(flags);constant=np.zeros((m,m));entries={}
   def add(i,j,q,v=1):
    key=(i*m+j,q);entries[key]=entries.get(key,0)+v
   if k==2:constant[0,0]=1
   else:add(0,0,ix(k,typ))
   for i,c in enumerate(flags,1):add(0,i,ix(k+1,c));add(i,0,ix(k+1,c))
   for i,c in enumerate(flags,1):
    aa=matrix(c,k+1)
    for j,d in enumerate(flags,1):
     bb=matrix(d,k+1)
     ab=np.zeros((k+2,k+2),dtype=int);ab[:k+1,:k+1]=aa;ab[:k,k+1]=bb[:k,k];ab[k+1,:k]=bb[k,:k]
     for edge in range(3):
      ab[k,k+1]=ab[k+1,k]=edge;h=encode(ab,list(range(k+2)))
      if h in data[k+2][2]:add(i,j,ix(k+2,h))
   rr=[];cc=[];vv=[]
   for (r,c),v in entries.items():rr.append(r);cc.append(c);vv.append(v)
   D=csr_matrix((vv,(rr,cc)),shape=(m*m,N));blocks.append((typ,m,constant,D))
 return {'variables':variables,'data':data,'ix':ix,'A':A,'rhs':np.array(rhs),'obj':obj,'names':names,'blocks':blocks}

def solve(psd=False,maxiter=500,regular=False):
 t=time.time();p=build();A=p['A'];b=p['rhs'];cuts=[];history=[]
 for step in range(maxiter if psd else 1):
  r=linprog(-p['obj'],A_ub=A[len(p['rhs']):] if regular and A.shape[0]>len(p['rhs']) else (None if regular else A),b_ub=b[len(p['rhs']):] if regular and len(b)>len(p['rhs']) else (None if regular else b),A_eq=p['A'] if regular else None,b_eq=p['rhs'] if regular else None,bounds=(0,None),method='highs')
  if not r.success:raise RuntimeError(r.message)
  mineig=0;new=[]
  for j,(typ,m,K,D) in enumerate(p['blocks']):
   M=K+(D@r.x).reshape(m,m);w,V=np.linalg.eigh(M);mineig=min(mineig,float(w.min()))
   for h in np.flatnonzero(w < -1e-8):
    v=V[:,h];outer=np.outer(v,v).reshape(-1);new.append((-(outer@D),v@K@v));cuts.append({'block':j,'vector':v.tolist()})
  history.append({'iteration':step,'objective':float(-r.fun),'min_eig':mineig,'cuts_added':len(new)})
  print(f'{step:3d} c={-r.fun:.12g} min_eig={mineig:.3g} cuts={len(new)} elapsed={time.time()-t:.1f}s',flush=True)
  if not psd or not new:break
  A=vstack([A,csr_matrix(np.array([x[0] for x in new]))],format='csr');b=np.r_[b,[x[1] for x in new]]
 out={'objective':float(-r.fun),'gram_min_eigenvalue':mineig,'status':r.message,'variables':len(p['variables']),'linear_constraints':len(p['rhs']),'gram_blocks':[{'type':list(a),'size':m} for a,m,K,D in p['blocks']], 'history':history,'nonzero_primal':[{'order':n,'colors':list(c),'value':float(r.x[i])}for i,(n,c)in enumerate(p['variables'])if r.x[i]>1e-10], 'degree_duals':dict((n,float(v)) for n,v in zip(p['names'],(r.eqlin.marginals if regular else r.ineqlin.marginals[:len(p['names'])])) if abs(v)>1e-10),'cuts':cuts}
 suffix=('regular_' if regular else '')+('psd' if psd else 'lp');Path(__file__).with_name(f'order5_{suffix}_result.json').write_text(json.dumps(out,indent=2)+'\n');np.savez(Path(__file__).with_name(f'order5_{suffix}_primal.npz'),x=r.x)
 return p,r,out
if __name__=='__main__':solve('--psd' in sys.argv,regular='--regular' in sys.argv)
