#!/usr/bin/env python3
"""Project a native dual to the exact C5 face, then fit support equalities.
Exploratory; no certificate claim unless all residual signs are exact.
"""
import sys,json,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from sympy import Matrix
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from rooted_order6 import build,BASE
sys.path.insert(0,str(BASE/'solver'))
from native_scs import smat
from c5_face_helpers import round_kernel_factor
FACE=Path(__file__).parent

def main(prefix='native_sdp_01'):
 t=time.time();p=build(gram=True);face=json.loads((FACE/'c5_face_data.json').read_text());fx=np.load(FACE/'c5_face_data.npz');support=fx['support'];meta=json.loads((BASE/f'{prefix}.json').read_text());data=np.load(BASE/f'{prefix}.npz');y=data['y'];neq=len(p['rhs']);N=len(p['variables']);R=10**12;T=R*R;factors=[];grams=[];off=neq+N
 for j,(typ,m,K,D)in enumerate(p['blocks']):
  Q=smat(y[off:off+m*(m+1)//2],m);off+=m*(m+1)//2;ev,V=np.linalg.eigh((Q+Q.T)/2);vecs=[]
  for h in np.flatnonzero(ev>1e-14):
   v=V[:,h]*np.sqrt(ev[h]);a=round_kernel_factor(v,face['blocks'][j],R,project=True);vecs.append(a);factors.append({'block':j,'vector':a})
  E=np.array(vecs,dtype=object).reshape(-1,m);grams.append(E.T@E)
 A=p['A'].astype(np.int64);AS=Matrix(A[:,support].T.toarray().tolist());rr,pivs=AS.rref();Z=AS.T.nullspace();print('support size',len(support),'rankA',len(pivs),'left-nullity',len(Z),'pivots',pivs,flush=True)
 out={'source':prefix,'scale':R,'support':support.tolist(),'support_degree_rank':len(pivs),'support_degree_pivot_rows':list(pivs),'support_left_nullspace':[[str(z[i])for i in range(len(support))]for z in Z],'factors':factors}
 # Initial projected dual residuals are measured exactly in denominator R².
 lam=[round(Fraction(str(float(v)))*T)for v in y[:neq]];res=[-round(Fraction(str(float(v)))*T)for v in p['obj']];raw=0
 for i,l in enumerate(lam):
  raw+=l*int(p['rhs'][i])
  for z in range(A.indptr[i],A.indptr[i+1]):res[int(A.indices[z])]+=l*int(A.data[z])
 for Q,(typ,m,K,D)in zip(grams,p['blocks']):
  DD=D.tocsr()
  for a in range(m):
   for b in range(m):
    l=int(Q[a,b]);raw+=l*int(K[a,b]);row=a*m+b
    for z in range(DD.indptr[row],DD.indptr[row+1]):res[int(DD.indices[z])]-=l*int(DD.data[z])
 violations=[sum(z[i]*res[int(s)]for i,s in enumerate(support))for z in Z]
 out.update(support_residuals=[str(Fraction(res[int(s)],T))for s in support],support_consistency_violations=[str(v/T)for v in violations],raw_objective=str(Fraction(raw,T)),negative_residual_count=sum(v<0 for v in res),negative_residual_sum=str(Fraction(sum(-v for v in res if v<0),T)),seconds=time.time()-t)
 (FACE/'projected_native_dual.json').write_text(json.dumps(out,indent=2)+'\n');np.savez_compressed(FACE/'projected_native_grams.npz',**{f'Q{j}':np.array(Q,dtype=str)for j,Q in enumerate(grams)})
 print(json.dumps({k:v for k,v in out.items()if k not in['factors','support_left_nullspace','support_residuals']},indent=2),flush=True)
if __name__=='__main__':main(*sys.argv[1:2])
