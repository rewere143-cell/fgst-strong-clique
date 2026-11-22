#!/usr/bin/env python3
"""True full PSD solve of the independently audited marked-root order-six model.
Uses the preinstalled CasADi-bundled SuperSCS; outputs are numerical only.
"""
import json,time,sys
from pathlib import Path
import numpy as np
from scipy.sparse import csr_matrix,vstack,eye,diags
from rooted_order6 import build,BASE
sys.path.insert(0,str(BASE/'solver'))
from native_scs import solve,diagnostics,svec

def main(seconds=600,eps=1e-6,prefix='native_sdp_01',warm_path=None):
 t=time.time();p=build(gram=True);N=len(p['variables']);neq=len(p['rhs']);mats=[p['A'],-eye(N,format='csr')];bs=[p['rhs'],np.zeros(N)];orders=[]
 for typ,m,K,D in p['blocks']:
  idx=np.array([i*m+j for j in range(m)for i in range(j,m)]);scales=np.array([1 if i==j else np.sqrt(2)for j in range(m)for i in range(j,m)])
  mats.append(-diags(scales)@D[idx]);bs.append(svec(K));orders.append(m)
 A=vstack(mats,format='csc');b=np.concatenate(bs);c=-p['obj'];cone={'f':neq,'l':N,'s':orders}
 print('native dimensions',A.shape,'nonzeros',A.nnz,'build seconds',time.time()-t,flush=True)
 # Warm start from a genuine outer-approximation LP primal/dual pair.
 srcpath=BASE/'refinement_best.json'if(BASE/'refinement_best.json').exists()else BASE/'certified_numeric_snapshot.json'
 src=json.loads(srcpath.read_text());x=np.load(BASE/('refinement_best_primal.npz'if'refinement'in srcpath.name else 'certified_numeric_primal.npz'))['x'];lam=np.array([-src['degree_duals'].get(n,0)for n in p['names']]);Qs=[np.zeros((m,m))for typ,m,K,D in p['blocks']]
 for cut,z in zip(src['cuts'][:src['used_cuts']],src['cut_duals']):
  if z>=0:continue
  v=np.array(cut['vector']);Qs[cut['block']]+=-z*np.outer(v,v)
 resid=p['A'].T@lam-p['obj']
 for Q,(typ,m,K,D)in zip(Qs,p['blocks']):resid-=Q.reshape(-1)@D
 y=np.concatenate([lam,resid]+[svec(Q)for Q in Qs]);warm={'x':x,'y':y,'s':b-A@x}
 if warm_path is not None:
  prior=np.load(BASE/warm_path);warm={key:prior[key]for key in['x','y','s']}
 print('warm primal objective',float(p['obj']@x),'dual upper',float(b@y),'stationarity',float(np.abs(A.T@y+c).max()),flush=True)
 r=solve(A,b,c,cone,eps=eps,max_seconds=seconds,max_iters=100000,verbose=True,memory=8,warm_start=warm)
 diag=diagnostics(A,b,c,cone,r);result={'info':r['info'],'diagnostics':diag,'total_seconds':time.time()-t,'cone':cone,'matrix_shape':A.shape,'matrix_nonzeros':A.nnz,'numerical_only':True}
 np.savez_compressed(BASE/f'{prefix}.npz',x=r['x'],y=r['y'],s=r['s']);(BASE/f'{prefix}.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main(float(sys.argv[1])if len(sys.argv)>1 else 600,float(sys.argv[2])if len(sys.argv)>2 else 1e-6,sys.argv[3]if len(sys.argv)>3 else 'native_sdp_01',sys.argv[4]if len(sys.argv)>4 else None)
