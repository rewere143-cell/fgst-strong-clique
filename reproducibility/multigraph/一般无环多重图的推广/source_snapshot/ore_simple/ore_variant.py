#!/usr/bin/env python3
"""Bipartite MARKED subgraph, arbitrary host, normalized by marked Ore degree.
No regularization equality is used. Host same-side edges remain unrestricted.
"""
import itertools as it,json,time,sys
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.sparse import csr_matrix,vstack,eye,diags,load_npz
from scipy.optimize import linprog
from rooted_order6 import build as base_build,BASE,ORDER_SIX_INDEX
from rooted_order4 import pairs,matrix,encode
from rooted_order5 import orbits
sys.path.insert(0,str(BASE/'solver'))
from native_scs import solve as scs_solve,diagnostics,svec

def marked_bipartite(n,c):
 A=matrix(c,n);color=[-1]*n
 for start in range(n):
  if color[start]>=0:continue
  color[start]=0;stack=[start]
  while stack:
   u=stack.pop()
   for v in range(n):
    if A[u,v]!=2:continue
    if color[v]==color[u]:return False
    if color[v]<0:color[v]=1-color[u];stack.append(v)
 return True

def build(extra=None, threshold=None, localizers=None, fixed_ratio=None, nonlocal_localizers=None, independent_root=None):
 if independent_root is None:independent_root="--independent-root" in sys.argv
 if nonlocal_localizers is None:nonlocal_localizers="--nonlocal-localizers" in sys.argv
 if fixed_ratio is None:fixed_ratio=next((a.split("=",1)[1]for a in sys.argv if a.startswith("--fixed-ratio=")),None)
 if fixed_ratio is not None:
  assert threshold is None
  threshold=fixed_ratio
 if localizers is None:localizers="--localizers" in sys.argv
 if extra is None:extra="--extra" in sys.argv
 if threshold is None:
  threshold=next((a.split("=",1)[1]for a in sys.argv if a.startswith("--threshold=")),None)
 t=time.time();p=base_build(gram=True);keep=np.array([i for i,(n,c)in enumerate(p['variables'])if marked_bipartite(n,c)]);variables=[p['variables'][i]for i in keep];new_index={old:new for new,old in enumerate(keep)};index={v:i for i,v in enumerate(p['variables'])};sm={k:orbits(k)for k in[3,4,5]};ids6=np.fromfile(ORDER_SIX_INDEX,dtype=np.int32);offset=sum(n<6 for n,c in p['variables']);N=len(keep)
 def ix(n,c):
  if n==2:return None
  if n<6:
   rep=sm[n][2].get(c)
   if rep is None:return None
   old=index[n,rep]
  else:
   q=int(ids6[sum(v*3**j for j,v in enumerate(c[1:]))])
   if q<0:return None
   old=offset+q
  return new_index.get(old)
 rows=[];rhs=[];names=[]
 for k in[2,3,4,5]:
  bases=[(2,)]if k==2 else[c for n,c in variables if n==k]
  for c in bases:
   a=matrix(c,k);exts=[{}for _ in range(k)]
   for tail in it.product(range(3),repeat=k):
    if not any(tail):continue
    aa=np.zeros((k+1,k+1),dtype=int);aa[:k,:k]=a;aa[k,:k]=aa[:k,k]=tail;j=ix(k+1,encode(aa,list(range(k+1))))
    if j is None:continue
    for u,z in enumerate(tail):
     if z:exts[u][j]=exts[u].get(j,0)+1
   def add(row,name):
    row=dict(row)
    if k>2:row[ix(k,c)]=-1
    rows.append(row);rhs.append(1 if k==2 else 0);names.append(name)
   for u in range(k):add(exts[u],f'degree_{k}_{c}_{u}')
   for u,v in pairs(k):
    if a[u,v]!=2:continue
    row=dict(exts[u])
    for j,z in exts[v].items():row[j]=row.get(j,0)+z
    add(row,f'ore_{k}_{c}_{u}_{v}')
 uniq={}
 for r,b,n in zip(rows,rhs,names):uniq[tuple(sorted(r.items())),b]=n
 rr=[];cc=[];vv=[];names=[];rhs=[]
 for i,((row,b),n)in enumerate(uniq.items()):
  names.append(n);rhs.append(b)
  for j,v in row:rr.append(i);cc.append(j);vv.append(v)
 A=csr_matrix((vv,(rr,cc)),shape=(len(rhs),N));blocks=[]
 for oldblock,(typ,m,K,D)in enumerate(p['blocks']):
  DD=D[:,keep].tocsr();alive=[i for i in range(m)if K[i,i]or DD[i*m+i].nnz]
  if not alive:continue
  selector=[i*m+j for i in alive for j in alive];blocks.append((typ,len(alive),K[np.ix_(alive,alive)],DD[selector]))
 if extra:
  extra_index=json.loads((BASE.parent/'ore/missing_type_blocks/index.json').read_text())
  for item in extra_index['blocks']:
   DD=load_npz(BASE.parent/'ore/missing_type_blocks'/Path(item['path']).name)[:,keep].tocsr();m=item['size'];alive=[i for i in range(m)if DD[i*m+i].nnz]
   if not alive:continue
   selector=[i*m+j for i in alive for j in alive];blocks.append((('extra',item['name']),len(alive),np.zeros((len(alive),len(alive))),DD[selector]))
 if localizers:
  local_index=json.loads((BASE/'ore_localizers/index.json').read_text())
  for item in local_index['blocks']:
   DD=load_npz(BASE/'ore_localizers'/item['path'])[:,keep].tocsr();KK=np.load(BASE/'ore_localizers'/item['constant_path']);m=item['size'];alive=[i for i in range(m)if KK[i,i]or DD[i*m+i].nnz]
   if not alive:continue
   selector=[i*m+j for i in alive for j in alive];blocks.append((('localizer',item['name']),len(alive),KK[np.ix_(alive,alive)],DD[selector]))
 if nonlocal_localizers:
  local_index=json.loads((BASE/'ore_nonlocal_localizers/index.json').read_text())
  for item in local_index['blocks']:
   DD=load_npz(BASE/'ore_nonlocal_localizers'/item['path'])[:,keep].tocsr();KK=np.load(BASE/'ore_nonlocal_localizers'/item['constant_path']);m=item['size'];alive=[i for i in range(m)if KK[i,i]or DD[i*m+i].nnz]
   if not alive:continue
   selector=[i*m+j for i in alive for j in alive];blocks.append((('nonlocal_localizer',item['name']),len(alive),KK[np.ix_(alive,alive)],DD[selector]))
 if independent_root:
  assert threshold is not None,'The independent-root augmented Gram needs a positive ratio threshold.'
  a=Fraction(str(threshold));assert a>0;meta=json.loads((BASE.parent/'ore/independent_root_gram_metadata.json').read_text());E=load_npz(BASE.parent/'ore/independent_root_gram.npz')[:,keep].tocoo();s=meta['size'];m=s+1;KK=np.zeros((m,m),dtype=np.int64);KK[0,0]=2*a.numerator;rr=((E.row//s+1)*m+(E.row%s+1)).tolist();cc=E.col.tolist();vv=(a.denominator*E.data).tolist()
  for i,(_,_,old)in enumerate(meta['basis'],1):
   if old<0:KK[0,i]=KK[i,0]=2*a.numerator
   elif old in new_index:
    rr.extend([i,i*m]);cc.extend([new_index[old]]*2);vv.extend([2*a.numerator]*2)
  DD=csr_matrix((vv,(rr,cc)),shape=(m*m,N));alive=[i for i in range(m)if KK[i,i]or DD[i*m+i].nnz];selector=[i*m+j for i in alive for j in alive];blocks.append((('independent_root',str(a)),len(alive),KK[np.ix_(alive,alive)],DD[selector]))
 if threshold is not None:
  a=Fraction(str(threshold));z=np.load(BASE/'uniformity_matrices.npz');U=csr_matrix((z['U_data'],z['U_indices'],z['U_indptr']),shape=tuple(z['U_shape']))[:,keep];V=csr_matrix((z['V_data'],z['V_indices'],z['V_indptr']),shape=tuple(z['V_shape']))[:,keep]
  UU=(2*a.numerator*V-2*a.denominator*U).tocsr();bb=np.zeros(UU.shape[0],dtype=int);bb[0]=-2*a.numerator;assert np.array_equal(UU.data,np.rint(UU.data));active=[i for i in range(UU.shape[0])if UU[i].nnz or bb[i]]
  A=vstack([A,UU[active]],format='csr');rhs=list(rhs)+bb[active].tolist();names+=['uniform_lower_'+str(i)+'_'+str(a)for i in active]
  if fixed_ratio is not None:
   A=vstack([A,-UU[active]],format='csr');rhs=list(rhs)+(-bb[active]).tolist();names+=['uniform_upper_'+str(i)+'_'+str(a)for i in active]
 out={'variables':variables,'original_columns':keep,'A':A,'rhs':np.array(rhs),'names':names,'obj':p['obj'][keep],'blocks':blocks,'threshold':str(Fraction(str(threshold)))if threshold is not None else None,'extra_types':bool(extra),'localizers':bool(localizers),'nonlocal_localizers':bool(nonlocal_localizers),'independent_root':bool(independent_root),'fixed_ratio':str(Fraction(str(fixed_ratio)))if fixed_ratio is not None else None};print('ORE model',N,'variables',len(rhs),'inequalities',len(blocks),'PSD blocks','seconds',time.time()-t,flush=True);return out

def lp():
 p=build();r=linprog(-p['obj'],A_ub=p['A'],b_ub=p['rhs'],bounds=(0,None),method='highs-ipm',options={'time_limit':300});print('ORE LP',r.message, -r.fun if r.success else None,flush=True)
 out={'status':r.message,'success':r.success,'numerical_only':True}
 if r.success:
  out['objective']=-r.fun;np.savez_compressed(BASE/'ore_lp.npz',x=r.x,dual=r.ineqlin.marginals)
 (BASE/'ore_lp.json').write_text(json.dumps(out,indent=2)+'\n')

def native(seconds=600,eps=1e-6):
 t=time.time();p=build();N=len(p['variables']);ng=len(p['rhs']);mats=[p['A'],-eye(N,format='csr')];bs=[p['rhs'],np.zeros(N)];orders=[]
 for typ,m,K,D in p['blocks']:
  idx=[i*m+j for j in range(m)for i in range(j,m)];sc=[1 if i==j else np.sqrt(2)for j in range(m)for i in range(j,m)];mats.append(-diags(sc)@D[idx]);bs.append(svec(K));orders.append(m)
 A=vstack(mats,format='csc');b=np.concatenate(bs);zero_objective='--zero-objective'in sys.argv;c=np.zeros(N)if zero_objective else -p['obj'];cone={'f':0,'l':ng+N,'s':orders};print('ORE native',A.shape,A.nnz,flush=True)
 warm=None
 prefix=next((a.split('=',1)[1]for a in sys.argv if a.startswith('--output-prefix=')),'ore_native')
 warm_prefix=next((a.split('=',1)[1]for a in sys.argv if a.startswith('--warm-prefix=')),'ore_native')
 if (BASE/f'{warm_prefix}.npz').exists() and '--fresh-k2' not in sys.argv:
  old=np.load(BASE/f'{warm_prefix}.npz');ox=old['x'];oy=old['y'];oldmeta=json.loads((BASE/f'{warm_prefix}.json').read_text());oldng=oldmeta.get('cone',{}).get('l',3120+N)-N
  assert oldng<=ng and len(ox)==N
  yy=np.r_[oy[:oldng],np.zeros(ng-oldng),oy[oldng:]];assert len(yy)<=A.shape[0]
  warm={'x':ox,'y':np.r_[yy,np.zeros(A.shape[0]-len(yy))],'s':b-A@ox}
 if '--fresh-k2' in sys.argv:
  x=np.zeros(N)
  for j,(n,col) in enumerate(p['variables']):
   if 1 in col:continue
   H=matrix(col,n);side=[int(H[0,v]==0) for v in range(n)]
   if all(bool(H[u,v])==(side[u]!=side[v])for u,v in pairs(n)):x[j]=2.0**(-(n-2))
  assert abs(p['obj']@x-.25)<1e-12
  assert np.max(p['A']@x-p['rhs'])<1e-12
  warm={'x':x,'y':np.zeros(A.shape[0]),'s':b-A@x}
  print('exact K2 warm start objective',p['obj']@x,flush=True)
 r=scs_solve(A,b,c,cone,max_seconds=seconds,eps=eps,max_iters=200000,verbose=True,memory=8,warm_start=warm,super_scs='--plain'not in sys.argv);di=diagnostics(A,b,c,cone,r);out={'info':r['info'],'native_objective':'zero'if zero_objective else 'clique','diagnostics':di,'seconds':time.time()-t,'numerical_only':True,'threshold':p['threshold'],'extra_types':p['extra_types'],'localizers':p['localizers'],'nonlocal_localizers':p['nonlocal_localizers'],'independent_root':p['independent_root'],'fixed_ratio':p['fixed_ratio'],'cone':cone};np.savez_compressed(BASE/f'{prefix}.npz',x=r['x'],y=r['y'],s=r['s']);(BASE/f'{prefix}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':
 if '--lp'in sys.argv:lp()
 else:native(float(sys.argv[1])if len(sys.argv)>1 else 600,float(sys.argv[2])if len(sys.argv)>2 else 1e-6)
