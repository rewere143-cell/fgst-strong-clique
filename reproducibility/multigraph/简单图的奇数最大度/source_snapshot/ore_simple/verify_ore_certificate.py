#!/usr/bin/env python3
"""Independent arithmetic pass for an Ore-model rational dual. No optimization.
This verifies arithmetic against the generated Ore matrices; combinatorial
validity of those matrices is a separate proof/audit obligation.
"""
import sys,json,time
from fractions import Fraction
import numpy as np
from rooted_order6 import BASE
from ore_variant import build

def main(filename='ore_exact_certificate.json',output='ore_exact_verification.json'):
 t=time.time();C=json.loads((BASE/filename).read_text())
 if C.get('extra_types') and '--extra'not in sys.argv:sys.argv.append('--extra')
 p=build(extra=C.get('extra_types',False),threshold=None if C.get('fixed_ratio')else C.get('threshold'),fixed_ratio=C.get('fixed_ratio'),localizers=C.get('localizers',False),nonlocal_localizers=C.get('nonlocal_localizers',False),independent_root=C.get('independent_root',False));
 if C.get('farkas'):p['obj']=np.zeros_like(p['obj'])
 T=int(C['common_denominator']);Q=int(C['weight_denominator']);R=int(C['vector_denominator']);assert T==Q*R*R
 W=C['degree_weights_numerators'];assert set(W)<=set(p['names']);lam=[int(W.get(n,0))for n in p['names']];assert all(v>=0 for v in lam)
 res=[-int(Fraction(str(float(v)))*T)for v in p['obj']];raw=0;A=p['A'].tocsr();assert np.array_equal(A.data,np.rint(A.data))
 for i,l in enumerate(lam):
  assert p['rhs'][i]==int(p['rhs'][i]);raw+=l*int(p['rhs'][i])
  for z in range(A.indptr[i],A.indptr[i+1]):res[int(A.indices[z])]+=l*int(A.data[z])
 gram=[[[0]*m for _ in range(m)]for typ,m,K,D in p['blocks']]
 for f in C['rank_one_factors']:
  mu=int(f['weight_numerator']);assert mu>=0;j=f['block'];v=list(map(int,f['vector_numerators']));assert len(v)==len(gram[j])
  for a,x in enumerate(v):
   for b,y in enumerate(v):gram[j][a][b]+=mu*x*y
 for M,(typ,m,K,D)in zip(gram,p['blocks']):
  DD=D.tocsr();assert np.array_equal(DD.data,np.rint(DD.data))
  for a in range(m):
   for b in range(m):
    l=M[a][b];assert K[a,b]==int(K[a,b]);raw+=l*int(K[a,b]);row=a*m+b
    for z in range(DD.indptr[row],DD.indptr[row+1]):res[int(DD.indices[z])]-=l*int(DD.data[z])
 neg={str(i):str(-v)for i,v in enumerate(res)if v<0};assert neg==C['negative_residual_numerators'];correction=sum(map(int,neg.values()));bound=Fraction(raw+correction,T);assert str(bound)==C['rational_bound'];assert Fraction(raw,T)==Fraction(C['raw_dual_value']);assert Fraction(correction,T)==Fraction(C['rounding_correction'])
 if C.get('farkas')and C.get('global_upper_bound')is not None:
  assert bound<0 and C.get('threshold')is not None
  assert Fraction(C['global_upper_bound'])==Fraction(C['threshold'])
 if C.get('fixed_ratio')and C.get('global_upper_bound')is not None:
  assert bound<(0 if C.get('farkas')else Fraction(C['fixed_ratio']))
  assert Fraction(C['global_upper_bound'])==Fraction(C['fixed_ratio'])
 global_bound=(Fraction(C['global_upper_bound'])if C.get('global_upper_bound')is not None else None)if(C.get('farkas')or C.get('fixed_ratio'))else(max(Fraction(C['threshold']),bound)if C.get('threshold')else bound)
 out={'arithmetic_verified':True,'nonnegative_inequality_multipliers_verified':True,'explicit_rank_one_PSD_factors_verified':True,'corrected_dual_constant':str(bound),'global_bound_certified':global_bound is not None,'bound':str(global_bound)if global_bound is not None else None,'bound_decimal':float(global_bound)if global_bound is not None else None,'below_620_over_1987':global_bound is not None and global_bound<Fraction(620,1987),'variables':len(res),'inequalities':len(lam),'blocks':len(gram),'seconds':time.time()-t};(BASE/output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main(*[s for s in sys.argv[1:]if not s.startswith('--')][:2])
