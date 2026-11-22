#!/usr/bin/env python3
"""Verify saved rational PSD certificate without any numerical optimization."""
from fractions import Fraction
from pathlib import Path
import json,time,sys
import numpy as np
from rooted_order6 import build,BASE

def verify(filename="order6_exact_psd_certificate.json", output="order6_certificate_verification.json"):
 t=time.time();C=json.loads((BASE/filename).read_text());p=build(gram=True)
 T=int(C['common_denominator']);Q=int(C['weight_denominator']);R=int(C['vector_denominator']);assert T==Q*R*R
 lambdas=C['degree_weights_numerators'];assert set(lambdas)<=set(p['names']);lam=[int(lambdas.get(n,0))for n in p['names']]
 A=p['A'].tocsr();assert np.array_equal(A.data,np.rint(A.data));res=[-int(Fraction(str(float(v)))*T)for v in p['obj']];raw=0
 for i,l in enumerate(lam):
  assert p['rhs'][i]==int(p['rhs'][i]);raw+=l*int(p['rhs'][i])
  for z in range(A.indptr[i],A.indptr[i+1]):res[int(A.indices[z])]+=l*int(A.data[z])
 gram=[[[0]*m for _ in range(m)]for typ,m,K,D in p['blocks']]
 for f in C['rank_one_factors']:
  mu=int(f['weight_numerator']);assert mu>=0;j=f['block'];v=list(map(int,f['vector_numerators']));assert len(v)==len(gram[j])
  for a,x in enumerate(v):
   for b,y in enumerate(v):gram[j][a][b]+=mu*x*y
 for j,(typ,m,K,D)in enumerate(p['blocks']):
  DD=D.tocsr();assert np.array_equal(DD.data,np.rint(DD.data))
  for a in range(m):
   for b in range(m):
    l=gram[j][a][b];assert K[a,b]==int(K[a,b]);raw+=l*int(K[a,b]);row=a*m+b
    for z in range(DD.indptr[row],DD.indptr[row+1]):res[int(DD.indices[z])]-=l*int(DD.data[z])
 neg={str(i):str(-v)for i,v in enumerate(res)if v<0};assert neg==C['negative_residual_numerators'];correction=sum(map(int,neg.values()));bound=Fraction(raw+correction,T)
 assert bound==Fraction(C['rational_bound']);assert Fraction(raw,T)==Fraction(C['raw_dual_value']);assert Fraction(correction,T)==Fraction(C['rounding_correction'])
 result={'arithmetic_verified':True,'explicit_rank_one_PSD_factors_verified':True,'bound':str(bound),'bound_decimal':float(bound),'below_2607_over_1987':bound<Fraction(2607,1987),'seconds':time.time()-t}
 (BASE/output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));return result
if __name__=='__main__':verify(*sys.argv[1:3])
