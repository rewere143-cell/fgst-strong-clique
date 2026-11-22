from functools import cache
from math import ceil

@cache
def max_product(D, delta, N, H, m, mark):
    if m==0: return 0
    if N==0 or m>delta*N: return -100000
    result=-100000
    for b in range(max(1,m-delta*(N-1)),min(delta,m)+1):
        for a in range(min(mark,H,D-b)+1):
            result=max(result,a*b+max_product(D,delta,N-1,H-a,m-b,mark))
    return result

@cache
def bound(l,r,sigma,D,q,parallel=2):
    if sigma<2 or min(l,r,D,q)<=0: return 0
    answer=0
    for side,(host,opp) in enumerate(((l,r),(r,l))):
      for r0 in range(D,min(host,sigma-1)+1):
       for a in range(ceil(D/parallel), min(D,q if side==1 else D)+1):
        b=min(opp,sigma-r0)
        if b*a<D: continue
        qa=q-1 if side==0 else q-a
        topA=a*min(b,D)
        C=D*(r0-D)
        answer=max(answer,topA+C)
        for delta in range(1,D+1):
         maxF=bound(l,r,sigma-a,delta,qa,parallel)
         N=q-1 if side==0 else maxF
         for m in range(delta,maxF+1):
          for p in range(a*b-D+1):
           top=min(topA,a*b-p)
           if a*m<=delta*p+max_product(D,delta,min(N,m),top-D,m,parallel*a):
            answer=max(answer,top+C+m)
            break
    return min(answer,D*q,l*q)

@cache
def local_bound(l,r,sigma,D,q,side,r0,a,parallel=2):
    """The same recurrence when a maximum-degree root is specified."""
    host,opp=((l,r),(r,l))[side]
    if not (D <= r0 <= min(host,sigma-1) and
            ceil(D/parallel) <= a <= min(D,q if side==1 else D)):
        return 0
    b=min(opp,sigma-r0)
    if b*a < D:
        return 0
    qa=q-1 if side==0 else q-a
    topA=a*min(b,D)
    C=D*(r0-D)
    answer=topA+C
    for delta in range(1,D+1):
        maxF=bound(l,r,sigma-a,delta,qa,parallel)
        N=q-1 if side==0 else maxF
        for m in range(delta,maxF+1):
            for p in range(a*b-D+1):
                top=min(topA,a*b-p)
                if a*m <= delta*p+max_product(D,delta,min(N,m),top-D,m,parallel*a):
                    answer=max(answer,top+C+m)
                    break
    return min(answer,D*q,l*q)

if __name__=='__main__':
  for q in (8,9,10):
    for sig in (11,12,13):
      print(q,sig,[bound(6,7,sig,D,q) for D in range(1,8)],flush=True)

