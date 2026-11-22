"""Exact two-root Ore bounds for a D9 graph after deleting a repeated pair."""

from functools import cache
from itertools import product

from d7_bipartite_ore_coupled import bound


@cache
def bipartite_cap(side_size, sigma, max_marked_degree):
    if not side_size or sigma<=1:
        return 0
    table=max(bound(8,9,sigma,d,side_size,2)
              for d in range(1,min(max_marked_degree,sigma-1)+1))
    return min(table,2989*sigma*sigma//10000)


def root_states(threshold=91):
    sigma=17
    for r,t,a,b in product(range(1,10),repeat=4):
        if not (r+t<=sigma and a<=r and b<=t and b<=a):
            continue
        for p,s,w in product(range(max(1,a-2),a+1),range(max(1,b-2),b+1),(1,2)):
            if not (w<=b and w-1<=a-p and w-1<=b-s):
                continue
            value=a*(r+t-a-b+s)+p*b
            single=value+w-b-a
            coarse=2989*(sigma-s)**2//10000+2989*(sigma-p)**2//10000
            if min(single,(value+coarse)//2)<threshold:
                continue
            m1=bipartite_cap(r-(a-p)-1,sigma-s,a)
            m2=bipartite_cap(t-(b-s)-1,sigma-p,a)
            upper=min(single,(value+m1+m2)//2)
            if upper>=threshold:
                yield r,t,a,b,p,s,w,m1,m2,value,upper


if __name__ == "__main__":
    exact=tuple(root_states())
    expected=((9,8,9,8,9,8,1,22,18,144,92),)
    if exact!=expected:
        raise ValueError(exact)
    print("Remaining Ore-17 root states above 90 marks:",exact)
