"""Small integer tests for q=12, p=5 in the D9 parallel-mark reduction."""

from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations, product

from d9_parallel_counts import local_ore_rows


@cache
def splits(total, count, minimum=0, maximum=9):
    if count == 0:
        return ((),) if total == 0 else ()
    return tuple((first, *rest)
                 for first in range(minimum, min(total, maximum)+1)
                 for rest in splits(total-first, count-1, minimum, maximum))


def residual_rows(t, columns, unmarked, available, degree):
    """Pack marked residual column degrees, allowing at most one unmarked edge."""
    options = []
    for weights in product(*(range(min(3, count)+1) for count in columns)):
        marks = frozenset(i for i, w in enumerate(weights) if w)
        if not marks:
            continue
        minimum = min(t[i] for i in marks)
        if sum(weights)>minimum:
            continue
        slots = 9-degree+minimum-sum(weights)
        for extra in (-1, *range(len(columns))):
            if extra >= 0 and (not unmarked or extra in marks or not slots):
                continue
            outside = marks if extra < 0 else marks | {extra}
            options.append((weights, marks, outside, extra >= 0,
                            slots-(extra >= 0), degree-min(t[i] for i in marks)))

    def place(rem, previous, first, used, charged):
        if not any(rem):
            return True
        for index in range(first, len(options)):
            weights, marks, host, extra, room, cost = options[index]
            if used+extra > unmarked or charged+cost > available:
                continue
            if any(x>y for x,y in zip(weights, rem)):
                continue
            witnesses = [j for j,(old,_) in enumerate(previous)
                         if marks-options[old][2] and options[old][1]-host]
            if len(witnesses)>room or any(previous[j][1]>=options[previous[j][0]][4]
                                          for j in witnesses):
                continue
            after = tuple((old, count+(j in witnesses))
                          for j,(old,count) in enumerate(previous))
            after += ((index,len(witnesses)),)
            if place(tuple(y-x for x,y in zip(weights, rem)), after, index,
                     used+extra, charged+cost):
                return True
        return False

    return place(columns, (), 0, 0, 0)


def check_maximum_nine():
    states = local_ore_rows(80, 8, 9)
    if {row[0:3] for row in states} != {(1,9,9)}:
        raise ValueError(states)
    if (max(row[4] for row in states) != 15
            or {(row[3],row[5],row[7]) for row in states if row[4]==15}
            != {(5,6,81),(5,7,80)}):
        raise ValueError(states)
    for t in ((1,3,3), (2,2,3)):
        if residual_rows(t,(5,5,5),0,56,9):
            raise ValueError((80,t))
    for t in ((0,3,3), (1,2,3), (2,2,2)):
        if residual_rows(t,(5,5,5),1,57,9):
            raise ValueError((81,t))
    return len(states)


@cache
def witness_cost(t, columns, unmarked):
    """Lower bound on marked A' incidence of the F rows at |A'|=8."""
    infinite = Fraction(10**6)
    best = sum((Fraction(8*copies, value)-copies if value else infinite)
               for value,copies in zip(t,columns) if copies)
    if not unmarked:
        return best
    for use in range(1, unmarked+1):
        for weights in product(*(range(min(3, value)+1) for value in columns)):
            incident = [i for i,w in enumerate(weights) if w]
            if not incident:
                continue
            root_need = 8-min(t[i] for i in incident)
            local = sum(weights)
            if local+root_need>9 or local+max(0,root_need-use)>8:
                continue
            rem = tuple(y-x for x,y in zip(weights,columns))
            best = min(best, max(0,root_need-use)+witness_cost(t,rem,unmarked-use))
    return best


def cap_for_root(side, order, q, delta, m, pi, top, total):
    return min(top, 7*q)+m if side==0 else total


def active_profiles():
    states=local_ore_rows(80,8,8)
    if any(cap_for_root(*row) >=80 for row in states if row[0]==0):
        raise ValueError("A central root may fail to produce an exterior maximum root")
    if {row[1:3] for row in states if row[0]==1} != {(9,7),(9,8)}:
        raise ValueError("Unlisted exterior root shape")
    if {(delta,f,pi,top,total) for side,_,a,delta,f,pi,top,total in states
            if side==1 and a==7} != {(6,24,8,48,80),(7,22,6,50,80)}:
        raise ValueError("Unlisted exterior root state at seven neighbors")
    for k in (2,3):
        budget=5+k
        for r in range(12,19-2*k):
            for marks in range(80,84):
                internal=103-k-r-marks
                slack=budget-internal
                if min(slack,internal)<0:
                    continue
                for _,_,a,delta,f,pi,top,total in (
                    row for row in states if row[0]==1 and row[2]==8):
                    if top+7+f<marks or pi>budget:
                        continue
                    for c_in_a in (False,True):
                        if c_in_a and not slack:
                            continue
                        for contribution in range(max(0,marks-f-top),8):
                            yield k,r,marks,internal,slack,delta,f,pi,c_in_a,contribution


def remain_profiles(internal,slack,r,m,f,delta,pi,c_in_a,contribution):
    # C is the host neighbor of the exterior maximum root beyond its marks.
    # Four residual A columns, or three if one of the four is C.
    width=3 if c_in_a else 4
    cross=m-f-contribution
    for nonmarks in range(slack//2+1):
        inside_host=internal+nonmarks
        outside_cost=slack-2*nonmarks-int(c_in_a)
        if outside_cost<0:
            continue
        for bad in range(outside_cost+1):
            t_total=pi-bad
            if not 0<=t_total<=inside_host:
                continue
            for wrong_edges in ((),*(((a,b),) for a,b in combinations(range(width),2)
                                     if nonmarks and t_total<inside_host)):
                wrong=tuple(sum(i in edge for edge in wrong_edges) for i in range(width))
                extra_max=min(7-contribution,inside_host-t_total-len(wrong_edges))
                extra_host=(tuple(row for amount in range(extra_max+1)
                                  for row in splits(amount,width,0,3))
                            if c_in_a else ((0,)*width,))
                for t in splits(t_total,width):
                    if any(t[i]>t[i+1] for i in range(width-1)):
                        continue
                    for root_cost in (cost for total in range(width,r-12+width+1)
                                      for cost in splits(total,width,1,3)):
                        if c_in_a:
                            c_weights=(0,)*width
                        else:
                            c_weights=None
                        choices=(c_weights,) if c_weights is not None else splits(
                            contribution,width,0,3)
                        for weights in choices:
                            if sum(max(0,x-1) for x in weights)>3:
                                continue
                            for extra in extra_host:
                                previous=tuple(9-root_cost[i]-t[i]-weights[i]-wrong[i]-extra[i]
                                               for i in range(width))
                                lost=sum(previous)-f
                                if not 0<=lost<=outside_cost-bad:
                                    continue
                                for loss in splits(lost,width):
                                    columns=tuple(x-y for x,y in zip(previous,loss))
                                    if any(not 0<=value<=delta for value in columns):
                                        continue
                                    yield t,columns,bad,cross-8


def test_maximum_eight_profiles():
    retained=Counter()
    cases=set()
    for profile in set(active_profiles()):
        k,r,m,internal,slack,delta,f,pi,c_in_a,contribution=profile
        for t,columns,bad,available in set(remain_profiles(internal,slack,r,m,f,delta,
                                                          pi,c_in_a,contribution)):
            cases.add((profile,t,columns,bad,available))
            if witness_cost(t,columns,bad)<=available:
                retained[k,r,m,c_in_a,pi,contribution]+=1
                # The only remaining profiles have C in A. The unmarked
                # wC edge uses the full unmarked/defect budget.
                if not c_in_a or slack!=1 or bad:
                    raise ValueError((profile,t,columns,bad,available))
                if residual_rows(t,columns,0,available,8):
                    raise ValueError((profile,t,columns,bad,available))
    return len(cases),retained


def check_opposition_counts():
    if any(r*(7-h)<=8 and h*(5-r)<=8 and r+h<=8
           for r,h in product(range(2,6),range(9))):
        raise ValueError("a residual row may mark more than one column")
    for marks, bits in product(range(80,85), range(3,7)):
        blanks=0 if bits==3 else marks-80+(marks-80)//(bits-1)
        for w in range(12,15+blanks//bits):
            lower=14*bits*(w-7)-14*blanks
            upper=w*(w-1)+(bits-1)*(9*w-marks)
            if lower<=upper:
                raise ValueError(("opposition count",marks,bits,w))


if __name__ == "__main__":
    check_opposition_counts()
    print("Maximum-nine integer packings excluded:",check_maximum_nine(),flush=True)
    total,remaining=test_maximum_eight_profiles()
    print("Maximum-eight profiles checked:",total)
    print("Profiles retained by incidence relaxation:",sorted(remaining.items()))
