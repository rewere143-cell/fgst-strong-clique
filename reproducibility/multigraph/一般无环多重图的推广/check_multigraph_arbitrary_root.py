"""Exact scalar checks for the general multigraph change-of-root bound."""

import argparse
from fractions import Fraction as F
import json

SLOPE = F(32, 5)
OFFSET = F(26, 5)
INTERIOR = F(19, 20)
ROOT_DERIVATIVE = F(49, 125)


def certify(beta,epsilon,target):
    # On p<=19/20, look for a point violating the desired rootwise
    # estimate 1-r-p <= SLOPE*r+OFFSET*EPSILON. The admissible bound
    # for r increases both scalar upper estimates, so test at equality.
    initial = ((F(0),INTERIOR),(F(0),F(1)),(F(0),F(1)))
    boxes = [(initial,0)]
    divisions = deepest = 0
    while boxes:
        box, depth = boxes.pop()
        deepest = max(deepest,depth)
        (p0,p1), (q0,q1), (b0,b1) = box
        if q0 > b1:
            continue
        r = (1-p0-OFFSET*epsilon)/(1+SLOPE)
        if r < 0:
            continue
        first = 1+r+p1*q1-(1-p1)*max(0,b0-q1)
        side_one = min(beta*(2-q0)**2,p1*b1+r)
        side_two = beta*(2-p0)**2
        if first <= target or first+side_one+side_two <= 2*target:
            continue
        if depth > 55:
            raise AssertionError((box,first,(first+side_one+side_two)/2))
        index = max(range(3),key=lambda i:box[i][1]-box[i][0])
        low,high = box[index]
        middle = (low+high)/2
        for interval in ((low,middle),(middle,high)):
            boxes.append((box[:index]+(interval,)+box[index+1:],depth+1))
        divisions += 1
    return divisions,deepest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--beta',type=F,default=F(2989,10000))
    parser.add_argument('--epsilon',type=F,default=F(11,10000))
    args = parser.parse_args()
    beta,epsilon = args.beta,args.epsilon
    target = 1+beta-epsilon
    assert 0 < beta <= F(2989,10000) and epsilon>0
    assert target > F(51, 40)
    assert F(17,20) - 2*beta*(2-F(17,20)) >= F(4,25)
    loss = 2*epsilon/F(4,25)
    denominator = 1-2*beta-(1+2*beta)*loss
    assert denominator>0
    loss = 2*epsilon/denominator
    assert 1-2*beta-(1+2*beta)*loss > ROOT_DERIVATIVE
    assert INTERIOR >= 3*beta
    pointwise = 1-2*beta-beta*(1-INTERIOR)
    assert 1/pointwise-1 <= SLOPE
    assert 2/pointwise <= OFFSET
    assert (2*SLOPE/ROOT_DERIVATIVE+2*OFFSET)*epsilon < target-F(5,4)
    divisions,depth = certify(beta,epsilon,target)
    print(json.dumps({"beta":str(beta),"epsilon":str(epsilon),"target":str(target),"divisions":divisions,
                      "max_depth":depth,"unresolved":0},indent=2))


if __name__ == "__main__":
    main()
