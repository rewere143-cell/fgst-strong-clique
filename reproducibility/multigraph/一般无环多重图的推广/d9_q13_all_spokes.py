"""Integer row comparison for the connected q=13 all-marked spoke core."""

from itertools import product


def compare_connected():
    for unmarked in range(1,22):
        inside=21-unmarked
        value=[0]*(unmarked+1)
        for a,b in product(range(7),range(8)):
            if not a+b:
                continue
            for u,v in product(range(7-a),range(8-b)):
                cost=u+v
                if not 1<=cost<=unmarked or a+b+cost>9:
                    continue
                if a*(7-b-v)+b*(6-a-u)>inside:
                    continue
                value[cost]=max(value[cost],min(9-cost,a+b+min(2,a+b)))
        result=[0]
        for used in range(1,unmarked+1):
            result.append(max((result[used-1],
                               *(result[used-cost]+value[cost] for cost in range(1,used+1)))))
        if result[-1]>=61:
            raise ValueError((unmarked,inside,value,result[-1]))
    return 21


if __name__ == "__main__":
    print("Connected all-marked spoke capacity cases excluded:",compare_connected())
