"""Verify the exact rational constants in the multigraph pentagon argument."""

from fractions import Fraction as F
from itertools import combinations, product
from math import ceil, floor, isqrt

ABUNDANCE = F('.99999')
ANCHOR = F('.56425')
REFINED_ANCHOR = F('.56820')
EPS_ABUNDANCE = F(2,10**9)
EPS_ANCHOR = F(1,10**9)
GRID = 10**10
OVERLAP = F(3,7)
JOINT_OVERLAP = F(5,12)


def anchor_ratio(delta, anchor=ANCHOR):
    density = F(1,8)-(delta+EPS_ABUNDANCE)/ABUNDANCE
    assert density>0
    return (delta+EPS_ANCHOR)/(anchor*density)


def verify(delta,rho,mu,threshold,holes,cover,coarse):
    assert anchor_ratio(delta)<rho
    size = (1-rho)/2
    cap = rho/2
    # Round each iterated upper bound upward to a grid of mesh 1e-8.
    missing = mu+rho
    for _ in range(8):
        covered = F(3,2)-cap-missing/size
        assert covered>1
        m = mu+cap*(2-covered)/covered
        scaled = m*10**8
        missing = F(-(-scaled.numerator//scaled.denominator),10**8)
    assert missing < holes
    assert F(3,2)-cap-holes/size >= cover
    assert (size-threshold)**2 > holes and 3*threshold>1
    wrong = 1-2*threshold
    assert cap < size-wrong
    assert cover-1 >= threshold
    eta = 1-2*(threshold-rho)
    assert eta*(cover-1+eta) <= cover*(2-cover)/2
    kappa = F(1,2)-eta/cover
    assert kappa>0
    if coarse:
        assert 2*(threshold-wrong) >= rho
    else:
        assert cap/(size-wrong) <= F(1,12)
        assert cap/(threshold-wrong-rho) <= F(1,12)
        assert kappa>F(1,3)
    return kappa


def grid_up(x):
    return F(ceil(x*GRID), GRID)


def grid_down(x):
    return F(floor(x*GRID), GRID)


def root_up(x):
    scaled = x*GRID**2
    k = isqrt(floor(scaled))
    return F(k+(k*k<scaled), GRID)


def root_down(x):
    return F(isqrt(floor(x*GRID**2)),GRID)


ANCHOR_COSTS = [
    (a,(1+root_down(1+3*a))**2,(1+root_down(1+4*a))**2)
    for a in [*(F(j,8) for j in range(9)),F(3,2),F(2),F(3),F(5),F(8),F(16)]
]


def outside_rates(cover, rho):
    spare_three, spare_four = (1+rho)/2, 2-cover
    assert 0<spare_three<=spare_four<2
    rates = [(F(0),max(spare_three/3,spare_four/4))]
    for a, cost_three, cost_four in ANCHOR_COSTS:
        cost = min(cost_three/spare_three,cost_four/spare_four)-2
        rates.append((1/cost,a/cost))
    return rates


def old_core(delta, mu, imposed, anchor=ANCHOR):
    rho = grid_up(anchor_ratio(delta, anchor))
    return old_core_for_anchor(rho, mu, imposed)


def old_core_for_anchor(rho, mu, imposed, *, enhanced=False, parallel=F(0)):
    size = (1-rho)/2
    reserve = rho-parallel
    assert reserve>=0
    missing = min(imposed, mu+reserve/3)
    for _ in range(16):
        cover = F(3,2)-rho/2-missing/size
        assert cover>(0 if enhanced else 1)
        upper = (rho/4)*(2-cover)/cover
        if enhanced:
            upper = min(upper,*(a*rho/2+b*reserve for a,b in outside_rates(cover,rho)))
        missing = min(missing, grid_up(mu+upper))
    cover = grid_down(F(3,2)-rho/2-missing/size)
    assert 1<cover<2
    return rho, size, missing, cover


def three_split_fee(rho, close, split):
    bound = F(0)
    intervals = 256
    for j in range(intervals):
        lo = rho*j/(3*intervals)
        hi = rho*(j+1)/(3*intervals)
        at = min(hi, max(lo, rho/4))
        new_new = min((rho-lo)**2/16, rho*at/2-at**2)
        bound = max(bound, hi/(close-rho+hi/5)+new_new/split)
    return bound


def wider_step(old, mu, mode):
    rho, size, missing, cover = old
    close = grid_down(size-root_up(missing))-F(1, GRID)
    if close<=rho:
        return None
    assert close<size and (size-close)**2>missing
    incorrect = 1-2*close
    gap = size-incorrect
    fee = (rho/3)/(close-rho+rho/15)
    if mode=="all":
        if gap<=0:
            return None
        fee = max(rho/(3*(close-rho)), rho/(4*gap))
    if fee>=1:
        return None
    factor = F(1)
    low_close = grid_up((2+rho)/6 if mode=="all" else F(1,4)+rho/2)
    if close<low_close:
        split = grid_down((size-low_close)**2)-F(1, GRID)
        if low_close>=size or split<=0:
            return None
        assert (size-low_close)**2>split
        if missing>split:
            high_fee = (fee+rho**2/(20*split) if mode=="all"
                        else three_split_fee(rho,close,split))
            factor = max(F(1), grid_up(high_fee)+F(1, GRID))

    def kappa(theta):
        if mode=="all":
            unmarked = min(close-theta,cover-1)
            assert unmarked>0
            base = F(1,2)-(1-2*unmarked)/cover
            surcharge = F(0)
        else:
            unmarked = min(close,cover-1)
            base = F(1,2)-(1-2*unmarked)/cover
            surcharge = max(0, unmarked-size+theta, 2*theta/3, unmarked/2)
            if gap<0:
                center = cover/2
                tangent = (F(1,2)-unmarked)/(center*(1-center))
                margin = min(unmarked-base,tangent*max(0,2*close+size-center)**2)
                assert 0<=margin<=unmarked
                surcharge = max(surcharge,2*(unmarked-margin)/3)
        slack_fee = grid_down(base-surcharge)
        missing_fee = grid_down(1-(1-2*base)*factor)
        support_fee = min(slack_fee,grid_down(missing_fee/(1+factor)))
        return support_fee, slack_fee, missing_fee

    value, slack_fee, missing_fee = kappa(rho)
    if value<=0:
        return None
    for _ in range(12):
        theta = min(rho, (rho+min(rho,2*mu/slack_fee))/2)
        updated = kappa(theta)
        if updated==(value,slack_fee,missing_fee):
            break
        assert all(x>=y for x,y in zip(updated,(value,slack_fee,missing_fee)))
        value, slack_fee, missing_fee = updated
    return value, slack_fee, missing_fee, mode, factor


def verify_wider_even(tolerance):
    old = old_core(tolerance, F(0), F(1))
    step = wider_step(old, F(0), "three")
    assert step is not None and step[0]>0
    return step[0]


def verify_wider_odd(tolerance, degree):
    mu = F(1, 2*degree)
    current = tolerance
    transitions = []
    for _ in range(12):
        imposed = F(1)
        modes = []
        for _ in range(12):
            old = old_core(current, mu, imposed)
            candidates = [s for mode in ("all", "three") if (s:=wider_step(old, mu, mode)) is not None]
            assert candidates, (current, degree, imposed)
            value, slack_fee, missing_fee, mode, factor = max(candidates, key=lambda item: item[0])
            modes.append(mode)
            if slack_fee>F(1,3) and factor==1:
                transitions.append((str(current),str(value),modes))
                return transitions
            next_imposed = grid_up(mu/missing_fee)
            if next_imposed>=imposed:
                break
            imposed = next_imposed
        transitions.append((str(current),str(value),modes))
        following = grid_up(mu/value)
        assert following<current, (tolerance, degree, transitions)
        current = following
    raise AssertionError((tolerance, degree, transitions))


def intervals(a, b, buckets):
    for i in range(buckets):
        yield a+(b-a)*i/buckets, a+(b-a)*(i+1)/buckets


def mixed_surcharge(rho, theta, unmarked, size, rich, residual_upper, lower=F(0)):
    def values(h):
        half = max((unmarked-size+h)/2,unmarked/4)
        third = max(rich,min(unmarked,h))/3
        outside = F(1,2)-max(0,h-rho/2)/residual_upper
        assert 0<=outside<=F(1,2)
        weight = max(0,6*outside-2)
        return 2*outside*half, min(1,3*outside)*third, weight*half+(1-weight)*third

    boundary = rho/2+residual_upper/6
    best = max(values(lower) if lower<=boundary else values(lower)[:2])
    points = sorted({lower,theta,*[h for h in [size-unmarked/2,unmarked,rich,rho/2,
                                              boundary] if lower<h<theta]})
    for lo, hi in zip(points, points[1:]):
        for index, (left,center,right) in enumerate(
                zip(values(lo), values((lo+hi)/2), values(hi))):
            if index==2 and (lo+hi)/2>boundary:
                continue
            quadratic = 2*(left+right-2*center)
            linear = right-left-quadratic
            maximum = max(left,right)
            if quadratic<0 and 0<linear<-2*quadratic:
                maximum = max(maximum,left-linear**2/(4*quadratic))
            best = max(best, maximum)
    return grid_up(2*best)


def linear_solve(rows):
    size = len(rows)
    matrix = [[F(x) for x in row] for row in rows]
    for col in range(size):
        pivot = next((j for j in range(col,size) if matrix[j][col]),None)
        if pivot is None:
            return None
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        leading = matrix[col][col]
        matrix[col] = [x/leading for x in matrix[col]]
        for j in range(size):
            if j!=col and (scale:=matrix[j][col]):
                matrix[j] = [a-scale*b for a,b in zip(matrix[j],matrix[col])]
    return [row[-1] for row in matrix]


def verify_overlap():
    results = []
    for signs in product((-1,1),repeat=5):
        outside = [{(i+sign)%5,(i+2*sign)%5} for i,sign in enumerate(signs)]
        gram = [[2 if i==j else int(j in outside[i])+int(i in outside[j])
                 for j in range(5)] for i in range(5)]
        results.append(quadratic_minimum(gram))
    assert min(results)==OVERLAP
    labels = [(j,sign) for j in range(5) for sign in (-1,1)]
    outside = [{(j+sign)%5,(j+2*sign)%5} for j,sign in labels]
    gram = [[2 if a==b else 1 if i==j else int(j in outside[a])+int(i in outside[b])
             for b,(j,_) in enumerate(labels)] for a,(i,_) in enumerate(labels)]
    joint = quadratic_minimum(gram)
    assert joint==JOINT_OVERLAP
    return min(results), joint


def quadratic_minimum(gram):
    best = F(1)
    for count in range(1,len(gram)+1):
        for face in combinations(range(len(gram)),count):
            rows = [[*(gram[i][j] for j in face),1,0] for i in face]
            result = linear_solve([*rows,[*[1]*count,0,1]])
            if result is not None and min(result[:-1])>=0:
                best = min(best,-result[-1]/2)
    return best


def binned_hole_choices(rho, size, close, theta, missing_lower, rem_lower, rem_upper,
                         buckets, parallel):
    count = (rho-rem_lower)/2
    heavy = min(rem_upper-parallel, count, (rho-parallel)/3)
    unpaid = max(0, rho-2*(size+2*close-1))*count/2
    slack_pair = (rho+rem_upper)/2
    if missing_lower==0:
        absolute = heavy*max(0,F(1,2)+theta/2-close)+min(count**2/4,heavy*count)
        old_charge = []
        margin = close-slack_pair
        if margin>0:
            old_charge.append(heavy/(margin+2*heavy))
        elif margin==0:
            old_charge.append(F(1,2))
        if close>theta:
            old_charge.append(heavy/(close-theta+heavy))
        multiplier = None
        if unpaid==0:
            multiplier = F(1)
        elif close>=rho:
            multiplier = F(3)
        elif margin>0 and 2*close>=rho+count:
            multiplier = 3+count/margin
        choices = ()
        if old_charge and multiplier is not None:
            choices = ((grid_up(multiplier*min(old_charge)),True),)
        yield F(0), F(0), absolute, choices
        return
    for lo, hi in intervals(F(0), heavy, buckets):
        count_max = min(count,(rho-lo)/2)
        assert hi<=count_max
        new_new = min(count_max**2/4,hi*count_max-hi**2/2)
        absolute = (1+min(rem_upper,rho-2*lo))/2-close
        vertex = min(hi,max(lo,absolute/(2*OVERLAP)))
        by_class = max(0,F(1,2)+theta/2-close)
        old_new = min(hi*by_class,
                      vertex*absolute-OVERLAP*vertex**2)/missing_lower
        if close>slack_pair:
            margin = close-slack_pair
            old_new = min(old_new,hi/(margin+2*hi))
        else:
            old_new = min(old_new,F(1,2)+F(5,2)*(slack_pair-close)
                          *min(absolute,by_class)/missing_lower)
        if close>theta:
            old_new = min(old_new,hi/(close-theta+hi))
        joint_quadratic = JOINT_OVERLAP+F(3,4)
        joint_linear = absolute+count_max/2
        joint_vertex = min(hi,max(0,joint_linear/(2*joint_quadratic)))
        joint = count_max**2/4+joint_vertex*joint_linear-joint_quadratic*joint_vertex**2
        absolute_factor = min(old_new+new_new/missing_lower,joint/missing_lower)
        charged_factor = old_new+min(new_new,unpaid)/missing_lower
        if close>=rho:
            charged_factor = min(charged_factor,3*old_new)
        yield lo, grid_up(absolute_factor), F(0), (
            (grid_up(absolute_factor),False),(grid_up(charged_factor),True))


def box_coefficient(kappa, slack_fee, missing_lower, missing_upper,
                    rem_lower, rem_upper, choices, mu, duplicate_fee):
    local = []
    for factor, charge_v in choices:
        if charge_v and kappa<=0:
            continue
        missing_fee = grid_down(1-(1-2*kappa)*factor)
        lower = (slack_fee*(rem_lower if slack_fee>=0 else rem_upper)/2
                 +missing_fee*(missing_lower if missing_fee>=0 else missing_upper))
        if lower+duplicate_fee>mu:
            return None
        low_ratio = rem_lower/(2*missing_upper)
        coefficient = (slack_fee*low_ratio+missing_fee)/(low_ratio+1+factor)
        if missing_lower:
            high_ratio = rem_upper/(2*missing_lower)
            coefficient = min(coefficient,(slack_fee*high_ratio+missing_fee)
                              /(high_ratio+1+factor))
        else:
            coefficient = min(coefficient,slack_fee)
        coefficient = min(coefficient,kappa if charge_v else F(1))
        local.append((grid_down(coefficient), factor))
    return max(local, default=(F(-1),F(0)))


def binned_step(tolerance, mu, imposed, *, anchor_cap=None, minimum_duplicates=F(0),
                desired_coefficient=F(0), anchor_parallel=F(0)):
    if anchor_cap is None:
        anchor_cap = grid_up(anchor_ratio(tolerance,REFINED_ANCHOR))
    rho, size, missing, _ = old_core_for_anchor(anchor_cap,mu,imposed,enhanced=True,
                                               parallel=anchor_parallel)
    low_needed = grid_up(F(1,4)+rho/2)
    if low_needed<size:
        split = grid_down((size-low_needed)**2)-F(1,GRID)
    else:
        split = F(0)
    if split<=0:
        split = F('.00002')
        if rho<size:
            alternative = grid_down((size-rho)**2)-F(1,GRID)
            if alternative>0:
                split = min(F('.00015'),alternative)
    assert split>0
    bins = [(F(0),min(split,missing))]
    edge = split
    while edge<min(missing,missing/80):
        following = min(missing, grid_up(F(6,5)*edge))
        bins.append((edge,following))
        edge = following
    if missing>edge:
        bins.extend(intervals(edge,missing,80))
    global_rho = rho

    def audit_interval(lo, hi, refinement, lower_theta, upper_theta):
        minimum, new_imposed, ruled_out = F(1), F(0), 0
        rho = min(global_rho,F(5,2)*upper_theta)
        size = (1-rho)/2
        upper_theta = min(upper_theta,rho)
        residual_buckets = 64 * 2**refinement
        heavy_buckets = 24 * 2**refinement
        if rho<anchor_parallel:
            return minimum, new_imposed, residual_buckets*heavy_buckets
        cover = grid_down(F(3,2)-rho/2-2*hi/(1-upper_theta))
        old_theta = upper_theta
        for _ in range(6):
            slack_gap = min((mu+a*rho/2+b*(rho-anchor_parallel)-lo)/(a+F(1,2))
                            for a,b in outside_rates(cover,rho))
            if slack_gap<0:
                break
            old_theta = min(old_theta,(rho+root_up(rho**2+6*slack_gap))/3)
            cover = max(cover,grid_down(F(3,2)-rho/2-2*hi/(1-old_theta)))
        if slack_gap<0 or old_theta<lower_theta:
            return minimum, new_imposed, residual_buckets*heavy_buckets
        extra_slack = rho-old_theta
        root = (root_up(extra_slack**2+4*hi)-extra_slack)/2
        close = grid_down(size-root)-F(1,GRID)
        assert 0<close<size and (size-close)*(size-close+extra_slack)>hi
        initial_residual = max(anchor_parallel,2*lower_theta-rho)
        for r0, r1 in intervals(initial_residual,rho,residual_buckets):
            theta = min(rho,(rho+r1)/2,old_theta)
            cover_bound = max(cover,grid_down(F(3,2)-rho/2-2*hi/(1-theta)))
            w = min(close,cover_bound-1)
            assert 0<w<=F(1,2) and 1<cover_bound<2
            base = F(1,2)-(1-2*w)/cover_bound
            min_rich_degree = 2*(close+size)
            fees = [(F(0),w-base)]
            if min_rich_degree<=1:
                center = cover_bound/2
                tangent = (F(1,2)-w)/(center*(1-center))
                unused = min(w-base,tangent*max(0,min_rich_degree-center)**2)
                assert 0<=unused<=w
                fees = [(w-unused,F(0))]
                if minimum_duplicates>0:
                    fees += [(w-unused/2,(w-base)/2),(w,w-base)]
            rates = [(mixed_surcharge(rho,theta,w,size,rich,r1,lower_theta),
                      max(w-size+theta,2*max(rich,min(w,theta))/3,w/2), rate)
                     for rich,rate in fees]
            outside = outside_rates(cover_bound,rho) if minimum_duplicates else ()
            for heavy, absolute, extra, choices in binned_hole_choices(
                    rho,size,close,theta,lo,r0,r1,heavy_buckets,anchor_parallel):
                rem_lower, rem_upper = max(r0,heavy+anchor_parallel), min(r1,rho-2*heavy)
                new_theta = max(0,lower_theta-(rho-rem_lower)/2)
                template_gap = max(0,new_theta*(3*new_theta-2*rem_upper)/2)
                external = F(0)
                if minimum_duplicates>0:
                    core_hosts = rem_upper/2-template_gap+2*(absolute*hi+extra)
                    external = min(a*core_hosts+b*(rem_upper-heavy-anchor_parallel)
                                   for a,b in outside)
                candidates = []
                for surcharge,total_fee,duplicate_rate in rates:
                    fee = min(surcharge,total_fee*(1-(heavy+anchor_parallel)/r1))
                    slack_fee = grid_down(base-fee)
                    duplicate_fee = duplicate_rate*max(0,minimum_duplicates-external)
                    bonus = duplicate_fee+(F(1,2)-base)*template_gap
                    if not lo:
                        direct = (slack_fee*(rem_lower if slack_fee>=0 else rem_upper)/2
                                  +bonus-(1-2*base)*extra)
                        if direct>mu:
                            break
                    result = box_coefficient(base,slack_fee,lo,hi,rem_lower,rem_upper,
                                             choices,mu,bonus)
                    if result is None:
                        break
                    candidates.append(result)
                else:
                    coefficient, factor = max(candidates)
                    if coefficient<=0 or coefficient<desired_coefficient:
                        if old_theta-lower_theta>global_rho/16:
                            mid = (lower_theta+old_theta)/2
                            return combine((audit_interval(lo,hi,refinement,lower_theta,mid),
                                            audit_interval(lo,hi,refinement,mid,old_theta)))
                        if refinement<2:
                            mid = (lo+hi)/2
                            return combine((
                                audit_interval(lo,mid,refinement+1,lower_theta,old_theta),
                                audit_interval(mid,hi,refinement+1,lower_theta,old_theta)))
                    assert coefficient>0, (rho,mu,lo,hi,r0,r1,heavy,coefficient,refinement)
                    minimum = min(minimum,coefficient)
                    new_imposed = max(new_imposed,min(hi,grid_up(mu/(coefficient*(1+factor)))))
                    continue
                ruled_out += 1
        return minimum, new_imposed, ruled_out

    def combine(results):
        coefficients, imposed_bounds, exclusions = zip(*results)
        return min(coefficients), max(imposed_bounds), sum(exclusions)

    return combine(tuple(audit_interval(lo,hi,0,F(0),rho) for lo,hi in bins))


def verify_binned_even(tolerance, prior=F(0)):
    result = binned_step(tolerance,F(0),F(1),minimum_duplicates=prior)
    assert result[0]>0
    return result


def verify_anchor_only(rho, parallel=F(0)):
    result = binned_step(None,F(0),F(1),anchor_cap=rho,anchor_parallel=parallel)
    assert result[0]>0
    return result


def conditional_tolerance(rho, certificate):
    gap = F(certificate["verified_support_gap"])
    shift = F(certificate["gamma"])*(rho-F(certificate["anchor_ratio"]))
    assert shift>=0
    return (gap+shift*(F(1,8)-EPS_ABUNDANCE/ABUNDANCE))/(1+shift/ABUNDANCE)


def verify_binned_odd(tolerance, degree, prior=F(0), *, anchor_cap=None):
    mu = F(1,2*degree)
    imposed = F(1)
    attempts = []
    for _ in range(6):
        coefficient, next_imposed, ruled_out = binned_step(
            tolerance,mu,imposed,anchor_cap=anchor_cap,minimum_duplicates=max(0,prior-mu),
            desired_coefficient=mu/(prior or tolerance))
        reduced = grid_up(mu/coefficient)
        attempts.append((str(coefficient),str(next_imposed),ruled_out,str(reduced)))
        if reduced<=prior:
            return attempts, [('prior support tolerance',str(prior))]
        if reduced<tolerance:
            try:
                finish = verify_wider_odd(reduced,degree)
            except AssertionError:
                pass
            else:
                return attempts, finish
        assert next_imposed<imposed, (tolerance,degree,attempts)
        imposed = next_imposed
    raise AssertionError((tolerance,degree,attempts))


def main():
    from check_c5_dual import CONDITIONAL_RHO, HERE, verify as replay_moment

    for name, coefficient, error in [
        ("c5_abundance_column_candidate_third.json",ABUNDANCE,EPS_ABUNDANCE),
        ("c5_anchor_column_candidate_fifth.json",ANCHOR,EPS_ANCHOR),
        ("c5_anchor_column_candidate_sixth.json",REFINED_ANCHOR,EPS_ANCHOR),
    ]:
        output = replay_moment(HERE/name)
        assert F(output["gamma"])>=coefficient and F(output["epsilon"])<=error
        print("Exact moment replay:", name, output["gamma"], output["epsilon"], flush=True)
    verify(F(1,500),F('.029'),F(1,1000),F('.4065'),F('.00620'),F('1.4727'),False)
    verify(F('.0048'),F('.071'),F(0),F('.346'),F('.01403'),F('1.4342'),True)
    odd_kappa = verify(F('.0047'),F('.07'),F(1,3000),F('.346'),F('.01415'),F('1.4345'),True)
    assert 1/(2*odd_kappa*1500)<F(1,500)
    print('Three multigraph support tolerances verified using exact rational arithmetic.')
    print('Wider even tolerance 0.0122:', verify_wider_even(F('.0122')))
    for tolerance, degree in [('.0105',323),('.0115',451),('.0120',751),('.0122',1001)]:
        steps=verify_wider_odd(F(tolerance),degree)
        print('Wider odd tolerance', tolerance, 'minimum degree', degree, 'certified steps', steps)
    print('Exact overlap constants:', tuple(map(str, verify_overlap())), flush=True)
    anchor_cap = F('.333')
    print('Anchor-only cap 0.333:',
          verify_anchor_only(anchor_cap), flush=True)
    for tolerance, degree in [('.0140',401),('.0150',451),('.0155',551)]:
        rounds, finish = verify_binned_odd(F(tolerance),degree)
        print('Joint odd tolerance', tolerance, 'minimum degree', degree,
              'certified steps', rounds, finish, flush=True)
    for tolerance, degree, prior in [('.0150',401,'.0140'),('.0160',451,'.0150'),
                                     ('.0165',451,'.0160'),('.0165',551,'.0155'),
                                     ('.0170',551,'.0165')]:
        rounds, finish = verify_binned_odd(F(tolerance),degree,F(prior))
        print('Odd tolerance with repeat charge',tolerance,'minimum degree',degree,
              'certified steps',rounds,finish,flush=True)
    joint = replay_moment(HERE/"c5_conditional_candidate_first.json")
    assert F(joint["anchor_ratio"])==CONDITIONAL_RHO
    assert F(joint["verified_support_gap"])>F('.01685')
    print("Exact combined moment gap:",joint["verified_support_gap"],flush=True)
    rounds, finish = verify_binned_odd(F('.01685'),651,F('.0165'),anchor_cap=CONDITIONAL_RHO)
    print('Odd tolerance with combined moment 0.01685 minimum degree 651:',
          rounds,finish,flush=True)
    for tolerance, degree, prior in [('.0172',651,'.01685'),('.0175',651,'.0172'),
                                     ('.0180',801,'.0175')]:
        rounds, finish = verify_binned_odd(F(tolerance),degree,F(prior))
        print('Odd tolerance with repeat charge',tolerance,'minimum degree',degree,
              'certified steps',rounds,finish,flush=True)
    stronger = replay_moment(HERE/"c5_conditional_candidate_032_fourth.json")
    assert F(stronger["anchor_ratio"])==F('.320')
    assert F(stronger["verified_support_gap"])>F('.01959')
    shifted = conditional_tolerance(anchor_cap,stronger)
    assert shifted>F('.02025')
    print('Even tolerance 0.02025 via shifted combined moment:',str(shifted),flush=True)
    rounds, finish = verify_binned_odd(F('.01959'),1501,F('.0180'),anchor_cap=F('.320'))
    print('Odd tolerance with combined moment 0.01959 minimum degree 1501:',
          rounds,finish,flush=True)
    rounds, finish = verify_binned_odd(F('.02025'),2501,F('.01943'),anchor_cap=anchor_cap)
    print('Odd tolerance with shifted combined moment 0.02025 minimum degree 2501:',
          rounds,finish,flush=True)
    print('Anchor-only cap 0.34 with parallel incidence at least 0.04:',
          verify_anchor_only(F('.34'),F('.04')),flush=True)
    print('All tabulated multigraph constants verified exactly.',flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run without -O/-OO or PYTHONOPTIMIZE")
    main()
