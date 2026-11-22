"""Lift the order-five weighted system with a targeted sixth-order simple projection."""

import argparse
from fractions import Fraction as Q
import hashlib
from itertools import combinations
import json
from math import lcm
from pathlib import Path
import sys

from multigraph_lift_probe import decode, edge_pairs
from multigraph_low_repeat_search import enhanced_system, solve


SHADOW_SUFFIXES = (".data.npz",".ore.npz",".gram.npz",".blocks.json",
                   ".sample_meta.npz",".sample.npz",".sample_tagged.npz")


def shadow_hashes(prefix):
    return {s:hashlib.sha256(prefix.with_suffix(s).read_bytes()).hexdigest()
            for s in SHADOW_SUFFIXES}


def anchor_six_coefficients(code):
    """Return the root-cycle positions and the good-neighbor coefficient."""
    colors = dict(zip(edge_pairs(6),decode(6,code)))

    def color(u,v):
        return colors[min(u,v),max(u,v)]

    good = 0
    outside = []
    good_vertices = []
    for u in range(6):
        cycle = tuple(v for v in range(6) if v!=u)
        edges = [(v,w) for v,w in combinations(cycle,2) if color(v,w)]
        if len(edges)!=5 or any(color(v,w)!=2 for v,w in edges):
            continue
        if any(sum(v in edge for edge in edges)!=2 for v in cycle):
            continue
        outside.append(u)
        neighbors = [v for v in cycle if color(u,v)]
        if len(neighbors)==2 and all(color(u,v)==2 for v in neighbors) and not color(*neighbors):
            good += 20
            good_vertices.append(u)
    return good,outside,good_vertices


def decorated_anchors(six,plain_six,anchors,depth):
    import numpy as np

    use = plain_six.copy()
    tags = np.fromiter((int(mask).bit_count() for mask in six["mask"]),dtype=np.int8)
    good = np.zeros((max(1,depth+1),len(use)),dtype=np.int64)
    excess = np.zeros((max(0,depth+1),len(use)),dtype=np.int64)
    for row in np.flatnonzero(plain_six):
        good[0,row] = anchors[int(six["code"][row])][0]
    if depth < 0:
        return use,tags,good,excess
    incidence = [sum(1<<i for i,e in enumerate(edge_pairs(6)) if u in e) for u in range(6)]
    for row in np.flatnonzero((six["order"]==6)&(tags>0)):
        decoration = int(six["mask"][row])
        count = int(tags[row])
        _,cycle_outside,good_outside = anchors[int(six["code"][row])]
        for u in cycle_outside:
            added = (decoration & incidence[u]).bit_count()
            if not added and count<=depth:
                use[row] = True
                if u in good_outside:
                    good[count,row] += 20
            elif added==1 and count-1<=depth:
                use[row] = True
                excess[count-1,row] += 10
    return use,tags,good,excess


def build_shadow(cache,shadow,settings):
    import numpy as np
    from scipy.sparse import coo_matrix, csr_matrix, hstack, load_npz, vstack

    eq,ineq,grams,sizes,base,tags,scale,objective,roots = enhanced_system(cache,settings)
    six = dict(np.load(shadow.with_suffix(".data.npz")))
    plain_six = (six["order"]==6)&(six["mask"]==0)
    anchors = {int(code):anchor_six_coefficients(int(code)) for code in six["code"][plain_six]}
    depth = settings.get("anchor_tag_depth",0 if settings.get("anchor_excess") else -1)
    assert -1<=depth<=2
    use,six_tags,good_rows,excess_rows = decorated_anchors(six,plain_six,anchors,depth)
    other = (six["order"]==6)&~use
    indices = {key:i for i,key in enumerate(zip(six["order"],six["code"],six["mask"]))}
    prefix = [indices[key] for key in zip(base["order"],base["code"],base["mask"])]
    columns = np.r_[prefix,np.flatnonzero(use)]
    full = {k:six[k][columns] for k in ("order","code","mask","aut_count","normalizer","twice_obj")}
    assert np.array_equal(full["twice_obj"],np.r_[objective,np.zeros(use.sum(),dtype=np.int64)])
    assert len(prefix)==np.count_nonzero(six["order"]<6)

    cap = Q(settings["simple_support_cap"])
    slo = (1-Q(settings["e_high"]))*Q(settings["mass_low"])
    shi = min(cap,(1-Q(settings["e_low"]))*Q(settings["mass_high"]))
    lower_anchor = Q(settings["anchor_minimum"])
    gamma = Q(settings["anchor_gamma"])
    eps = Q(settings["anchor_epsilon"])
    mass_lower = Q(settings["mass_low"])
    below_uniform = max(Q(0), Q(5,4)-mass_lower)
    # Below 5/4 the caller must establish the support cap and anchor
    # lower bound independently. The generic slack bound gives 2J-R <= 4δ D.
    assert not below_uniform or settings.get("known_support_and_anchor_bounds") is True
    assert 0<=lower_anchor<=Q(33,100)
    assert 0<gamma<=Q(56820,100000) and eps>=Q(1,10**9)
    extra_scale = lcm((2*slo).denominator,(2*shi).denominator,
                      lower_anchor.denominator,gamma.denominator,eps.denominator,
                      (4*below_uniform).denominator,4)
    new_scale = lcm(scale,extra_scale)
    multiplier = new_scale//scale
    nextra = int(use.sum())
    n = len(columns)

    def extend_rows(matrix):
        return hstack((matrix*multiplier,csr_matrix((matrix.shape[0],nextra),dtype=np.int64)),
                      format="csr")

    def extend_gram(matrix):
        return vstack((matrix*multiplier,csr_matrix((nextra,matrix.shape[1]),dtype=np.int64)),
                      format="csc")

    terms = [extend_rows(ineq)]
    degree = load_npz(shadow.with_suffix(".ore.npz")).tocsr().astype(np.int64)
    cycle_parent = (six["order"]==5)&(six["code"]==6012)
    parent_atoms = (six["order"]==5)&((six_tags==0)|(cycle_parent&(six_tags<=depth)))
    negative_parent = degree[:,parent_atoms].min(axis=1).toarray().ravel()
    degree = degree[negative_parent<0]
    assert not np.any(degree[:,other].data<0)
    omitted = degree[:,other]
    exhaustive = omitted.getnnz(axis=1)==0
    terms.append(degree[~exhaustive][:,columns]*new_scale)
    out_eq = vstack((extend_rows(eq),degree[exhaustive][:,columns]*new_scale),format="csr")

    root = csr_matrix(np.where((full["order"]==2)&(full["mask"]==0),2,0))
    cycle = csr_matrix(np.where((full["order"]==5)&(full["mask"]==0)&(full["code"]==6012),10,0))
    assert cycle.nnz==1
    good = csr_matrix(good_rows[0,columns])
    loss = 5*cycle-good
    simple_mass = csr_matrix(np.where(full["mask"]==0,full["twice_obj"],0).astype(np.int64))
    terms.extend((
        int(lower_anchor*new_scale)*cycle-loss*new_scale,
        loss*int(gamma*new_scale)+simple_mass*(new_scale//2)
        -root*int((Q(5,4)+eps)*new_scale),
    ))
    for k,excess in enumerate(excess_rows):
        if k:
            tagged_cycle = csr_matrix(np.where(cycle_parent[columns]&(six_tags[columns]==k),10,0))
            loss_k = 5*tagged_cycle-csr_matrix(good_rows[k,columns])
            terms.append(int(lower_anchor*new_scale)*tagged_cycle-loss_k*new_scale)
        else:
            loss_k = loss
        cycle_k = tagged_cycle if k else cycle
        terms.append((2*csr_matrix(excess[columns])-loss_k)*new_scale
                     -cycle_k*int(4*below_uniform*new_scale))

    sample_info = np.load(shadow.with_suffix(".sample_meta.npz"))
    sample_parents = sample_info["extension_parents"]
    plain_parents = (six["order"][sample_parents]==4)&(six["mask"][sample_parents]==0)
    parents = sample_parents[plain_parents]
    extension = load_npz(shadow.with_suffix(".sample.npz"))-load_npz(shadow.with_suffix(".sample_tagged.npz"))
    extension = extension[plain_parents].tocsr().astype(np.int64)
    assert not extension[:,other].nnz
    parent = coo_matrix((six["aut_count"][parents],(np.arange(len(parents)),parents)),
                        shape=extension.shape,dtype=np.int64).tocsr()
    extension,parent = extension[:,columns],parent[:,columns]
    terms.extend((parent*int(2*slo*new_scale)-extension*new_scale,
                  extension*new_scale-parent*int(2*shi*new_scale)))

    out_grams = [extend_gram(g) for g in grams]
    selected = settings.get("shadow_blocks")
    record = json.loads(shadow.with_suffix(".blocks.json").read_text())
    all_gram = load_npz(shadow.with_suffix(".gram.npz")).tocsc()
    size_out = list(sizes)
    offset = 0
    for size,(number,mask) in zip(record["sizes"],record["origins"]):
        block = all_gram[:,offset:offset+size**2]
        offset += size**2
        if mask or size<=1 or (selected is not None and number not in selected):
            continue
        if not block[plain_six].nnz:
            continue
        assert not block[other].nnz
        out_grams.append(block[columns].tocsc().astype(np.int64)*new_scale)
        size_out.append(size)
    assert offset==all_gram.shape[1]
    options = dict(variables=n,rows=sum(a.shape[0] for a in terms),
                   grams=len(size_out),shadow_grams=len(size_out)-len(sizes),
                   shadow_coordinates=nextra,anchor_good_coefficients=good.nnz)
    print(json.dumps(options),flush=True)
    return (out_eq,vstack(terms,format="csr"),out_grams,size_out,full,
            np.r_[tags,six_tags[use]],new_scale,full["twice_obj"],roots)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cache",type=Path)
    parser.add_argument("shadow",type=Path)
    parser.add_argument("--vendor",type=Path)
    parser.add_argument("--lower",type=Q)
    parser.add_argument("--upper",type=Q)
    parser.add_argument("--seconds",type=int,default=480)
    parser.add_argument("--iterations",type=int,default=12000)
    parser.add_argument("--anchor-minimum",type=Q,default=Q(34,125))
    parser.add_argument("--shadow-blocks",type=int,nargs="*")
    parser.add_argument("--anchor-excess",action="store_true")
    parser.add_argument("--anchor-tag-depth",type=int,choices=(0,1,2))
    parser.add_argument("--direct",action="store_true")
    parser.add_argument("--numerical",type=Path)
    parser.add_argument("--certificate",type=Path)
    parser.add_argument("--replay",action="store_true")
    args = parser.parse_args()
    if args.vendor:
        sys.path.insert(0,str(args.vendor))
    from multigraph_weighted_maxdeg_exact import rounded_certificate, verify

    if args.replay:
        cert = json.loads(args.certificate.read_text())
        assert shadow_hashes(args.shadow)==cert["shadow_sha256"]
        print(json.dumps(verify(args.cache,cert,build_shadow(args.cache,args.shadow,cert["settings"])),
                         indent=2))
        return
    settings = dict(e_low=str(args.lower),e_high=str(args.upper),mass_low="5/4",
                    mass_high="2579/2000",local_beta="186/625",blend=True,
                    simple_support_cap="6189/5000",abundance_gamma="99999/100000",
                    abundance_epsilon="1/500000000",rooted_pentagon=True,
                    anchor_minimum=str(args.anchor_minimum),anchor_gamma="2841/5000",
                    anchor_epsilon="1/1000000000",shadow_blocks=args.shadow_blocks,
                    anchor_excess=args.anchor_excess)
    if args.anchor_tag_depth is not None:
        settings["anchor_tag_depth"] = args.anchor_tag_depth
    system = build_shadow(args.cache,args.shadow,settings)
    if args.certificate:
        cert = rounded_certificate(args.cache,args.numerical,"infeasible",settings,system)
        cert["shadow_sha256"] = shadow_hashes(args.shadow)
        result = verify(args.cache,cert,system)
        print(json.dumps(result,indent=2))
        if result["rigorous_infeasible"]:
            args.certificate.write_text(json.dumps(cert,separators=(",",":"))+"\n")
    else:
        solve(system,args.seconds,args.iterations,args.numerical,indirect=not args.direct)


if __name__=="__main__":
    main()
