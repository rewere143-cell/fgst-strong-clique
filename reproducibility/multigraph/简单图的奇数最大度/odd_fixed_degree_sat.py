"""Benchmark exact finite searches for other fixed odd degrees."""
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse
import datetime
import gzip
import json
import shutil
import subprocess

from d5_exact_sat import instance
from d5_check_lrat import replay


def profiles(degree):
    target = (5*degree**2 - 2*degree + 1)//4 + 1
    delta = Fraction(5*degree**2, 4) - target
    penalty = delta * 2*target / (Fraction(9,20)*degree)
    limit = (int(penalty)//2)*2

    def choose(h, total, cost, counts):
        if h == degree:
            if total % degree == 0:
                yield counts + (total//degree,), (limit-cost)//6
            return
        weight = h * (degree-h)
        for n in range(min(total//h, (limit-cost)//weight)+1):
            yield from choose(h+1,total-n*h,cost+n*weight,counts+(n,))
    for counts, tri in choose(1,2*target,0,()):
        n = sum(counts)
        if n <= degree:
            continue
        # A vertex of marked degree h is incident with h distinct pairs.
        levels = tuple(h for h,n_h in enumerate(counts,1) for _ in range(n_h))
        yield n, tri, counts, levels


def check_one(args, case):
    n, tri, counts, levels = case
    name = f'd{args.degree:02d}_n{n:02d}_' + '-'.join(map(str,counts))
    certdir = args.out
    cnf, proof, log, result = (
        certdir / (name + suffix) for suffix in ('.cnf','.lrat','.log','.json')
    )
    if result.exists():
        old = json.loads(result.read_text())
        if old['result'] == 'VERIFIED_UNSAT':
            if args.gzip:
                for path in (cnf, proof):
                    if path.exists():
                        zip_file(path)
            return old
    if args.deadline and datetime.datetime.now(datetime.timezone.utc) >= args.deadline:
        return dict(name=name, n=n, counts=counts, result='DEADLINE')
    f = instance(levels,tri,args.degree,args.cuts)
    f.dump(cnf)
    with log.open('wb') as stream:
        seconds = args.time_limit
        if args.deadline:
            seconds = min(seconds, max(1, (args.deadline - datetime.datetime.now(datetime.timezone.utc)).total_seconds()))
        try:
            code = subprocess.run(
                [str(args.solver), '--lrat', '--no-binary', str(cnf), str(proof)],
                stdout=stream, stderr=subprocess.STDOUT, timeout=seconds,
            ).returncode
        except subprocess.TimeoutExpired:
            code = None
    row = dict(name=name,n=n,triangles=tri,counts=counts,code=code,extra_cuts=args.cuts)
    if code == 20:
        row['result'] = 'VERIFIED_UNSAT'
        if args.checker:
            verification = subprocess.run(
                [str(args.checker), cnf.name, proof.name], cwd=certdir,
                capture_output=True, check=True, text=True,
            )
            row['check'] = json.loads(verification.stdout)
        else:
            row['check'] = replay(cnf,proof)
        for path, key in ((cnf, 'cnf_sha256'), (proof, 'lrat_sha256')):
            digest = sha256()
            with path.open('rb') as stream:
                for chunk in iter(lambda: stream.read(1 << 20), b''):
                    digest.update(chunk)
            row[key] = digest.hexdigest()
    elif code == 10:
        row['result'] = 'SAT_REQUIRES_GRAPH_VALIDATION'
    else:
        row['result'] = 'UNKNOWN'
        if args.discard_unverified_proof and proof.exists():
            proof.unlink()
    if args.gzip:
        for path in (cnf, proof):
            if path.exists():
                zip_file(path)
    result.write_text(json.dumps(row,indent=2)+'\n',encoding='utf-8')
    print(f"{name}: {row['result']}",flush=True)
    return row


def zip_file(path):
    target = path.with_suffix(path.suffix + '.gz')
    with path.open('rb') as source, gzip.open(target, 'wb', compresslevel=1) as dest:
        shutil.copyfileobj(source, dest)
    path.unlink()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('degree',type=int)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--solver',type=Path,required=True)
    parser.add_argument('--max-order',type=int,default=100)
    parser.add_argument('--min-order',type=int,default=1)
    parser.add_argument('--samples',type=int,default=1)
    parser.add_argument('--jobs',type=int,default=6)
    parser.add_argument('--time-limit',type=int,default=60)
    parser.add_argument('--gzip',action='store_true')
    parser.add_argument('--cuts',action='store_true')
    parser.add_argument('--checker',type=Path)
    parser.add_argument('--deadline',type=datetime.datetime.fromisoformat)
    parser.add_argument('--avoid',type=Path,action='append',default=[])
    parser.add_argument('--discard-unverified-proof',action='store_true')
    parser.add_argument('--select',nargs='*')
    args=parser.parse_args()
    args.solver=args.solver.resolve()
    if args.checker:
        args.checker=args.checker.resolve()
    if args.deadline and args.deadline.tzinfo is None:
        parser.error('--deadline requires a time zone offset')
    if args.degree<5 or not args.degree%2:
        parser.error('expected an odd degree at least 5')
    args.out.mkdir(parents=True,exist_ok=True)
    all_cases=sorted(profiles(args.degree))
    cases=[case for case in all_cases if args.min_order<=case[0]<=args.max_order]
    if args.avoid:
        avoided = set()
        for directory in args.avoid:
            for path in directory.glob('d*.json'):
                try:
                    if json.loads(path.read_text())['result'] == 'VERIFIED_UNSAT':
                        avoided.add(path.stem)
                except (json.JSONDecodeError, KeyError):
                    continue
        cases = [case for case in cases if f'd{args.degree:02d}_n{case[0]:02d}_' + '-'.join(map(str,case[2])) not in avoided]
    if args.select:
        cases=[case for case in cases if '-'.join(map(str,case[2])) in args.select]
    if args.samples:
        from collections import defaultdict
        by_order=defaultdict(list)
        for case in cases:
            by_order[case[0]].append(case)
        cases=[]
        for group in by_order.values():
            if len(group)<=args.samples:
                cases.extend(group)
            else:
                cases.extend(group[(len(group)-1)*idx//max(1,args.samples-1)]
                             for idx in range(args.samples))
    print(f'{len(all_cases)} profiles, {len(cases)} selected',flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results=list(pool.map(lambda c:check_one(args,c),cases))
    (args.out/'summary.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':
    main()
