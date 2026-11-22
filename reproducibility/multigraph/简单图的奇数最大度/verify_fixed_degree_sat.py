"""Regenerate all fixed-degree simple-graph CNFs and replay archived RUP."""

from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import gzip
import json
import subprocess

from d5_check_lrat import replay
from d5_exact_sat import instance
from odd_fixed_degree_sat import profiles


def copy_and_hash(source, target):
    digest = sha256()
    opener = gzip.open if source.suffix == '.gz' else open
    with opener(source, 'rb') as data, target.open('wb') as output:
        for chunk in iter(lambda: data.read(1 << 20), b''):
            digest.update(chunk)
            output.write(chunk)
    return digest.hexdigest()


def locate(directory, name, extension):
    compressed = directory / (name + extension + '.gz')
    if compressed.is_file():
        return compressed
    raw = directory / (name + extension)
    if raw.is_file():
        return raw
    raise FileNotFoundError(compressed)


def verify(case, evidence, degree, checker):
    n, triangles, counts, levels = case
    directory, row = evidence
    name = row['name']
    assert n == row['n'] and triangles == row['triangles']
    assert counts == tuple(row['counts'])
    archived_cnf = locate(directory, name, '.cnf')
    archived_proof = locate(directory, name, '.lrat')
    extra_cuts = row.get('extra_cuts', False)
    with TemporaryDirectory(prefix='fgst-rup-') as temporary:
        work = Path(temporary)
        expected = work / 'regenerated.cnf'
        cnf = work / 'input.cnf'
        proof = work / 'proof.lrat'
        instance(levels, triangles, degree, extra_cuts).dump(expected)
        input_hash = copy_and_hash(archived_cnf, cnf)
        if input_hash != row['cnf_sha256'] or cnf.read_bytes() != expected.read_bytes():
            raise ValueError(f'CNF differs from regenerated input: {name}')
        proof_hash = copy_and_hash(archived_proof, proof)
        if proof_hash != row['lrat_sha256']:
            raise ValueError(f'LRAT SHA-256 mismatch: {name}')
        if checker:
            process = subprocess.run(
                [str(checker), cnf.name, proof.name], cwd=work,
                capture_output=True, check=True, text=True,
            )
            result = json.loads(process.stdout)
        else:
            result = replay(cnf, proof)
    if result != row['check']:
        raise ValueError(f'RUP replay counts differ: {name}')
    return {
        'name': name, 'directory': str(directory), 'n': n,
        'cnf_sha256': input_hash, 'lrat_sha256': proof_hash,
        'extra_cuts': extra_cuts, **result,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('degree', type=int)
    parser.add_argument('directories', type=Path, nargs='+')
    parser.add_argument('--checker', type=Path)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--available-only', action='store_true')
    args = parser.parse_args()
    expected = {
        f'd{args.degree:02d}_n{n:02d}_' + '-'.join(map(str, counts)):
        (n, triangles, counts, levels)
        for n, triangles, counts, levels in profiles(args.degree)
    }
    available = {}
    for directory in args.directories:
        for metadata in sorted(directory.glob('d*.json')):
            row = json.loads(metadata.read_text())
            if row['result'] == 'VERIFIED_UNSAT':
                if metadata.stem != row['name'] or row['name'] not in expected:
                    raise ValueError(f'Unexpected proof metadata: {metadata}')
                available.setdefault(row['name'], (directory, row))
    missing = sorted(expected.keys() - available.keys())
    if missing and not args.available_only:
        raise ValueError(f'Missing {len(missing)} profiles, first {missing[:4]}')
    checker = args.checker.resolve() if args.checker else None
    names = sorted(available)
    rows = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        jobs = pool.map(lambda key: verify(expected[key], available[key], args.degree, checker), names)
        for row in jobs:
            rows.append(row)
            if len(rows) % 25 == 0:
                print(f'{len(rows)}/{len(names)} independently replayed', flush=True)
    report = {
        'degree': args.degree,
        'profiles': len(expected),
        'verified': len(rows),
        'all_unsat': not missing,
        'missing': missing,
        'checker': 'compiled positive RUP' if checker else 'Python positive RUP',
        'rows': rows,
    }
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(f'Exact replay complete: {len(rows)}/{len(expected)}', flush=True)


if __name__ == '__main__':
    main()

