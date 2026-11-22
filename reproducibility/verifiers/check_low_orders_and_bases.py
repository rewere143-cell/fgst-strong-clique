#!/usr/bin/env python3
"""Standard-library-only independent exhaustive audit of low-order indexes and bases.
Does not import production code or read a production variable/representative list.
"""
from pathlib import Path
from itertools import combinations, permutations
from collections import defaultdict
from array import array
import json,sys,time
P=Path(__file__).resolve().parents[1]/'data'
import argparse
parser=argparse.ArgumentParser();parser.add_argument('--output',required=True);args=parser.parse_args()
if not __debug__:raise RuntimeError('Assertions must be enabled')
start=time.time()
def edges(n):return list(combinations(range(n),2))
def decode(n,code):
 assert 0<=code<3**(n*(n-1)//2-1)
 a=[[0]*n for _ in range(n)];a[0][1]=a[1][0]=2
 for i,j in edges(n)[1:]:a[i][j]=a[j][i]=code%3;code//=3
 return a
def encode(a,order):
 assert a[order[0]][order[1]]==2
 result=0;power=1
 for i,j in edges(len(order))[1:]:result+=power*a[order[i]][order[j]];power*=3
 return result
def admissible(a):
 n=len(a)
 # Check each four-set and each of its three partitions into pairs.
 for vertices in combinations(range(n),4):
  u=vertices[0]
  for v in vertices[1:]:
   x,y=[w for w in vertices[1:] if w!=v]
   if a[u][v]==a[x][y]==2 and not any(a[i][j] for i in (u,v) for j in (x,y)):return False
 # A graph is connected iff every cut with vertex 0 on one side is crossed.
 for cut in range(1,2**n-1,2):
  if not any(a[i][j] and ((cut>>i)&1)!=((cut>>j)&1) for i,j in edges(n)):return False
 return True
valid={2:{0}};indexes={};reports=[]
for n in (3,4,5):
 total=3**(n*(n-1)//2-1)
 with open(P/f'idx{n}.bin','rb') as f:idx=array('i');idx.frombytes(f.read())
 assert idx.itemsize==4 and len(idx)==total
 if sys.byteorder!='little':idx.byteswap()
 expected={c for c in range(total) if admissible(decode(n,c))};valid[n]=expected;indexes[n]=idx
 for c,id in enumerate(idx):assert (id>=0)==(c in expected),(n,c,id,'validity');assert id>=0 or id==-1
 remaining=expected.copy();seen_ids=set();orbit_sizes=[];perms=list(permutations(range(n)))
 while remaining:
  c=min(remaining);a=decode(n,c)
  orbit={encode(a,p) for p in perms if a[p[0]][p[1]]==2}
  assert orbit<=remaining,(n,c,'intersecting independently generated orbits')
  labels={idx[z] for z in orbit};assert len(labels)==1,(n,c,'split orbit',labels)
  label=labels.pop();assert label not in seen_ids,(n,c,'merged orbit',label)
  seen_ids.add(label);orbit_sizes.append(len(orbit));remaining-=orbit
 offset=sum(x['orbits'] for x in reports)
 assert seen_ids==set(range(offset,offset+len(orbit_sizes))),(n,'missing/duplicate/out-of-range representative IDs')
 reports.append(dict(order=n,total_patterns=total,valid_patterns=len(expected),orbits=len(orbit_sizes),first_id=offset,last_id=offset+len(orbit_sizes)-1,all_validity_and_partition_checks=True))
 print(json.dumps(reports[-1]),flush=True)
# Verify all declared types and flags, prefix compatibility, and basis completeness.
lines=iter((P/'basis.txt').read_text().splitlines());N,B=map(int,next(lines).split());assert N==23789 and B==57
blocks=[];total_flags=0
for b in range(B):
 k,t,m=map(int,next(lines).split());assert k in (2,3,4) and t in valid[k]
 flags=[tuple(map(int,next(lines).split())) for _ in range(m)];assert len(set(flags))==m,(b,'duplicate basis entry')
 assert flags[0]==(k,t),(b,'missing type-only basis flag')
 for n,c in flags:
  assert k<=n<=5 and c in valid[n],(b,n,c,'invalid/disconnected flag')
  assert encode(decode(n,c),range(k))==t,(b,n,c,'wrong type prefix')
 sizes=sorted({n for n,c in flags})
 assert sizes==([2,3] if b==0 else [3,4] if b<=8 else [2,3,4] if b==9 else [4,5]),(b,sizes)
 # Independently enumerate all permissible extension-pattern orbits.
 for n in sizes:
  def tail_orbit(c):
   a=decode(n,c)
   return frozenset(encode(a,tuple(range(k))+p) for p in permutations(range(k,n)))
  expected={tail_orbit(c) for c in valid[n] if encode(decode(n,c),range(k))==t}
  actual=[tail_orbit(c) for nn,c in flags if nn==n]
  assert len(set(actual))==len(actual),(b,n,'equivalent duplicate basis functions')
  assert set(actual)==expected,(b,n,'incomplete extension basis')
 blocks.append((k,t,m));total_flags+=m
try:next(lines);raise AssertionError('extra basis data')
except StopIteration:pass
assert blocks[0][0:2]==blocks[9][0:2]==(2,0)
assert {t for k,t,m in blocks[1:9]}==valid[3]
assert len({indexes[4][t] for k,t,m in blocks[10:]})==reports[1]['orbits']==47
# Validate every degree base and selected extension-attachment vertex.
lines=iter((P/'degree.txt').read_text().splitlines());D=int(next(lines));rows=[];hist=defaultdict(int)
for row in range(D):
 k,c,u=map(int,next(lines).split());assert k in (2,3,4,5) and c in valid[k],(row,'invalid/disconnected base')
 assert 0<=u<k,(row,'attachment vertex out of range');rows.append((k,c,u));hist[k]+=1
assert len(set(rows))==D
try:next(lines);raise AssertionError('extra degree data')
except StopIteration:pass
out=dict(low_order_indexes=reports,basis_blocks=B,basis_flags=total_flags,all_basis_types_flags_prefixes_valid=True,all_bases_complete_without_duplicate_extension_functions=True,degree_rows=D,degree_rows_by_base_order=dict(hist),all_degree_bases_and_vertices_valid=True,seconds=time.time()-start)
Path(args.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
