exec(open(__file__.replace('export_reverse_data.py','check_moments.py')).read().split('cases=[]')[0])
def code(c):return sum(v*3**i for i,v in enumerate(c[1:]))
with open(OUT/'basis.txt','w') as f:
 f.write(f"{len(p['variables'])} {len(bases)}\n")
 for (k,typ,flags),(_,m,K,D) in zip(bases,p['blocks']):
  f.write(f'{k} {code(typ)} {m}\n')
  for n,c in flags:f.write(f'{n} {code(c)}\n')
# Independent complete low-order orbit map from all permutations of representatives.
for n in (3,4,5):
 idx=np.full(3**(n*(n-1)//2-1),-1,dtype=np.int32)
 for q,(nn,c) in enumerate(p['variables']):
  if nn!=n:continue
  a=mat(c,n)
  for perm in it.permutations(range(n)):
   if a[perm[0],perm[1]]==2:idx[code(pattern(a,perm))]=q
 idx.tofile(OUT/f'idx{n}.bin')
keys=[];values=[];offset=0;N=len(p['variables'])
for typ,m,K,D in p['blocks']:
 coo=D.tocoo();keys.extend(((offset+coo.row.astype(np.int64))*N+coo.col).tolist());values.extend(coo.data.astype(np.int32).tolist());offset+=m*m
np.array(keys,dtype=np.int64).tofile(OUT/'keys.bin');np.array(values,dtype=np.int32).tofile(OUT/'values.bin')
print('Exported',len(keys),'expected nonzeros',flush=True)
import re,ast
with open(OUT/'degree.txt','w') as f:
 f.write(f"{len(p['names'])}\n")
 for name in p['names']:
  k,txt,u=re.match(r'degree_(\d+)_(.*)_(\d+)$',name).groups();c=ast.literal_eval(txt);f.write(f'{k} {code(c)} {u}\n')
coo=p['A'].tocoo();(coo.row.astype(np.int64)*N+coo.col).tofile(OUT/'degree_keys.bin');coo.data.astype(np.int32).tofile(OUT/'degree_values.bin')
