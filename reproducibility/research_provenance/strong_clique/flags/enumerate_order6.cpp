// Enumerate isomorphism classes of root-connected, admissible marked graphs.
// Colors 0 absent, 1 unmarked host edge, 2 marked. Root is marked edge 01.
#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <chrono>
using namespace std;
int main(){
 const int n=6,T=4782969; vector<int32_t> id(T,-1);vector<int> reps; vector<pair<int,int>> pairs;
 for(int u=0;u<n;u++)for(int v=u+1;v<n;v++)pairs.push_back({u,v});
 vector<array<int,6>> perms;array<int,6> pp{0,1,2,3,4,5};do{perms.push_back(pp);}while(next_permutation(pp.begin(),pp.end()));
 long long valid_count=0;auto start=chrono::steady_clock::now();
 for(int c=0;c<T;c++){
  if(id[c]>=0)continue;int a[6][6]={};a[0][1]=a[1][0]=2;int cc=c;
  for(int j=1;j<15;j++){auto[u,v]=pairs[j];a[u][v]=a[v][u]=cc%3;cc/=3;}
  bool valid=true;for(int j=0;j<15&&valid;j++){auto[u,v]=pairs[j];if(a[u][v]!=2)continue;
   for(int k=j+1;k<15;k++){auto[x,y]=pairs[k];if(a[x][y]!=2||u==x||u==y||v==x||v==y)continue;
    if(a[u][x]+a[u][y]+a[v][x]+a[v][y]==0){valid=false;break;}}}
  if(!valid)continue;int reached=3,last=0;while(reached!=last){last=reached;for(int u=0;u<n;u++)if(reached>>u&1)for(int v=0;v<n;v++)if(a[u][v])reached|=1<<v;}
  if(reached!=63)continue;int ix=reps.size();reps.push_back(c);
  for(auto&p:perms){if(a[p[0]][p[1]]!=2)continue;int z=0,mul=1;for(int j=1;j<15;j++){auto[u,v]=pairs[j];z+=mul*a[p[u]][p[v]];mul*=3;}
   if(id[z]<0){id[z]=ix;valid_count++;}else if(id[z]!=ix){cerr<<"orbit collision";return 2;}}
 }
 ofstream bin("strong_clique/flags/order6_orbit_index.bin",ios::binary);bin.write((char*)id.data(),id.size()*sizeof(id[0]));
 ofstream out("strong_clique/flags/order6_representatives.json");out<<"[";for(int i=0;i<(int)reps.size();i++)out<<(i?",":"")<<reps[i];out<<"]\n";
 cerr<<"raw_valid="<<valid_count<<" orbits="<<reps.size()<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
