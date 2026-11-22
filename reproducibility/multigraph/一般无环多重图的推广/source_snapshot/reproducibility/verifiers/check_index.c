/* Exhaustive independent six-position admissibility and orbit audit.
 * The validity predicate uses 45 disjoint-edge masks, then host reachability.
 * For each stored class, its orbit is regenerated with all 720 permutations.
 */
#include "c_runtime.h"
static void need(int ok, const char *s) { if (!ok) { printf("FAIL %s\n",s); exit(1); } }
enum { TOTAL=4782969, ORBITS=23061 };
static int eu[15], ev[15], powers[14], perms[720][6], np;
static void permute(int *p,int at) {
 if(at==6){ for(int j=0;j<6;j++)perms[np][j]=p[j];np++;return; }
 for(int j=at;j<6;j++){int t=p[j];p[j]=p[at];p[at]=t;permute(p,at+1);t=p[j];p[j]=p[at];p[at]=t;}
}
static void decode(int code,int a[6][6]) {
 a[0][1]=a[1][0]=2;
 for(int e=1;e<15;e++){a[eu[e]][ev[e]]=a[ev[e]][eu[e]]=code%3;code/=3;}
}
int main(void){
 need(sizeof(int)==4&&sizeof(U64)==8,"integer widths");
 unsigned endian=1;need(*(char*)&endian==1,"this C implementation requires little endian");
 FILE *f=fopen("data/order6_orbit_index.bin","rb");need(f!=0,"open index");
 need(fseek(f,0,2)==0&&ftell(f)==4L*TOTAL&&fseek(f,0,0)==0,"index size");
 int *ids=malloc(4*(SZ)TOTAL),*first=malloc(4*(SZ)ORBITS),*cnt=calloc(ORBITS,4),*seen=calloc(TOTAL,4);
 need(ids&&first&&cnt&&seen,"allocation");need(fread(ids,4,TOTAL,f)==TOTAL,"read index");fclose(f);
 for(int i=0;i<ORBITS;i++)first[i]=-1;
 int e=0;for(int u=0;u<6;u++)for(int v=u+1;v<6;v++){eu[e]=u;ev[e++]=v;}
 powers[0]=1;for(int j=1;j<14;j++)powers[j]=3*powers[j-1];
 int badmark[45],crosshost[45],pairs=0;
 for(int e=0;e<15;e++)for(int f=e+1;f<15;f++){
  int a=eu[e],b=ev[e],c=eu[f],d=ev[f];if(a==c||a==d||b==c||b==d)continue;
  int cross=0;for(int g=0;g<15;g++){
   int u=eu[g],v=ev[g];
   if(((u==a||u==b)&&(v==c||v==d))||((v==a||v==b)&&(u==c||u==d)))cross|=1<<g;
  }
  need(pairs<45,"pair capacity");badmark[pairs]=(1<<e)|(1<<f);crosshost[pairs++]=cross;
 }
 need(pairs==45,"pair census");U64 valid=0;
 for(int code=0;code<TOTAL;code++){
  int a[6][6]={{0}},adj[6]={0},host=0,mark=0;decode(code,a);
  for(int e=0;e<15;e++){int z=a[eu[e]][ev[e]];if(z){host|=1<<e;adj[eu[e]]|=1<<ev[e];adj[ev[e]]|=1<<eu[e];}if(z==2)mark|=1<<e;}
  int ok=1;for(int j=0;j<45;j++)if((mark&badmark[j])==badmark[j]&&!(host&crosshost[j])){ok=0;break;}
  if(ok){int reach=1,old;do{old=reach;for(int u=0;u<6;u++)if(reach&(1<<u))reach|=adj[u];}while(reach!=old);ok=reach==63;}
  int id=ids[code];need(ok==(id>=0),"validity mismatch");
  if(!ok){need(id==-1,"negative sentinel");continue;}
  need(id<ORBITS,"orbit range");cnt[id]++;valid++;if(first[id]<0)first[id]=code;
 }
 int p[6]={0,1,2,3,4,5};permute(p,0);need(np==720,"permutations");U64 members=0;
 for(int id=0;id<ORBITS;id++){
  need(first[id]>=0,"empty orbit");int a[6][6]={{0}},size=0;decode(first[id],a);
  for(int j=0;j<720;j++){
   int *p=perms[j];if(a[p[0]][p[1]]!=2)continue;int code=0;
   for(int e=1;e<15;e++)code+=powers[e-1]*a[p[eu[e]]][p[ev[e]]];
   need(ids[code]==id,"split orbit");if(seen[code]!=id+1){seen[code]=id+1;size++;}
  }
  need(size==cnt[id],"merged orbit");members+=size;
 }
 need(members==valid&&valid==4450424ULL,"census");
 printf("{\"all_passed\":true,\"total_colorings\":4782969,\"valid_connected_colorings\":%llu,\"orbits\":23061,\"orbit_members\":%llu}\n",valid,members);
 return 0;
}
