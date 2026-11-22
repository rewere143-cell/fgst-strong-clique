/* Fresh C implementation of reverse union projection. No production imports.
 * CRT declarations allow the installed Lean clang to compile without C headers.
 * Run with cwd full/ (all consumed original files are read-only).
 */
#include "c_runtime.h"
static void need(int ok,const char* msg){if(!ok){printf("FAIL %s\n",msg);exit(1);}}
static void *load(const char *path,SZ width,SZ expected){
 FILE *f=fopen(path,"rb");need(f!=0,path);fseek(f,0,2);long bytes=ftell(f);fseek(f,0,0);
 need(bytes>=0 && (SZ)bytes==width*expected,"binary size");void *p=malloc((SZ)bytes);need(p!=0,"malloc");
 need(fread(p,width,expected,f)==expected,"read");fclose(f);return p;
}
typedef struct {U64 *key;int *val;SZ cap,entries;} Hash;
static SZ mix(U64 x){x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;x*=0x94d049bb133111ebULL;return (SZ)(x^(x>>31));}
static Hash mkhash(SZ cap){Hash h;h.cap=cap;h.entries=0;h.key=calloc(cap,8);h.val=calloc(cap,4);need(h.key&&h.val,"hash allocation");return h;}
static SZ find(Hash *h,U64 key){U64 k=key+1;SZ p=mix(k)&(h->cap-1);while(h->key[p]&&h->key[p]!=k)p=(p+1)&(h->cap-1);return p;}
static void insert(Hash*h,U64 key,int val){SZ p=find(h,key);need(!h->key[p],"duplicate sparse key");h->key[p]=key+1;h->val[p]=val;h->entries++;}
static void adjust(Hash*h,U64 key,int delta,int gram){SZ p=find(h,key);need(h->key[p]!=0,"unexpected nonzero reconstructed coefficient");if(gram)need(h->val[p]>0,"Gram multiplicity exhausted");h->val[p]+=delta;}
static void zero(Hash*h,const char*name){SZ nz=0;for(SZ p=0;p<h->cap;p++)if(h->key[p]&&h->val[p]){if(!nz)printf("First mismatch %s key=%llu remainder=%d\n",name,h->key[p]-1,h->val[p]);nz++;}need(nz==0,name);}
static int pow3[15],count[7],*idx[7];
static int project(int a[6][6],const int *v,int n){int c=0,t=0;for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){if(i==0&&j==1)continue;c+=a[v[i]][v[j]]*pow3[t++];}return c;}
typedef struct {int k,type,m,offset;int *lookup[6];} Block;
static Block blocks[57];
static int group[5][244][3],groupsize[5][244];
static int *degree_row[6];
int main(void){
 const int N=23789;const char*dir="data/";(void)dir;
 need(sizeof(int)==4&&sizeof(U64)==8,"integer widths");unsigned endian=1;need(*(char*)&endian==1,"little-endian");
 pow3[0]=1;for(int i=1;i<15;i++)pow3[i]=3*pow3[i-1];
 for(int n=2;n<=6;n++)count[n]=pow3[n*(n-1)/2-1];
 idx[3]=load("data/idx3.bin",4,count[3]);idx[4]=load("data/idx4.bin",4,count[4]);idx[5]=load("data/idx5.bin",4,count[5]);idx[6]=load("data/order6_orbit_index.bin",4,count[6]);
 FILE*f=fopen("data/basis.txt","r");need(f!=0,"basis");int vars,B;need(fscanf(f,"%d %d",&vars,&B)==2&&vars==N&&B==57,"basis shape");int offset=0;
 for(int b=0;b<B;b++){Block*z=&blocks[b];need(fscanf(f,"%d %d %d",&z->k,&z->type,&z->m)==3,"basis header");need(z->k>=2&&z->k<=4&&z->type>=0&&z->type<244&&z->m>0,"basis range");z->offset=offset;offset+=z->m*z->m;int gs=groupsize[z->k][z->type]++;need(gs<3,"group capacity");group[z->k][z->type][gs]=b;
  for(int i=0;i<z->m;i++){int n,c;need(fscanf(f,"%d %d",&n,&c)==2&&n>=z->k&&n<=5&&c>=0&&c<count[n],"basis flag");if(!z->lookup[n]){z->lookup[n]=malloc(4*(SZ)count[n]);need(z->lookup[n]!=0,"basis allocation");for(int t=0;t<count[n];t++)z->lookup[n][t]=-1;}need(z->lookup[n][c]<0,"duplicate basis entry");z->lookup[n][c]=i;}
 }need(offset==326281,"Gram shape");fclose(f);
 U64*keys=load("data/keys.bin",8,1895405);int*vals=load("data/values.bin",4,1895405);Hash gram=mkhash(1ULL<<22);
 for(SZ j=0;j<1895405;j++){need(keys[j]<(U64)offset*N&&vals[j]>0,"Gram sparse range");insert(&gram,keys[j],vals[j]);}free(keys);free(vals);
 keys=load("data/degree_keys.bin",8,433899);vals=load("data/degree_values.bin",4,433899);Hash degree=mkhash(1ULL<<20);
 for(SZ j=0;j<433899;j++){need(keys[j]<3516ULL*N&&vals[j]!=0,"degree sparse range");insert(&degree,keys[j],vals[j]);}free(keys);free(vals);
 for(int n=2;n<=5;n++){degree_row[n]=malloc(6*4*(SZ)count[n]);need(degree_row[n]!=0,"degree allocation");for(int j=0;j<6*count[n];j++)degree_row[n][j]=-1;}
 f=fopen("data/degree.txt","r");need(f!=0,"degree bases");int dn;need(fscanf(f,"%d",&dn)==1&&dn==3516,"degree shape");
 for(int row=0;row<dn;row++){int k,c,u;need(fscanf(f,"%d %d %d",&k,&c,&u)==3&&k>=2&&k<=5&&c>=0&&c<count[k]&&u>=0&&u<k,"degree base");int p=c*6+u;need(degree_row[k][p]<0,"duplicate degree base");degree_row[k][p]=row;if(k>2){int q=idx[k][c];need(q>=0&&q<N,"degree coordinate");adjust(&degree,(U64)row*N+q,1,0);}}
 fclose(f);U64 matches=0,valid=0,degree_extensions=0;int root[6]={0,1,2,3,4,5};
 for(int n=3;n<=6;n++){
  U64 nv=0;for(int code=0;code<count[n];code++){
   if(idx[n][code]<0)continue;int q=idx[n][code]+(n==6?728:0);need(q>=0&&q<N,"union coordinate");nv++;int a[6][6]={{0}},x=code;a[0][1]=a[1][0]=2;
   for(int i=0;i<n;i++)for(int j=i+1;j<n;j++)if(i!=0||j!=1){a[i][j]=a[j][i]=x%3;x/=3;}
   int prefix=project(a,root,n-1);for(int u=0;u<n-1;u++){int row=degree_row[n-1][prefix*6+u];if(row>=0&&a[u][n-1]){adjust(&degree,(U64)row*N+q,-1,0);degree_extensions++;}}
   for(int k=2;k<=4&&k<=n;k++){int type=project(a,root,k);for(int g=0;g<groupsize[k][type];g++){Block*z=&blocks[group[k][type][g]];
     for(int ni=k;ni<=5&&ni<=n;ni++){int nj=n+k-ni;if(nj<k||nj>5||!z->lookup[ni]||!z->lookup[nj])continue;int c1=project(a,root,ni),i=z->lookup[ni][c1];if(i<0)continue;
      int v2[6];for(int t=0;t<k;t++)v2[t]=t;for(int t=ni;t<n;t++)v2[k+t-ni]=t;int c2=project(a,v2,nj),j=z->lookup[nj][c2];if(j<0)continue;
      U64 key=(U64)(z->offset+i*z->m+j)*N+q;adjust(&gram,key,-1,1);matches++;
     }
    }}
  }valid+=nv;printf("Fresh C union-projection order %d: %llu admissible labeled patterns checked\n",n,nv);
 }
 zero(&degree,"degree coefficients");zero(&gram,"Gram coefficients");
 printf("PASS fresh independent C implementation: %llu indexed labeled patterns; 3516 degree rows (%llu sparse coefficients, %llu extension contributions); 1895405 Gram nonzeros (%llu full-union contributions); all zero entries agree.\n",valid,degree.entries,degree_extensions,matches);
 printf("{\"all_passed\":true,\"valid_labeled_patterns\":%llu,\"degree_rows\":3516,\"degree_nonzeros\":%llu,\"gram_nonzeros\":1895405,\"gram_union_contributions\":%llu,\"all_zero_entries_agree\":true}\n",valid,degree.entries,matches);
 return 0;
}
