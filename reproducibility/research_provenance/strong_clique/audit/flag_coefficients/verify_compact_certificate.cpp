// Independent direct-JSON exact certificate verifier. C++17, standard library;
// GCC/Clang __int128 and checked-overflow intrinsics for integer arithmetic.
#include <algorithm>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;using I=__int128_t;
void need(bool x,const string&s){if(!x)throw runtime_error(s);}
I add(I a,I b){I c;need(!__builtin_add_overflow(a,b,&c),"int128 addition overflow");return c;}
I sub(I a,I b){I c;need(!__builtin_sub_overflow(a,b,&c),"int128 subtraction overflow");return c;}
I mul(I a,I b){I c;need(!__builtin_mul_overflow(a,b,&c),"int128 multiplication overflow");return c;}
string dec(I x){if(!x)return "0";bool neg=x<0;need(x!=-(I(1)<<126)-(I(1)<<126),"int128 minimum printing unsupported");if(neg)x=-x;string s;while(x){s.push_back('0'+int(x%10));x/=10;}if(neg)s+='-';reverse(s.begin(),s.end());return s;}
I integer(const string&s){need(!s.empty(),"empty integer");bool neg=s[0]=='-';size_t i=neg?1:0;need(i<s.size(),"bad integer");I x=0;for(;i<s.size();i++){need(s[i]>='0'&&s[i]<='9',"nonintegral numeric value");x=add(mul(x,10),s[i]-'0');}return neg?sub(0,x):x;}
struct J{char kind='?';string text;vector<J> items;map<string,J> fields;const J& at(string k)const{need(kind=='o',"not object");auto p=fields.find(k);need(p!=fields.end(),"missing key "+k);return p->second;}I number()const{need(kind=='n'||kind=='s',"not an integer number/string");return integer(text);}};
struct Parser{string s;size_t p=0;void ws(){while(p<s.size()&&isspace((unsigned char)s[p]))p++;}char take(){need(p<s.size(),"unexpected JSON end");return s[p++];}void expect(char c){ws();need(take()==c,"JSON delimiter mismatch");}
 string str(){expect('"');string out;while(true){char c=take();if(c=='"')return out;need((unsigned char)c>=32,"JSON control char");if(c!='\\'){out+=c;continue;}char e=take();if(e=='"'||e=='\\'||e=='/')out+=e;else if(e=='b')out+='\b';else if(e=='f')out+='\f';else if(e=='n')out+='\n';else if(e=='r')out+='\r';else if(e=='t')out+='\t';else if(e=='u'){unsigned x=0;for(int i=0;i<4;i++){char h=take();unsigned d=h>='0'&&h<='9'?h-'0':h>='a'&&h<='f'?h-'a'+10:h>='A'&&h<='F'?h-'A'+10:99;need(d<16,"bad unicode escape");x=16*x+d;}need(x<128,"non-ASCII unicode escape unsupported");out+=char(x);}else throw runtime_error("bad string escape");}}
 J value(){ws();need(p<s.size(),"missing JSON value");J x;char c=s[p];if(c=='{'){x.kind='o';p++;ws();if(s[p]=='}'){p++;return x;}while(true){string k=str();expect(':');J y=value();need(x.fields.emplace(k,move(y)).second,"duplicate JSON key");ws();char d=take();if(d=='}')break;need(d==',',"object separator");}return x;}if(c=='['){x.kind='a';p++;ws();if(s[p]==']'){p++;return x;}while(true){x.items.push_back(value());ws();char d=take();if(d==']')break;need(d==',',"array separator");}return x;}if(c=='"'){x.kind='s';x.text=str();return x;}if(c=='t'||c=='f'||c=='n'){string lit=c=='t'?"true":c=='f'?"false":"null";need(s.substr(p,lit.size())==lit,"bad literal");p+=lit.size();x.kind='l';x.text=lit;return x;}x.kind='n';size_t begin=p;if(s[p]=='-')p++;need(p<s.size()&&isdigit((unsigned char)s[p]),"bad JSON number");if(s[p]=='0')p++;else while(p<s.size()&&isdigit((unsigned char)s[p]))p++;if(p<s.size()&&s[p]=='.'){p++;need(p<s.size()&&isdigit((unsigned char)s[p]),"bad fractional number");while(p<s.size()&&isdigit((unsigned char)s[p]))p++;}if(p<s.size()&&(s[p]=='e'||s[p]=='E')){p++;if(p<s.size()&&(s[p]=='+'||s[p]=='-'))p++;need(p<s.size()&&isdigit((unsigned char)s[p]),"bad exponent");while(p<s.size()&&isdigit((unsigned char)s[p]))p++;}x.text=s.substr(begin,p-begin);return x;}
 J parse(){J x=value();ws();need(p==s.size(),"trailing JSON content");return x;}};
string readtext(string path){ifstream f(path,ios::binary);need(bool(f),"cannot read "+path);return string(istreambuf_iterator<char>(f),{});}
vector<int64_t> binary(string path,int width){string s=readtext(path);need(s.size()%width==0,"bad binary length");vector<int64_t> out;out.reserve(s.size()/width);for(size_t p=0;p<s.size();p+=width){uint64_t u=0;for(int j=0;j<width;j++)u|=uint64_t((unsigned char)s[p+j])<<(8*j);if(width==4)out.push_back(u>=2147483648ULL?int64_t(u)-4294967296LL:int64_t(u));else{need(u<=uint64_t(INT64_MAX),"negative/oversized sparse key");out.push_back(int64_t(u));}}return out;}
int small(I x,int max,const string&s){need(x>=0&&x<max,s);return int(x);}
int main(int argc,char**argv){try{
 string dir="strong_clique/audit/flag_coefficients/";string cert=argc>1?argv[1]:"strong_clique/flags/sharp_face/compact/compact_R10000_simple_fourdefects_certificate.json";
 J C=Parser{readtext(cert)}.parse();I T=C.at("common_denominator").number(),Q=C.at("weight_denominator").number(),R=C.at("vector_denominator").number();need(T>0&&Q>0&&R>0&&T==mul(Q,mul(R,R)),"invalid denominator relation");need(T%2==0,"odd objective denominator unsupported");
 ifstream f(dir+"basis.txt");need(bool(f),"missing basis");int N,B;f>>N>>B;need(N==23789&&B==57,"unexpected shape");vector<int> sizes,offsets,typeorders;int rows=0;for(int b=0;b<B;b++){int k,t,m;f>>k>>t>>m;need(k>=2&&k<=4&&m>0&&m<=133,"invalid basis block");sizes.push_back(m);offsets.push_back(rows);typeorders.push_back(k);rows+=m*m;for(int i=0;i<m;i++){int n,c;f>>n>>c;need(n>=k&&n<=5&&c>=0,"bad basis flag");if(i==0)need(n==k&&c==t,"type-only flag not first");}need(bool(f),"truncated basis");}need(rows==326281,"Gram shape");
 need(C.at("variables").number()==N&&C.at("psd_blocks").number()==B,"certificate shape");
 ifstream df(dir+"degree.txt");int nr;df>>nr;need(nr==3516&&C.at("equations").number()==nr,"degree shape");vector<I> lambda(nr);vector<int> rhs(nr);map<string,int> names;
 for(int row=0;row<nr;row++){int k,c,u;df>>k>>c>>u;need(bool(df)&&k>=2&&k<=5&&u>=0&&u<k,"invalid degree row");string name="degree_"+to_string(k)+"_(2";int count=k*(k-1)/2-1;for(int j=0;j<count;j++){name+=", "+to_string(c%3);c/=3;}if(!count)name+=",";name+=")_"+to_string(u);need(names.emplace(name,row).second,"duplicate degree name");rhs[row]=k==2;}
 const J &ls=C.at("degree_weights_numerators");need(ls.kind=='o',"lambda not object");I maxlambda=0;for(auto &kv:ls.fields){auto it=names.find(kv.first);need(it!=names.end(),"unknown lambda row "+kv.first);I v=kv.second.number();lambda[it->second]=v;maxlambda=max(maxlambda,v<0?sub(0,v):v);}
 vector<I> gram(rows);const J &factors=C.at("rank_one_factors");need(factors.kind=='a',"factors not array");int positive=0;I maxweight=0,maxvector=0;
 for(const J &factor:factors.items){int b=small(factor.at("block").number(),B,"factor block");I w=factor.at("weight_numerator").number();need(w>=0,"negative rank-one weight");if(w>0)positive++;maxweight=max(maxweight,w);const J &vv=factor.at("vector_numerators");need(vv.kind=='a'&&vv.items.size()==size_t(sizes[b]),"factor vector size");vector<I> v;for(const J &z:vv.items){I x=z.number();v.push_back(x);maxvector=max(maxvector,x<0?sub(0,x):x);}for(int i=0;i<sizes[b];i++)for(int j=0;j<sizes[b];j++){int pos=offsets[b]+i*sizes[b]+j;gram[pos]=add(gram[pos],mul(w,mul(v[i],v[j])));}}
 need(C.at("nonzero_rank_one_factors").number()==positive,"nonzero factor count");
 // Objective independently derived from complete labeled four-flags, not certificate data.
 vector<I> residual(N);auto index4=binary(dir+"idx4.bin",4);need(index4.size()==243,"order-four index length");for(int c=0;c<243;c++)if(index4[c]>=0&&(c/81)%3==2){need(index4[c]<N,"objective variable index");int q=int(index4[c]);residual[q]=sub(residual[q],T/2);}
 I raw=0;for(int i=0;i<nr;i++)raw=add(raw,mul(lambda[i],rhs[i]));for(int b=0;b<B;b++)if(typeorders[b]==2)raw=add(raw,gram[offsets[b]]);
 auto ak=binary(dir+"degree_keys.bin",8),av=binary(dir+"degree_values.bin",4);need(ak.size()==av.size()&&ak.size()==433899,"degree sparse lengths");for(size_t z=0;z<ak.size();z++){int64_t row=ak[z]/N,q=ak[z]%N;need(row>=0&&row<nr&&q>=0&&q<N,"degree sparse index");residual[q]=add(residual[q],mul(lambda[row],av[z]));}
 auto dk=binary(dir+"keys.bin",8),dv=binary(dir+"values.bin",4);need(dk.size()==dv.size()&&dk.size()==1895405,"Gram sparse lengths");for(size_t z=0;z<dk.size();z++){int64_t row=dk[z]/N,q=dk[z]%N;need(row>=0&&row<rows&&q>=0&&q<N&&dv[z]>=0,"Gram sparse index/coefficient");residual[q]=sub(residual[q],mul(gram[row],dv[z]));}
 int strict=0;I maxres=0;for(int q=0;q<N;q++){need(residual[q]>=0,"NEGATIVE residual at "+to_string(q)+": "+dec(residual[q]));if(residual[q])strict++;maxres=max(maxres,residual[q]);}
 need(mul(4,raw)==mul(5,T),"raw value is not 5/4");need(C.at("rounding_correction").number()==0,"nonzero correction claimed");need(C.at("negative_residual_count").number()==0,"negative residual claim");const J &neg=C.at("negative_residual_numerators");need(neg.kind=='o'&&neg.fields.empty(),"negative residual corrections present");need(C.at("rational_bound").text=="5/4"&&C.at("raw_dual_value").text=="5/4","bound claims differ");
 cout<<"PASS: direct JSON; checked int128 arithmetic; nonnegative rank-one weights; all "<<N<<" residuals nonnegative; no corrections; 4*raw=5*T exactly.\n";
 cout<<"T="<<dec(T)<<" Q="<<dec(Q)<<" R="<<dec(R)<<" raw="<<dec(raw)<<" positive_factors="<<positive<<" strict_residuals="<<strict<<" max_residual="<<dec(maxres)<<"\n";
 cout<<"Observed max_weight="<<dec(maxweight)<<" max_abs_vector="<<dec(maxvector)<<" max_abs_lambda="<<dec(maxlambda)<<"\n";
 for(int q=0;q<N;q++)if(residual[q])cout<<"residual["<<q<<"]="<<dec(residual[q])<<"/"<<dec(T)<<"\n";
 return 0;
 }catch(const exception&e){cerr<<"FAIL: "<<e.what()<<"\n";return 1;}}
