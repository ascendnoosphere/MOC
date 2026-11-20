#include <gmpxx.h>
#include <array>
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>
using Z=mpz_class;
constexpr int d=13,D=9,n=14;
using Index=std::array<unsigned char,d>;
using X=std::array<long,n>;
using Mat=std::array<X,n>;
using ZM=std::array<std::array<Z,n>,n>;
long A[n][n][n], HE[n][n], fac[10],ch[10][10],stir[10][10];
std::vector<Index> inds;
std::vector<uint64_t> keys;
std::unordered_map<uint64_t,int> where;
std::vector<Z> data;
static int degree(const Index &v){int n=0;for(auto t:v)n+=t;return n;}
void enumerate(Index &v,int layer,int budget,uint64_t key){
 if(layer==d){where[key]=inds.size();inds.push_back(v);keys.push_back(key);return;}
 for(int i=0;i<=budget;i++){v[layer]=i;enumerate(v,layer+1,budget-i,key+(uint64_t(i)<<(4*layer)));}
}
void exactdiv(Z &x,const Z &y){mpz_divexact(x.get_mpz_t(),x.get_mpz_t(),y.get_mpz_t());}
Z det(ZM &a){
 int sign=1;Z temp,prev=1;
 for(int k=0;k<n-1;k++){int p=k;while(p<n && a[p][k]==0)++p;
  if(p==n)return 0;
  if(p!=k){std::swap(a[p],a[k]);sign=-sign;}
  for(int i=k+1;i<n;i++)for(int j=k+1;j<n;j++){
   temp=a[i][j]*a[k][k];
   mpz_submul(temp.get_mpz_t(),a[i][k].get_mpz_t(),a[k][j].get_mpz_t());
   if(k)exactdiv(temp,prev);
   std::swap(a[i][j],temp);
  }
  prev=a[k][k];
 }
 return sign*a[n-1][n-1];
}
Z oriented_nonic(const Index &v){
 X h{},hp{};for(int i=0;i<d;i++)h[i]=11*v[i];h[d]=2;
 Mat H{};
 for(int i=0;i<n;i++)for(int j=0;j<n;j++){
  long val=2*A[i][j][d];for(int k=0;k<d;k++) val+=h[k]*A[i][j][k];H[i][j]=val;hp[i]+=val*h[j];
 }
 long fq=0,qq=0;for(int i=0;i<n;i++){fq+=h[i]*hp[i];qq+=hp[i];}
 if(fq%6 || qq%2){std::cerr<<"bad cubic normalization";exit(2);}
 long f=fq/6,q=qq/2;
 if(q%11==0){std::cerr<<"bad q";exit(2);}
 ZM m;
 for(int i=0;i<n;i++)for(int j=0;j<n;j++)m[i][j]=(long)(q*H[i][j]-f*HE[i][j]);
 Z val=-det(m);
 Z qz(q);for(int i=0;i<12;i++){if(!mpz_divisible_p(val.get_mpz_t(),qz.get_mpz_t())){std::cerr<<"inexact Q division";exit(2);}exactdiv(val,qz);}
 Z root,rem;
 if(val<0){std::cerr<<"negative square";exit(2);}
 mpz_sqrtrem(root.get_mpz_t(),rem.get_mpz_t(),val.get_mpz_t());
 if(rem!=0){std::cerr<<"nonsquare";exit(2);}
 unsigned long s=mpz_fdiv_ui(root.get_mpz_t(),11);
 if(s==(1UL<<24)%11)return root;
 if((11-s)==(1UL<<24)%11)return -root;
 std::cerr<<"inconsistent square root";exit(2);
}
void change(int axis,int mode){
 uint64_t unit=1ULL<<(4*axis);
 for(size_t k=0;k<inds.size();k++){
  if(inds[k][axis])continue;
  int m=D-degree(inds[k]);int id[10];Z a[10],b[10];
  for(int j=0;j<=m;j++){id[j]=where.at(keys[k]+j*unit);a[j]=data[id[j]];}
  if(mode==0){
   for(int j=0;j<=m;j++){b[j]=a[0];for(int i=0;i<m-j;i++)a[i]=a[i+1]-a[i];}
  }else if(mode==1){
   for(int j=0;j<=m;j++){for(int u=j;u<=m;u++)b[j]+=a[u]*(fac[9]/fac[u])*stir[u][j];
    if(!mpz_divisible_ui_p(b[j].get_mpz_t(),fac[9])){std::cerr<<"interpolation denominator";exit(2);}
    mpz_divexact_ui(b[j].get_mpz_t(),b[j].get_mpz_t(),fac[9]);}
  }else{
   for(int j=0;j<=m;j++)for(int u=0;u<=j;u++)b[j]+=ch[j][u]*a[u];
  }
  for(int j=0;j<=m;j++)data[id[j]]=std::move(b[j]);
 }
}
int main(int argc,char**argv){
 fac[0]=stir[0][0]=ch[0][0]=1;
 for(int i=1;i<=D;i++){fac[i]=i*fac[i-1];ch[i][0]=ch[i][i]=1;
  for(int j=1;j<i;j++)ch[i][j]=ch[i-1][j-1]+ch[i-1][j];
  for(int j=1;j<=i;j++)stir[i][j]=stir[i-1][j-1]-(i-1)*stir[i-1][j];
 }
 Index v{};enumerate(v,0,D,0);std::cout<<"grid "<<inds.size()<<std::endl;
 if(argc<2)return 1;
 std::string mode=argv[1];
 if(mode=="grid"){
  std::ifstream f("spin_facet_tensor.dat");for(int i=0;i<n;i++)for(int j=0;j<n;j++)for(int k=0;k<n;k++){f>>A[i][j][k];HE[i][j]+=A[i][j][k];}
  std::vector<Z> result(inds.size());
  size_t left=argc>2?std::stoul(argv[2]):0,right=argc>3?std::stoul(argv[3]):inds.size();
  #pragma omp parallel for schedule(static,128)
  for(size_t i=left;i<right;i++){result[i]=oriented_nonic(inds[i]);}
  std::ofstream out(argc>4?argv[4]:"spin_grid.dat");
  for(size_t i=left;i<right;i++)out<<result[i]<<"\n";
 }else if(mode=="coeff"){
  std::ifstream f("spin_grid.dat");Z x;for(size_t i=0;i<inds.size();i++){if(!(f>>x))return 2;data.push_back(x*fac[9]);}
  for(int i=0;i<d;i++)change(i,0);
  for(int i=0;i<d;i++)change(i,1);
  std::ofstream o("spin_coeff.dat");for(auto &u:data)o<<u<<"\n";
 }else if(mode=="bern"){
  if(argc!=16)return 2;
  std::ifstream f("spin_coeff.dat");if(!f)return 2;long den=std::stol(argv[2]);long R[d];for(int j=0;j<d;j++)R[j]=std::stol(argv[3+j]);
  for(size_t i=0;i<inds.size();i++){
   Z x;f>>x;int k=degree(inds[i]);x*=fac[9-k];
   for(int a=0;a<D-k;a++)x*=(11*den);
   for(int j=0;j<d;j++){x*=fac[inds[i][j]];for(int a=0;a<inds[i][j];a++)x*=R[j];}
   data.push_back(x);
  }
  for(int i=0;i<d;i++)change(i,2);
  size_t neg=0,zero=0;Z mn=data[0];size_t at=0;
  for(size_t i=0;i<inds.size();i++){if(data[i]<0)neg++;if(data[i]==0)zero++;if(data[i]<mn){mn=data[i];at=i;}}
  std::cout<<"negative "<<neg<<" zero "<<zero<<" min "<<mn<<" constant "<<data[0]<<" at";
  for(int u:inds[at])std::cout<<" "<<u;std::cout<<std::endl;
  if(neg!=0 || data[0]<=0)return 3;
 }
}
