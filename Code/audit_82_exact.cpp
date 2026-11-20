#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <vector>

using Matrix = std::array<std::array<long long,14>,14>;
using Perm = std::array<int,4>;
using Mask = uint32_t;
int count(Mask x) { return __builtin_popcount(x); }
int indexbit(Mask x) { return __builtin_ctz(x); }
long long det(Matrix a, int n) {
 if(n==0) return 1;
 int sign=1;
 long long divisor=1;
 for(int k=0;k+1<n;k++){
  int row=k;
  while(row<n && a[row][k]==0)row++;
  if(row==n)return 0;
  if(row!=k){std::swap(a[k],a[row]);sign=-sign;}
  long long pivot=a[k][k];
  for(int i=k+1;i<n;i++)for(int j=k+1;j<n;j++){
   long long numerator=pivot*a[i][j]-a[i][k]*a[k][j];
   assert(numerator%divisor==0);
   a[i][j]=numerator/divisor;
  }
  divisor=pivot;
 }
 return sign*a[n-1][n-1];
}
Mask next(Mask x) {
 Mask c=x & -x, r=x+c;
 return r | (((r^x)>>2)/c);
}
int moment(Perm p, int i, int j) {
 int image=0;
 for(int x=0;x<4;x++) if(j&(1<<x))image |= 1<<p[x];
 return int(image==i);
}
int main(){
 std::vector<Perm> original;
 Perm p{0,1,2,3};
 do {original.push_back(p);} while(std::next_permutation(p.begin(),p.end()));
 std::vector<int> order{0,1,2,3,4,6,7,8,9,10,12,13,16,18};
 for(int x=0;x<24;x++)if(std::find(order.begin(),order.end(),x)==order.end())order.push_back(x);
 std::vector<Perm> ps;for(int x:order)ps.push_back(original[x]);
 const int singleton_indices[9]={0,5,10,15,7,12,1,14,6};
 int B[14][24];
 for(int i=0;i<24;i++){
  B[0][i]=1;
  for(int j=0;j<9;j++){
   int v=singleton_indices[j];B[j+1][i]=moment(ps[i],1<<(v/4),1<<(v%4));
  }
  B[10][i]=moment(ps[i],12,10);B[11][i]=moment(ps[i],12,12);
  B[12][i]=moment(ps[i],5,10);B[13][i]=moment(ps[i],5,12);
 }
 Matrix base{};
 for(int i=0;i<14;i++)for(int j=0;j<14;j++)base[i][j]=B[i][j];
 long long scale=det(base,14);assert(scale==1 || scale==-1);
 int N[14][10];
 for(int i=0;i<14;i++)for(int j=0;j<10;j++){
  Matrix tmp=base;
  for(int k=0;k<14;k++)tmp[k][i]=B[k][14+j];
  N[i][j]=int(det(tmp,14)/scale);
  assert(std::abs(N[i][j])<=2);
 }
 constexpr Mask all=(1u<<24)-1, pivs=(1u<<14)-1;
 std::vector<int8_t> sign(1u<<24);
 int num14=0;
 for(Mask w=(1u<<14)-1;w<=all;w=next(w)){
  int ii[14],jj[14],k=0,h=0;
  for(Mask z=pivs & ~w;z;z &= z-1)ii[k++]=indexbit(z);
  for(Mask z=w>>14;z;z &= z-1)jj[h++]=indexbit(z);
  assert(h==k);
  int inv=0;
  for(int a=0;a<k;a++)inv+=13-ii[a]-(k-1-a);
  Matrix small{};
  for(int a=0;a<k;a++)for(int b=0;b<k;b++)small[a][b]=N[ii[a]][jj[b]];
  long long d=det(small,k);
  int s=(d>0)-(d<0);
  sign[w]=(inv%2 ? -s:s);
  ++num14;
 }
 std::set<Mask> found,expected;
 int num13=0;
 for(Mask w=(1u<<13)-1;w<=all;w=next(w)){
  ++num13;int s=0;Mask zers=w;bool both=false;
  for(Mask z=all & ~w;z;z &= z-1){
   Mask c=z & -z; int j=indexbit(c);int d=sign[w|c];
   if(!d){zers|=c;continue;}
   if(count(w>>(j+1))%2)d=-d;
   if(s && s!=d){both=true;break;}s=d;
  }
  if(!both && s)found.insert(zers);
 }
 auto ray=[&](auto eval){
  Mask z=0;
  for(int i=0;i<24;i++){
   int v=eval(ps[i]);assert(v>=0);if(!v)z|=1u<<i;
  }
  expected.insert(z);
 };
 for(int i=1;i<16;i++)for(int j=1;j<16;j++)
  if((count(i)==1 || count(i)==2) && count(i)==count(j))ray([&](Perm g){return moment(g,i,j);});
 for(Perm r:ps)for(Perm t:ps){
  int a=1<<r[0],b=1<<r[1],c=1<<r[2],e=1<<t[0],f=1<<t[1],g=1<<t[2],h=1<<t[3];
  ray([&](Perm p){return moment(p,c,g)+moment(p,b,h)+moment(p,a|b,e|g)-moment(p,a|c,f|g);});
 }
 std::cout<<"14-subsets "<<num14<<"; 13-subsets "<<num13<<"; exact facets "<<found.size()<<"; stated facets "<<expected.size()<<"\n";
 assert(found==expected && found.size()==82);
}
