// Exact enumeration in the nonnegative chamber of the posted Q28 polar.
// Build: g++ -O2 -std=c++17 enumerate_chamber.cpp -o enumerate_chamber
// Run: ./enumerate_chamber > chamber_vertices_raw.txt
// No floating-point arithmetic. Determinants use fraction-free Bareiss elimination.
#include <array>
#include <cassert>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <vector>
using I = __int128_t;
using Mat = std::array<std::array<I,5>,5>;
// Nonnegative chamber: ten unsigned original inequalities plus -x_j <= 0.
const long long A[14][5] = {
{18,0,0,0,1},{0,0,30,0,1},{0,0,0,30,1},
{0,5,0,25,1},{0,0,18,18,1},{0,0,18,0,-1},
{0,30,0,0,-1},{30,0,0,0,-1},{25,0,0,5,-1},{18,18,0,0,-1},
{-1,0,0,0,0},{0,-1,0,0,0},{0,0,-1,0,0},{0,0,0,-1,0}};
const long long RHS[14] = {1,1,1,1,1,1,1,1,1,1,0,0,0,0};

I det(Mat a) {
  I prev=1; int sign=1;
  for(int k=0;k<4;++k){
    int p=k; while(p<5 && a[p][k]==0) ++p;
    if(p==5) return 0;
    if(p!=k){std::swap(a[p],a[k]);sign=-sign;}
    I pivot=a[k][k];
    for(int i=k+1;i<5;++i) {
      for(int j=k+1;j<5;++j){
        I x=a[i][j]*pivot-a[i][k]*a[k][j];
        assert(x%prev==0); a[i][j]=x/prev;
      }
      a[i][k]=0;
    }
    prev=pivot;
  }
  return sign*a[4][4];
}
int main(){
  std::map<std::array<long long,6>, std::array<int,5>> verts;
  long long total=0, singular=0, infeasible=0, feasible=0;
  for(int i0=0;i0<10;++i0) for(int i1=i0+1;i1<11;++i1)
  for(int i2=i1+1;i2<12;++i2) for(int i3=i2+1;i3<13;++i3)
  for(int i4=i3+1;i4<14;++i4){
    ++total; std::array<int,5> ix={i0,i1,i2,i3,i4}; Mat m;
    for(int i=0;i<5;++i)for(int j=0;j<5;++j)m[i][j]=A[ix[i]][j];
    I den=det(m); if(den==0){++singular;continue;}
    std::array<I,5> nums;
    for(int j=0;j<5;++j){Mat b=m;for(int i=0;i<5;++i)b[i][j]=RHS[ix[i]];nums[j]=det(b);}
    if(den<0){den=-den;for(auto &v:nums)v=-v;}
    bool ok=true;
    for(int i=0;i<14;++i){I s=0;for(int j=0;j<5;++j)s+=A[i][j]*nums[j];if(s>den*RHS[i]){ok=false;break;}}
    if(!ok){++infeasible;continue;} ++feasible;
    assert(den < (I(1)<<60));
    long long g=(long long)den;
    for(I v:nums){assert(v>-(I(1)<<60)&&v<(I(1)<<60));g=std::gcd(g,(long long)v);}
    std::array<long long,6> key;
    for(int j=0;j<5;++j)key[j]=(long long)(nums[j]/g);key[5]=(long long)(den/g);
    verts.emplace(key,ix);
  }
  std::cerr << "bases "<<total<<" singular "<<singular<<" infeasible "<<infeasible
            <<" feasible "<<feasible<<" distinct_vertices "<<verts.size()<<"\n";
  for(auto const& [v,ix]:verts){for(auto x:v)std::cout<<x<<' ';for(auto i:ix)std::cout<<i<<' ';std::cout<<'\n';}
}
