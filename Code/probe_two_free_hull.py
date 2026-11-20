import numpy as np
from itertools import permutations, combinations, product
from scipy.spatial import ConvexHull
from scipy.optimize import linprog
from fractions import Fraction
import sympy as s
perms=list(permutations(range(4)))
def coeff(a,b):
 F=[]
 for p in perms:
  v=[]
  for x,y in [(0,0),(1,0),(0,1),(1,1)]:
   q=np.prod([([*a,x][i]+[*b,y][p[i]])for i in range(4)])
   v.append(q)
  d,c,b_,a_=v
  F.append([d,c-d,b_-d,a_-b_-c+d])
 return np.array(F)
def hrows(Z):
 f=ConvexHull(Z)
 eq={}
 for n,h in zip(f.equations,f.simplices):
  ints=tuple(round(v,8) for v in n)
  if ints not in eq:eq[ints]=h
 return list(eq.values())
def hr(Z):
 N=[]
 for ix in hrows(Z):
  l=s.Matrix(np.c_[Z[ix],np.ones(len(ix),int)]).nullspace()
  if not l:continue
  q=np.ravel(np.array(l[0].T* s.ilcm(*[d.q for d in l[0]])),).astype(int)
  val=Z@q[:-1]+q[-1]
  if np.min(val)<0:q=-q
  N.append(q)
 return np.array(N)
if __name__=='__main__':
 for a,b in [([0,1,2],[1,2,3]),([-1,0,1],[-1,0,1]),([0,1,2],[0,2,4]),([0,1,2],[2,4,7])]:
  Z=coeff(a,b)
  H=hr(Z)
  print(a,b,'facets',len(H),'rank1',sum(h[0]*h[3]==h[1]*h[2] for h in H))
I=range(4); prs=list(combinations(I,2))
single=np.array([[p[i]==j for p in perms] for i in I for j in I],int).T
def span(t, trans):
 beta=[0,1,2,t]
 def v(p,ij):
  i,j=ij
  return beta[p[i]]*beta[p[j]]
 B=np.array([[v(tuple(np.argsort(p))if trans else p,ij) for ij in prs] for p in perms])
 Q=s.Matrix(np.c_[single,B])
 ix=Q.rref()[1]
 return np.array(Q[:,ix]).astype(float)
def matrices(ts):
 return [span(t,d)for d in [0,1] for t in ts]
from scipy.linalg import block_diag
def dec(f,L):
 return linprog(np.zeros(sum(M.shape[1]for M in L)),A_ub=-block_diag(*L),b_ub=np.zeros(24*len(L)),A_eq=np.hstack(L),b_eq=f,bounds=(None,None))
if __name__=='__main__':
 L=matrices([-3,-2,-1,0,1,2,3,4,5,6])
 for a,b in [([0,1,2],[1,2,3]),([0,1,2],[2,4,7]),([-1,0,1],[2,3,4]),([-1,0,1],[3,6,7])]:
  Z=coeff(a,b);H=hr(Z)
  bad=[]
  for h in H:
   f=Z@h[:4]+h[4]
   if h[0]*h[3]==h[1]*h[2]:continue
   if not dec(f,L).success:bad.append(tuple(h))
  print(a,b,'uncertified',len(bad),bad[:3],flush=True)
