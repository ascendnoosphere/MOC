# Erdős #1020: exact shifted core and the full-strength deficit still needed

**Status:** the finite-core reduction, extension formula, and conditional induction below are proved. The two-point deficit inequality is unproved and is equivalent, inductively, to the full target. This is not a proof of the Erdős matching conjecture, and the finite LP witness is not a counterexample to that conjecture.

Let r,k>=2 and n>=rk. The cases r=1 or k=1 are immediate. For an r-uniform family with no k disjoint members, the desired bound is
\[
|\mathcal F|\le\max\left\{\binom{rk-1}{r},\binom nr-\binom{n-k+1}{r}\right\}.
\]
Write A<=B for coordinatewise comparison of increasingly ordered r-subsets. Standard shifting preserves cardinality and cannot increase matching number. Thus it suffices to consider order ideals under this comparison.

## 1. Exact core on q=rk vertices

Put q=rk. For A={a_1<...<a_r} in [n], define
\[
\pi(A)_i=\min(a_i,q-r+i).
\]
This is the largest r-subset of [q] below A. If H is a shifted family in binom([q],r), set
\[
L_n(H)=\{A\in\tbinom{[n]}r:\pi(A)\in H\}.
\]

**Lemma.** L_n(H) has no k disjoint members if and only if H contains no partition of [q] into k members.

**Proof.** One direction uses H subset L_n(H). For the other, suppose A_1,...,A_k are disjoint members of L_n(H). Replace the j-th smallest vertex of their q-element union by j. The resulting B_1,...,B_k partition [q]. Each B_i is below A_i and is a subset of [q], hence is below pi(A_i). Shiftedness puts every B_i in H, a contradiction. ∎

Every shifted F is contained in L_n(F intersect binom([q],r)), since pi(A)<=A. Thus maximizing over these extensions loses no admissible family.

For a core edge A let t(A) be the length of its terminal consecutive block ending at q. Put b_t=|{A in H:t(A)=t}|. A matching-free ideal has b_r=0, because the largest r-set generates the entire core. Writing N=n-q, direct counting gives
\[
\boxed{W_H(N):=|L_{q+N}(H)|
 =\sum_{t=0}^{r-1}b_t\binom{N+t}{t}.}\tag{1}
\]
Indeed, a core edge with terminal block length t has its first r-t coordinates fixed in every preimage. The last t coordinates are an arbitrary t-subset of [q-t+1,q+N], giving the displayed binomial coefficient.

Averaging over uniform partitions of [q] into k blocks gives
\[
|H|\le\frac{k-1}{k}\binom qr=\binom{q-1}{r}=:C.
\tag{2}
\]

## 2. The exact two-point deficit assertion

Let
\[
S(n)=\binom nr-\binom{n-k+1}{r},\quad
T=\max\{N\ge0:S(q+N)\le C\},\quad D=C-|H|.
\]
For r,k>=2, T exists and is finite: the star family proves S(q)<=C, whereas S(n) is eventually unbounded.

The missing assertion for every matching-free shifted H is
\[
\boxed{
D\ge\max\left\{
\sum_{t=1}^{r-1}b_t\left[\binom{T+t}{t}-1\right],\quad
\sum_{t=1}^{r-1}b_t\left[\binom{T+1+t}{t}-1\right]
 -[S(q+T+1)-C]
\right\}.
}\tag{3}
\]
These are exactly W_H(T)<=C and W_H(T+1)<=S(q+T+1).

### Why the two points suffice, assuming the lower-rank conjectures

For t>=1, the prefixes counted by b_t form an (r-t)-uniform family G_t on [q-t-1] with no k disjoint members. Otherwise k disjoint prefixes could be completed with the remaining kt core vertices, and every completed edge is below its prefix together with the top t vertices, producing a forbidden core partition.

Let d=r-t and m=q-t-1. Applying the target at the smaller rank d gives
\[
b_t\le s_t:=\binom{q-t-1}{r-t}-\binom{q-t-k}{r-t}.\tag{4}
\]
The star term does dominate the lower-rank clique term here. Indeed m>=(d+1)k-2, and at m_0=(d+1)k-2 one has
\[
\binom{m_0}{d}\ge2\binom{dk-1}{d}.
\]
To check this, compare the factors
\[
1+\frac{k-1}{dk-1-i}\ \ge\ 1+\frac1{2d-1-i},\qquad0\le i<d.
\]
Their product on the right is 2; the factor inequality is equivalent to (k-2)(d-1-i)>=0. Increasing m only increases the star term.

The coefficients s_t, including the analogous s_0, are precisely the terminal-block counts for the core family meeting [k-1]. Hence
\[
S(q+N)-W_H(N)
=(s_0-b_0)+\sum_{t=1}^{r-1}(s_t-b_t)\binom{N+t}{t}
\]
is nondecreasing in N by (4). The second inequality in (3) therefore propagates to all N>=T+1. The first propagates to all N<=T because W_H is nondecreasing.

Thus proving (3) for all r,k proves the complete conjecture by induction on rank. Conversely, the conjecture applied to the exact extensions implies (3). This reduces the necessary ground-set sizes, but does not supply the missing estimate.

## 3. Integer generator compatibility, not just average matching constraints

For two core edges A,B and 1<=h<k, form the q coordinates of h copies of A and k-h copies of B. Sort them as d_1<=...<=d_q. If
\[
d_i\ge i\quad(1\le i\le q),\tag{5}
\]
the two principal shifted ideals together contain a perfect matching. Assign vertex i to the slot with the i-th smallest deadline d_i, then group slots by their originating generator. Each resulting edge is below its generator.

Therefore any matching-free ideal satisfies
\[
\mathbf1_H(A)+\mathbf1_H(B)\le1\tag{6}
\]
whenever (5) holds for some h. More generally the same test applies to any multiset of k generators. Conversely, a perfect matching dominated by those generators yields the same deadline condition, so this is an exact scheduling criterion for that specified generator multiset.

The conditions carry genuinely integer information that is absent from first-moment partition inequalities.

## 4. Exact fractional obstruction to the first-moment relaxation

Take (r,k,n)=(3,4,13), so q=12 and the conjectured bound is 166. On the core define
\[
U=\{A:a_1\le3\text{ or }a_2\le7\text{ or }a_3\le11\},\quad
S=\{A:a_1\le3\},\quad J=\{A:a_2\le3\},
\]
\[
x_A=(3\mathbf1_U(A)+\mathbf1_S(A)+\mathbf1_J(A))/5.
\]
This is shifted, lies between zero and one, and vanishes on the forbidden diagonal a_i>=4i. For every partition P of [12] into four triples,
\[
\sum_{A\in P}(\mathbf1_S(A)+\mathbf1_J(A))\le3,
\]
because each summand is at most |A intersect [3]|. Consequently sum_(A in P) x_A<=3: every ordinary perfect-partition inequality holds.

The weighted extension sizes at N=1 are
\[
W_U=234,\qquad W_S=166,\qquad W_J=31,
\]
so the relaxed objective is
\[
\boxed{W_x=(3\cdot234+166+31)/5=899/5>166.}\tag{7}
\]
But A=(3,11,12), B=(9,10,11), with one copy of A and three of B, satisfy (5). A genuine matching-free ideal therefore obeys (6), whereas this witness has x_A+x_B=4/5+3/5=7/5.

This explains a concrete failure of shiftedness plus all average partition constraints. It is not a failure of the conjecture, because x is fractional, not the indicator of an admissible family.

## Remaining full target

Derive (3) uniformly from integer, globally compatible generator constraints, or find a valid counterexample. Neither the finite-core reformulation, the exact fractional witness, nor finitely many sharp LP certificates establish that uniform deficit inequality.
