# Full Rota attack: positive capacity versus the missing central coefficient

**Status:** the capacity bound, entropy formula, and replicated fractional packing below are proved. The multiplicity-one assertion is unproved and is the full conjecture. These statements use standard mixed-discriminant and matroid-intersection theorems; no publication-priority claim is made.

## 1. Exact target for arbitrary linear bases

Let B_i=(v_i1,...,v_in) be arbitrary invertible n-by-n real or complex matrices, and set
\[
\Delta=\prod_i|\det B_i|^2>0,\qquad X=\prod_{i,a}x_{ia}.
\]
Define the nonnegative-coefficient polynomial
\[
p(x)=\sum_{a_1,\ldots,a_n}
|\det(v_{1a_1},\ldots,v_{na_n})|^2\prod_i x_{ia_i}.
\]
Its support consists of the rainbow bases. The exact weighted number of ordered decompositions into n disjoint rainbow bases is
\[
\boxed{Z=[X]p(x)^n.}\tag{1}
\]
Consequently the full linear conjecture is Z>0 for every input, not merely the existence of one rainbow basis.

## 2. A global quantitative capacity bound

For positive x put
\[
G_i=B_i\operatorname{diag}(x_{i1},\ldots,x_{in})B_i^*.
\]
Cauchy–Binet and the generalized mixed-discriminant inequality give
\[
p(x)=[t_1\cdots t_n]\det\Bigl(\sum_i t_iG_i\Bigr)
\ge n!\prod_i(\det G_i)^{1/n}
=n!\Delta^{1/n}X^{1/n}.
\]
Thus
\[
\boxed{\operatorname{Cap}(p^n):=\inf_{x>0}\frac{p(x)^n}{X}
\ge(n!)^n\Delta>0.}\tag{2}
\]
This is valid for arbitrary linear input bases, without independently orthonormalizing them.

For a rainbow basis T, write w(T)=|det(v_T)|^2 and
q_x(T)=w(T)x^T/p(x). Independence gives the exact identity
\[
\Pr_{q_x^{\otimes n}}(\text{disjoint})=\frac{ZX}{p(x)^n},\qquad
\boxed{\sup_{x>0}\Pr_{q_x^{\otimes n}}(\text{disjoint})=
\frac{Z}{\operatorname{Cap}(p^n)}.}\tag{3}
\]
Finite-dimensional entropy duality also gives
\[
\frac1n\log\operatorname{Cap}(p^n)
=\max_{q:\Pr_q(e\in T)=1/n}
\{H(q)+\mathbb E_q\log w(T)\}.
\tag{4}
\]
In particular there is a balanced law with
H(q)+E_q log w(T)>=log(n!)+(log Delta)/n. The entropy statement remains valid if no finite positive scaling attains the capacity infimum.

### Why coefficient extraction is not automatic

Positive capacity says the required exponent belongs to the Newton polytope. It does not say that exponent occurs in the polynomial. The usual real-stable coefficient inequalities cannot simply be applied here: the rainbow polynomial need not be real stable.

For example, when n=2 and B_1=B_2=I,
\[
p=x_{11}x_{22}+x_{12}x_{21}.
\]
Set x_11=x_22=1+i and x_12=x_21=-1+i. All four variables are in the open upper half-plane, but p=0. This is a counterexample to a proposed stability premise, not to Rota.

## 3. The full matroid version has a fractional solution

This part works over every field, and for nonrepresentable matroids as well. Replace repeated input elements with labelled parallel copies and let
E=B_1 disjoint-union ... disjoint-union B_n. Let N be the partition matroid selecting at most one element of each B_i.

The vector u_e=1/n lies in both base polytopes. Indeed
\[
|S|=\sum_i|S\cap B_i|\le n\,r_M(S),
\qquad u(E)=n,\quad u(B_i)=1.
\]
Matroid-intersection integrality yields
\[
u=\sum_T\lambda_T\mathbf1_T,\qquad\lambda_T\ge0,\quad\sum_T\lambda_T=1,
\]
where every T is a rainbow basis. The coefficients can be chosen rational. Clearing denominators proves that for some integer m>=1 there are mn rainbow bases, counted with multiplicity, in which every labelled element occurs exactly m times.

**The missing step is m=1.** With
P=conv{1_T:T is a rainbow basis}, the proved statement is 1_E in nP. The required integer decomposition
\[
\mathbf1_E=\mathbf1_{T_1}+\cdots+\mathbf1_{T_n}
\tag{5}
\]
is exactly the full conjecture. Invoking an unproved integer-decomposition property for this intersection polytope would be circular.

## 4. Diagnostic data, not a lower-dimensional substitute

Ten local searches in dimension three found Z/Delta approximately 3/4. A checked integer configuration is B_1=I and
\[
B_2=\begin{pmatrix}1&1&1\\0&1&-1\\1&-1&-1\end{pmatrix},\qquad
B_3=\begin{pmatrix}1&1&1\\0&1&-1\\-1&1&1\end{pmatrix}.
\]
Here Delta=256 and Z=192. Thus any universal bound Z>=c_3 Delta must have c_3<=3/4. This does not prove that 3/4 is the infimum or that a positive c_n exists for every n.

Sampled modular span tests over F_1009 did not yield a certificate. They are not proofs of polynomial identities or characteristic-zero nonmembership, and no claim above depends on them.

The unresolved full-strength target is positivity of the central coefficient in (1), or equivalently the integral decomposition (5). Global reweighting, positive capacity, and replicated packings do not close that gap.
