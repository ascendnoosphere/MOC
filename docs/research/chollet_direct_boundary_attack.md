# Direct all-dimensional Chollet attack: endpoint reduction and the remaining boundary

**Status:** the endpoint principle and necessary optimality conditions below are proved. The singular boundary inequality is unproved. The Gaussian interpolation is exact, but its proposed monomial-coefficient positivity is **false**, as shown explicitly below. A positive expansion in a different basis still does not compare the endpoints. Neither numerical evidence nor an analogy with determinant couplings is treated as a proof of Chollet. No publication-priority claim is made.

The full two-matrix conjecture is equivalent, by Cauchy–Schwarz on permutation products, to
\[
\operatorname{per}(A\circ\bar A)\le(\operatorname{per}A)^2
\quad(A\succeq0).
\]
Zero diagonal entries force zero rows and make the inequality trivial. Otherwise diagonal congruence reduces to correlation matrices A_ii=1. Write
\[
S=A\circ\bar A,\quad P=\operatorname{per}A,\quad
Q=\operatorname{per}S,\quad R=Q/P^2.
\]
The correlation elliptope is compact. For unit Gram vectors, the creation-operator identity gives
\[
P=\operatorname{per}A_{-i}
 +\left\|a(u_i)\prod_{j\ne i}a^\dagger(u_j)|0\rangle\right\|^2
\ge\operatorname{per}A_{-i}\ge1.
\]
Thus R is continuous everywhere on this compact domain.

## 1. A coordinate has no interior maximum

Fix i and multiply its off-diagonal row and column entries by sqrt(x), leaving the diagonal equal to one. Call the result A_i(x). Put
\[
p=\operatorname{per}A_{-i},\qquad q=\operatorname{per}S_{-i}.
\]
Every non-fixing permutation uses exactly two entries incident to i. Therefore
\[
\operatorname{per}A_i(x)=p+x(P-p),\qquad
\operatorname{per}|A_i(x)|^2=q+x^2(Q-q),
\]
\[
\boxed{
R_i'(x)=\frac{2\{p(Q-q)x-q(P-p)\}}{[p+x(P-p)]^3}.
}
\tag{1}
\]
If row i has a nonzero off-diagonal entry, Q-q>0: its transposition contributes a strictly positive term. Hence the numerator of (1) is strictly increasing. Every interior critical point is a strict minimum, not a maximum.

Reorder i first and write
\[
A=\begin{pmatrix}1&b^*\\b&C\end{pmatrix},\qquad
c=b^*C^\dagger b.
\]
PSD implies b belongs to ran(C) and 0<=c<=1. If b is nonzero then c>0, and the exact feasible interval is
\[
A_i(x)\succeq0\quad\Longleftrightarrow\quad 0\le x\le1/c.
\]
Consequently
\[
\boxed{
R(A)\le\max\{R(C),R(A_i(1/c))\}.
}
\tag{2}
\]
If c<1 and b is nonzero, at least one endpoint is strictly better than A. The second endpoint lowers the rank by one; the first isolates a vector and reduces the problem's size.

**Corollary.** No nonidentity positive-definite correlation matrix is a local maximum of R. The identity itself is a strict local maximum: near I, with Hermitian zero-diagonal E,
\[
R(I+E)=1-2\sum_{i<j}|E_{ij}|^2+O(\|E\|^3).
\]
At any other local maximum, every Gram vector is either orthogonal to all the others or belongs to their span.

The limitation is important: at a singular irreducible matrix, c=1 may hold at every index. Equation (2) then includes the original matrix as an endpoint and is not a decreasing induction.

## 2. Necessary KKT conditions including rank increases

Define the permanent-cofactor matrix with adjugate indexing,
\[
\mathcal C(M)_{ij}=\operatorname{per}M[\widehat j\mid\widehat i],
\qquad C_1=\mathcal C(A),\quad D_1=\mathcal C(S).
\]
Under the real trace pairing on Hermitian matrices,
\[
G=\nabla_A\log R
 =2\left(\frac{A\circ D_1}{Q}-\frac{C_1}{P}\right).
\tag{3}
\]
Rowwise permanent expansion gives, at every A,
\[
\boxed{(AG)_{ii}=0.}\tag{4}
\]
Indeed (AC_1)_ii=P and [A(A circ D_1)]_ii=Q.

At a local maximum, add epsilon z z* and normalize the diagonal. The first derivative is z*Gz, because the normalization terms vanish by (4). Hence G<=0. Also tr(AG)=0, so PSD implies AG=0. Equivalently,
\[
\boxed{
K:=\frac{C_1}{P}-\frac{A\circ D_1}{Q}\succeq0,\qquad AK=0.
}\tag{5}
\]
This necessary condition includes rank-increasing directions. Fixed-rank Gram stationarity alone would only give XG=0 for A=X*X, which is weaker.

Suppose n is the smallest dimension admitting a counterexample, and take a global maximizer with R>1. It is singular, is orthogonally indecomposable, and has no Gram vector outside the span of the others. With
\[
p_i=\operatorname{per}A_{-i},\quad q_i=\operatorname{per}S_{-i},
\quad t_i=p_i/P\in(0,1],
\]
minimality gives q_i<=p_i^2, and thus
\[
\boxed{K_{ii}=t_i-q_i/Q\ge t_i-t_i^2/R>0.}\tag{6}
\]
A PSD K with positive diagonal can still annihilate the range of a singular A. That fact alone is not a contradiction. Excluding the specific cofactor matrix (5) at R>1 is an unresolved boundary problem.

## 3. Gaussian averaging: an exact full-strength endpoint comparison

Let xi^(1),...,xi^(m) be independent proper complex Gaussian vectors with covariance bar(A), and set
\[
W_m=\frac1m\sum_{s=1}^m\xi^{(s)}\xi^{(s)*},\qquad
F_m=\mathbb E\operatorname{per}(A\circ W_m).
\]
Write v_pi=product_i A_i,pi(i), and let c(tau) be the number of cycles of tau, including fixed points. Wick expansion gives
\[
\boxed{
F_m=m^{-n}\sum_{\pi,\tau\in S_n}
 m^{c(\tau)}v_\pi\overline{v_{\pi\circ\tau}}.
}\tag{7}
\]
To verify (7), expand each entry of W_m using sample labels s_i. A Wick matching tau is permitted precisely when s_i=s_tau(i). Summing the labels gives m^{c(tau)}. The covariance product is conjugate(v_(pi compose tau)), after choosing the matching orientation consistently; replacing tau by its inverse gives the equivalent opposite convention.

For m=1, separate the two permutation sums; for m tending to infinity, only tau=id survives. Therefore
\[
\boxed{F_1=P^2,\qquad\lim_{m\to\infty}F_m=Q.}\tag{8}
\]
Thus the full one-matrix Chollet conjecture is the endpoint comparison F_1>=F_infinity for these Gram-generated coefficients.

A possible stronger statement would be nonnegativity of every coefficient in
\[
F_m=Q+\sum_{k=1}^{n-1}\frac{c_k(A)}{m^k},
\quad
c_k(A)=\sum_{c(\tau)=n-k}\sum_\pi v_\pi\overline{v_{\pi\circ\tau}}.
\tag{9}
\]
**Coefficientwise nonnegativity is false.** For the singular trine correlation matrix T with diagonal 1 and off-diagonal -1/2, the permutation products are 1, three copies of 1/4, and two copies of -1/8. Exact summation gives
\[
\boxed{F_m(T)=\frac{39}{32}+\frac{9}{8m}-\frac{3}{32m^2}.}\tag{10}
\]
Even for the positive-definite correlation matrix with off-diagonal -t/2, 0<t<1, the coefficient of m^(-2) is
\[
\frac{t^3}{32}(t^3+12t-16)<0.
\]
This refutes the proposed stronger coefficient claim, not Chollet or monotonicity of F_m.

There is nonetheless an exact positive expansion in the falling-factorial basis. Define
\[
H_k(A)=\frac1{k!}
\sum_{\substack{(B_1,\ldots,B_k),(C_1,\ldots,C_k)\text{ ordered partitions of }[n]\\
 B_s,C_s\ne\varnothing,\ |B_s|=|C_s|}}
\prod_{s=1}^k|\operatorname{per}A[B_s,C_s]|^2.
\]
Grouping the Gaussian labels by their nonempty fibers gives
\[
\boxed{F_m=m^{-n}\sum_{k=1}^n(m)_kH_k(A),\qquad H_k\ge0,}
\tag{11}
\]
where (m)_k=m(m-1)...(m-k+1). For each row-block partition B_s, group the permutation images into blocks C_s. The permutation sum and Wick sum give conjugate permanents of the same rectangular-indexed square submatrices, producing the displayed squared moduli. Distinct sample labels give (m)_k; division by k! removes block ordering.

Here H_1=P^2 and H_n=Q. On the trine the coefficients are (H_1,H_2,H_3)=(9/4,153/32,39/32). Their positivity does not imply H_1>=H_n. Converting bases produces the negative coefficient in (10).

Finally, positive Fourier blocks alone cannot fill this gap. On S_3 the class function
\[
\phi(e)=1,\quad\phi(\text{transposition})=1/6,\quad
\phi(\text{3-cycle})=-1/4
\]
has Fourier blocks 1, 0, and (5/4)I_2 in the trivial, sign, and standard representations. Thus it is positive definite and has the representation support allowed at Gram rank two, but
\[
|\sum_\pi\phi(\pi)|^2=1<29/24=\sum_\pi|\phi(\pi)|^2.
\]
It cannot be generated by Gram permutation products: those obey
|v_(123)|^2=v_(12)v_(23)v_(13), whereas this function gives 1/16 rather than 1/216. A Fourier proof must retain those nonlinear product constraints. Positivity and vanishing determinant sectors are insufficient.

## 4. Numerical evidence and reproducibility

The direct search used complex Gram matrices in dimensions 5 through 8, including every rank cap from 2 to n in the extended pass. Across 4,200 sampled frames and 1,536 multistart optimizations, no violation was reported. The retained 22 rank-cap winners were recomputed at 80-digit precision; the apparent double-precision excesses above one disappeared. These checks do not classify singular extrema or prove the conjecture.

Artifacts from this pass are preserved under `build/direct_attack/chollet/`: `probe.py`, `extended.py`, `validate.py`, `derivation.md`, `report.json`, `extended_report.json`, `validation.json`, and saved example arrays. The exact trine and Fourier-obstruction arithmetic is independently checked by `code/research/verify_direct_conjecture_reductions.py`. This note's claims do not depend on treating finite observations as universal.

The remaining full target is R<=1 on the singular irreducible boundary, equivalently the Gaussian endpoint inequality in (8). Neither another known low-dimensional case nor a determinant-style local coupling closes that target.
