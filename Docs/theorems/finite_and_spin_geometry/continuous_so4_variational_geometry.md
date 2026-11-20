# Exact variational geometry on the real four-dimensional orthogonal orbit

This note proves the actual determinant Hessian, its exact criterion on real rank-two generators, a Casimir identity, and constructive finite and coherent escapes. It does not prove unrestricted complex MOC.

Throughout, (A=\operatorname{diag}(a_1,a_2,a_3,a_4)), (B=O\operatorname{diag}(b_1,b_2,b_3,b_4)O^T), (O\in SO(4)), and

\[
F(U)=\Re\{\eta\det(A+UBU^*)\}.
\]

The base point is (U=I). The support parameter (\eta\in\mathbb C) is fixed; multiplying it by a positive number does not change the maximizers.

## 1. The actual determinant Hessian

Let (M=A+B), (d=\det M), and initially assume (M) invertible, with (R=M^{-1}). For a real skew-symmetric generator (K), multiplication on the right by (e^{tK}) gives

\[
\det(A+e^{tK}Be^{-tK})=\det(Ae^{tK}+e^{tK}B),
\]

because (\det e^{tK}=1). Set

\[
S_K=AK+KB,\qquad T_K=AK^2+K^2B.
\]

Differentiating the determinant yields

\[
D'(K)=d\,\operatorname{tr}(RS_K),
\tag{1}
\]

\[
D''(K)=d\left[(\operatorname{tr}RS_K)^2
-\operatorname{tr}(RS_KRS_K)+\operatorname{tr}(RT_K)\right].
\tag{2}
\]

The real support gradient and Hessian are the real parts of (\eta) times these expressions. For mixed directions (K,L), polarization gives

\[
\begin{aligned}
H(K,L)=\Re\Bigg\{\eta d\Bigg[
&\operatorname{tr}(RS_K)\operatorname{tr}(RS_L)
-\operatorname{tr}(RS_KRS_L)\\
&+\operatorname{tr}\left(R\left(A\frac{KL+LK}{2}
+\frac{KL+LK}{2}B\right)\right)\Bigg]\Bigg\}.
\end{aligned}
\tag{3}
\]

The determinant derivative itself is polynomial in the entries. Thus (1)–(3), after cancellation of the apparent inverse denominators, extend to singular (M) by continuity. The explicit examples below are nonsingular and need no limiting argument.

There are two useful symmetry facts. Since (A^T=A) and (B^T=B), transposition gives

\[
\det(A+UBU^*)=\det(A+\bar U B U^T).
\tag{4}
\]

Consequently the objective is invariant under (U\mapsto\bar U). In the tangent decomposition (K+iS), with (K) real skew and (S) real symmetric, all first derivatives in the (iS) directions vanish at the real base, and all real/imaginary mixed Hessian entries vanish. Therefore vanishing of the real skew gradient proves full unitary stationarity at these bases.

Second, diagonal unitary matrices commute with (A), so left multiplication by one leaves (F) invariant. At a stationary point its tangent directions lie in the kernel of the full Hessian, including all mixed Hessian pairings. One direct proof differentiates (F(e^{sV}e^{tK})=F(e^{tK})), where (V) is imaginary diagonal; at a stationary point the mixed second derivative agrees with the intrinsic Hessian independently of the coordinate chart.

## 2. Rank-two generators form the Pfaffian null cone

Use the edge coordinates

\[
k=(k_{12},k_{13},k_{14},k_{23},k_{24},k_{34}),
\]

where (K_{ij}=k_{ij}) above the diagonal. In four dimensions,

\[
\operatorname{Pf}(K)=k_{12}k_{34}-k_{13}k_{24}+k_{14}k_{23}.
\tag{5}
\]

Every nonzero real skew matrix with zero Pfaffian has rank two. Let (J) be the real symmetric six by six matrix with the only nonzero upper-triangular entries

\[
J_{1,6}=1,\qquad J_{2,5}=-1,\qquad J_{3,4}=1.
\]

Then (k^TJk=2\operatorname{Pf}(K)) and (J^2=I). The orthonormal self-dual and anti-self-dual coordinates are

\[
x=\frac{(k_{12}+k_{34},\ k_{13}-k_{24},\ k_{14}+k_{23})}{\sqrt2},
\]

\[
y=\frac{(k_{12}-k_{34},\ k_{13}+k_{24},\ k_{14}-k_{23})}{\sqrt2}.
\]

Thus

\[
k^TJk=\|x\|^2-\|y\|^2.
\tag{6}
\]

The rank-two cone is a balanced cone between two three-dimensional Euclidean spaces; its linear span is the whole tangent space, but testing a quadratic form on it need not test the whole space.

## 3. A PSD lift is exact for this quadratic problem

The following elementary decomposition explains the precise relaxation that is permitted.

**Lemma.** If (X\succeq0), (\operatorname{tr}X=1), and (\operatorname{tr}(JX)=0), then (X) is a convex combination of matrices (vv^T) with (\|v\|=1) and (v^TJv=0).

**Proof.** Factor (X=VV^T). The symmetric matrix (S=V^TJV) has trace zero. A real symmetric trace-zero matrix has an orthonormal basis (q_1,\ldots,q_m) in which every diagonal entry is zero: if it is not already zero, choose a unit vector with zero Rayleigh quotient by continuity between a positive and a negative eigenvector, compress to its orthogonal complement, and induct, since that compression still has trace zero. Put (w_j=Vq_j). Then

\[
X=\sum_j w_jw_j^T,\qquad w_j^TJw_j=0,
\qquad \sum_j\|w_j\|^2=1.
\]

Discard zero columns and normalize the others. Their squared norms are the desired convex weights. \(\square\)

In particular, for any real symmetric Hessian matrix (H),

\[
\begin{aligned}
\mu(H)&:=\max_{\|k\|=1,\ k^TJk=0}k^THk\\
&=\max\{\operatorname{tr}(HX):X\succeq0,
\operatorname{tr}X=1,\operatorname{tr}(JX)=0\}.
\end{aligned}
\tag{7}
\]

This quadratic lift uses one indefinite quadratic constraint and a linear objective in (X); it does not justify nonlinear density substitutions.

## 4. The exact one-multiplier criterion

The dual scalar formula is

\[
\boxed{\mu(H)=\min_{\lambda\in\mathbb R}
\lambda_{\max}(H-\lambda J).}
\tag{8}
\]

Here is a proof without assuming a black-box matrix optimization theorem. Consider the compact convex set

\[
\mathcal C=\{(\operatorname{tr}JX,\operatorname{tr}HX):X\succeq0,
\operatorname{tr}X=1\}\subset\mathbb R^2.
\]

Its first-coordinate projection is ([-1,1]). Its upper boundary is a finite concave function on the interior of that interval, so at zero it has a finite supporting slope (\lambda). Consequently every density matrix satisfies

\[
\operatorname{tr}HX-\lambda\operatorname{tr}JX\le\mu(H).
\]

Testing rank-one densities gives (H-\lambda J\preceq\mu(H)I). Conversely every isotropic unit vector satisfies (k^THk=k^T(H-\lambda J)k\le\lambda_{\max}(H-\lambda J)). These two inequalities prove (8), with an attained minimum.

Therefore

\[
\boxed{H(K,K)\le0\text{ for every real rank-two }K
\quad\Longleftrightarrow\quad
H-\lambda J\preceq0\text{ for some real }\lambda.}
\tag{9}
\]

The missing scalar (\lambda) is a genuine geometric degree of freedom. No zero-multiplier assumption is made.

## 5. The actual Casimir contraction

The exterior-square representation of (O\in SO(4)) preserves the self-dual and anti-self-dual spaces. In the bases

\[
\frac{(12+34,\ 13-24,\ 14+23)}{\sqrt2},
\qquad
\frac{(12-34,\ 13+24,\ 14-23)}{\sqrt2},
\]

write

\[
\wedge^2O=\operatorname{diag}(R_+,R_-),\qquad R_\pm\in SO(3).
\]

Define the complex diagonal matrices

\[
X_a=\operatorname{diag}\left(
\frac{a_1a_2+a_3a_4}{2},
\frac{a_1a_3+a_2a_4}{2},
\frac{a_1a_4+a_2a_3}{2}\right),
\tag{10}
\]

and (X_b) by the same rule. Put

\[
F_\pm=\operatorname{tr}(X_aR_\pm X_bR_\pm^T).
\]

Then the actual support Hessian obeys the exact identity

\[
\boxed{\operatorname{tr}(HJ)
=-12\Re\{\eta(F_+-F_-)\}.}
\tag{11}
\]

This formula does not require stationarity.

**Proof.** In the determinant expansion by squared minors, the terms of sizes zero and four are constant. The terms of sizes one and three are linear combinations of (O_{ij}^2), since complementary three-minors of an orientation-preserving orthogonal matrix equal signed entries. The difference between the self-dual and anti-self-dual Casimirs is

\[
2(D_{12}D_{34}-D_{13}D_{24}+D_{14}D_{23}),
\]

which annihilates each (O_{ij}^2): in each summand the two disjoint row rotations cannot both act nontrivially on a function of one row.

For the size-two term, the diagonal product-weight matrices become block matrices with equal diagonal blocks (X_a,X_a) and (X_b,X_b). Their other blocks are diagonal matrices (Y_a,Y_b), whose precise entries are not needed. Expanding its trace gives

\[
F_++F_-+2\sum_{p,q}(Y_a)_{pp}(Y_b)_{qq}(R_+)_{pq}(R_-)_{pq}.
\]

Each orthonormal self-dual generator acts on (R_+) with angular speed (\sqrt2) and fixes (R_-); the anti-self-dual generators do the converse. On (SO(3)), direct differentiation of the three coordinate-plane rotations gives

\[
\sum_jD_j^2 R_{pq}=-2R_{pq},\qquad
\sum_jD_j^2 R_{pq}^2=2-6R_{pq}^2.
\]

The extra angular-speed square is two. Thus each pure (F_\pm) contributes (4\operatorname{tr}X_a\operatorname{tr}X_b-12F_\pm); the mixed terms have identical Casimir eigenvalue in the two factors and cancel. The two constants cancel as well. Finally the Casimir difference equals (\operatorname{tr}(HJ)), by the displayed self-dual coordinate change. This proves (11). \(\square\)

## 6. Simple-spectrum setup and exact curvature certificate

Take (\eta=1) and

\[
A=\operatorname{diag}(3,1,-1,-3),
\qquad
B=\begin{pmatrix}
2&-i&0&0\\-i&2&0&0\\
0&0&-2&-i\\0&0&-i&-2
\end{pmatrix}.
\tag{12}
\]

Both are normal and have simple spectra. In fact, with

\[
R_\theta=\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix},
\quad O=\operatorname{diag}(R_{\pi/4},R_{\pi/4}),
\]

one has (B=O\operatorname{diag}(2+i,2-i,-2+i,-2-i)O^T). The base determinant is (256); the largest real permutation value is (260).

The real skew gradient is zero. Equation (3), in the edge order of Section 2, gives

\[
H=\begin{pmatrix}
0&0&0&0&0&-16\\
0&-544&0&0&32&0\\
0&0&-504&24&0&0\\
0&0&24&-440&0&0\\
0&32&0&0&-544&0\\
-16&0&0&0&0&0
\end{pmatrix}.
\tag{13}
\]

The exact identity

\[
\begin{aligned}
k^THk+32\operatorname{Pf}(K)={}&
-528(k_{13}^2+k_{24}^2)-16(k_{13}-k_{24})^2\\
&-464k_{14}^2-400k_{23}^2-40(k_{14}-k_{23})^2
\end{aligned}
\tag{14}
\]

proves nonpositivity for every real rank-two generator. Equality on that cone forces all four cross-block coordinates to vanish; its remaining equation is (k_{12}k_{34}=0). The only nonzero equality directions are therefore the two internal coordinate rotations.

Nevertheless (K=E_{12}-E_{34}) has (H(K,K)=32>0). The full Hessian has eigenvalues

\[
-576,-512,-512,-432,-16,16.
\]

This is an actual stationary saddle with no positive real rank-two second derivative. Moreover, the multiplier in (9) is uniquely (\lambda=-16): the internal two by two block of (H-\lambda J) has zero diagonal, so its off-diagonal entry (-16-\lambda) must vanish. Equation (14) then proves the remaining blocks negative semidefinite. Its Casimir contraction is (-48), in agreement with (11), whose pure terms here are (F_+=49,F_-=45).

## 7. Flat transport and a complex rank-two escape

The same example admits an exact two-variable formula, so its geometry is fully visible. Rotate the first and second coordinate blocks by angles (\theta_1,\theta_2). Direct multiplication of the two block determinants gives

\[
\det(A+e^{\theta_1E_{12}+\theta_2E_{34}}
 B e^{-\theta_1E_{12}-\theta_2E_{34}})
=(16+2i\sin2\theta_1)(16+2i\sin2\theta_2),
\]

\[
F=256-4\sin2\theta_1\sin2\theta_2.
\tag{15}
\]

Either coordinate axis is exactly flat. Move along one of them, then use the other with the opposite sign: this is a sequence of two real rank-two rotations whose support is first constant and then increasing. At (\theta_1=\pi/4,\theta_2=-\pi/4) it reaches the permutation ceiling (260). The example is therefore not a barrier to all sequences of monotone elementary moves.

The simultaneous infinitesimal escape (K=E_{12}-E_{34}) has real rank four and obeys (K^2=-I). Yet

\[
P=\frac{I-iK}{2}
\]

is a complex orthogonal projection of rank two, and

\[
K+iI=2iP,\qquad
e^{t(K+iI)}=I+(e^{2it}-1)P.
\tag{16}
\]

The scalar phase (e^{it}) cancels in conjugation. Hence (16) is a complex rank-two update with the same positive curvature and the same objective trajectory as (e^{tK}). Real rank-two and complex rank-two escape questions must be distinguished even at a real orthogonal base.

## 8. A finite real rank-two escape can cross an initial loss

There is also a single real rank-two rotation whose endpoint improves the support, although its curvature at zero is negative. Let

\[
u=(1,2,0,0)^T/\sqrt5,\qquad
v=(0,0,1,-2)^T/\sqrt5,\qquad K=uv^T-vu^T.
\]

Then (K^3=-K), and exact determinant expansion gives

\[
\boxed{
F(e^{\theta K})
=256-\frac{6736}{25}\sin^2\theta
+\frac{576}{625}(1-\cos\theta)^2.}
\tag{17}
\]

The second derivative is (-13472/25), but the half-turn endpoint has gain (2304/625>0). To certify the whole curve rationally, put (K_0=5K), whose upper edges are ((0,1,-2,2,-4,0)), and use the Cayley parameter (t=\tan(\theta/2)/5). The real support is exactly

\[
\frac{256-14144t^2+162304t^4}{(1+25t^2)^2}.
\tag{18}
\]

The Gaussian rational determinant numerator has imaginary coefficient (-1280i,t^2); taking the real part gives (18). The full polynomial division in the certificate verifies it, and elementary half-angle substitution gives (17).

The companion note `continuous_rank_two_torus.md` proves the general identity behind this calculation: a stationary real rank-two fiber in any dimension is determined by its second derivative, third derivative, and half-turn endpoint through an exact two by two matrix. Thus a negative Hessian alone cannot establish global nonascent even on a single real rank-two fiber.

## 9. Scope and certificates

The exact calculations are implemented in `code/theorems/finite_and_spin_geometry/continuous_third_batch_exact.py`. All numeric entries above are Gaussian rational identities, including the Hessians, stationarity, permutation ceiling, shifted sum of squares, finite Cayley curve, and rank-two complex update.

The rigorous conclusions are the precise quadratic rank-two criterion, its actual obstruction, and explicit finite or coherent ways around that obstruction. The remaining complex MOC issue concerns the support at a global unitary maximum. The universal rank-two torus inequalities in the companion note retain more information than the Hessian, but deriving the permutation bound from them remains an unproved step.

### Research context

The primary publisher abstract for Juan Ignacio Mulero-Martínez, “A variational framework for determinantal inequalities of normal matrices: Successes and obstructions,” *Linear Algebra and its Applications* **740** (2026), 19–38, DOI [10.1016/j.laa.2026.03.019](https://doi.org/10.1016/j.laa.2026.03.019), describes support-functional variational methods and obstructions for normal matrices. Only its publisher abstract and institutional bibliographic record were checked. No priority claim is made here for the general variational approach, and no uninspected theorem from that article is used in these proofs.
