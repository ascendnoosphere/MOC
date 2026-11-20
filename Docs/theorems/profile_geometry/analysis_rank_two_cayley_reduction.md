# Exact rank-two Cayley reduction and a proved support certificate

This note gives exact formulas and a sufficient inequality. It does not prove universal rank-two Cayley positivity or unrestricted MOC. Throughout, the identity is assumed to be a maximizing permutation in the support direction under consideration. A restriction on the Cayley generator must not be silently assumed to survive the permutation relabeling needed for a different support direction.

## 1. The compressed matrix has size four, independently of n

Let a,b be complex spectra, m_i=a_i+b_i≠0, z_id=product_i m_i, and zeta=eta z_id. Let Y be a real n×2 matrix with Y^TY=I2, with row vectors y_i. Put J=[[0,1],[-1,0]], K=YJY^T, and

\[
U_\theta=I+Y(R_\theta-I_2)Y^T,
\qquad R_\theta=\cos\theta I_2+\sin\theta J.
\]

Define

\[
P_i'=\frac1{m_i}\begin{pmatrix}a_i&1\\a_ib_i&b_i\end{pmatrix},
\qquad W_i=y_iy_i^T,
\qquad N=\sum_iP_i'\otimes W_i.
\]

These P_i' are a common conjugation of the idempotents in the Clifford reformulation. The rank-one determinant lemma gives

\[
\boxed{\frac{\det(D_a+U_\theta D_bU_\theta^T)}{z_{id}}
=\det\{I_4+(I_2\otimes(R_\theta-I_2))N\}.}
\tag{1}
\]

To see the factorization directly, write P_i'=u_iw_i^T, with u_i=(1,b_i)^T and w_i^T=(a_i,1)/m_i. Then w_i^Tu_j=(a_i+b_j)/m_i. The Hadamard multiplier of U_theta differs from identity by the product of the matrices with rows w_i^T tensor y_i^T and columns u_i tensor (R_theta−I)y_i. Interchanging the two factors in det(I+AB) gives (1).

## 2. Hamiltonian symmetry and the reflection endpoint

The compressed matrix has block form

\[
N=\begin{pmatrix}A&B\\E&I_2-A\end{pmatrix},
\]

where A,B,E are complex symmetric 2×2 matrices. Therefore H=N−I4/2 is Hamiltonian for Omega=[[0,I2],[-I2,0]]: H^T Omega+Omega H=0. Its eigenvalues occur in opposite pairs, so those of N occur in pairs lambda,1−lambda. In particular

\[
\operatorname{tr}N=2,\qquad e_3(N)=e_2(N)-1.
\]

At theta=pi the orthogonal matrix is the reflection I−2YY^T, and

\[
\boxed{\det(I_4-2N)=-3+2\operatorname{tr}(N^2)+16\det N.}
\tag{2}
\]

This follows by expanding the determinant in elementary symmetric functions and substituting e3=e2−1 and e2=2−tr(N²)/2.

Let s_ij=tr(P_i'P_j')=z_(ij)/z_id. Then

\[
\operatorname{tr}(N^2)=\sum_{ij}s_{ij}(y_i^Ty_j)^2.
\]

Since sum_i W_i=I2, the corresponding sum without s_ij is two.

## 3. Exact coefficients in dimension four

Now let n=4, and allow an arbitrary full-rank real X in R^(4×2). Put

\[
K=XJX^T,\quad\sigma=\det(X^TX)>0,\quad
F_a(X)=\det[X,D_aX],\quad F_b(X)=\det[X,D_bX].
\]

Let U_t=(I+tK)(I−tK)^{-1}. If h=Re(eta z_id) is the maximum of the permutation support values, put delta_pi=h−Re(eta z_pi)≥0. The exact support numerator is

\[
(1+\sigma t^2)^2
\{h-\operatorname{Re}(\eta\det(D_a+U_tD_bU_t^T))\}
=t^2(q_0+q_1t+q_2t^2).
\]

The first and third coefficients are

\[
\boxed{q_0=4\sum_{i<j}\delta_{ij}K_{ij}^2,}
\tag{3}
\]

\[
\boxed{q_2=4\sum_{i<j}\delta_{ij}(K^2_{ij})^2
-16\operatorname{Re}\{\eta F_a(X)F_b(X)\}.}
\tag{4}
\]

For the proof of (4), normalize Y=X(X^TX)^{-1/2}. The rank-one factorization of N gives

\[
\det N=\frac{F_a(X)F_b(X)}{\sigma^2z_{id}}.
\]

Also K²=−sigma YY^T. Equation (2), followed by multiplication by sigma², gives (4). Thus the apparently complicated reflection interference is one product of two mixed four-volumes.

For q1, put S_i=(1,b_i−a_i,a_ib_i), V_i=(x_i²,x_iy_i,y_i²) when X_i=(x_i,y_i), and let S,V be the corresponding 4×3 matrices. Then

\[
\boxed{q_1=8\operatorname{Re}\{\zeta
\det(S^T\operatorname{diag}(1/m_i)V)\}.}
\tag{5}
\]

The proof uses Kij Kjk Kki=−det V[ijk] and

\[
z_{(ijk)}-z_{(ikj)}=m_l\det S[ijk].
\]

The two signs cancel in the support gap, and Cauchy–Binet combines the four triples. All polynomial formulas extend to zero m_i after canceling denominators; no division by zero is needed in their polynomial versions.

## 4. The exact two-by-two Gram obligation

Define

\[
A=\sum_{i<j}\delta_{ij}K_{ij}^2,\qquad
B=q_1/8,\qquad
C_0=\sum_{i<j}\delta_{ij}(K^2_{ij})^2,
\qquad P=\operatorname{Re}(\eta F_aF_b).
\]

Then q0=4A, q1=8B, q2=4(C0−4P). Thus positivity for every real t is equivalent to

\[
\boxed{\begin{pmatrix}A&B\\B&C_0-4P\end{pmatrix}\succeq0.}
\tag{6}
\]

The known support inequalities guarantee A≥0. They do not yet supply the remaining determinant inequality B²≤A(C0−4P), nor the lower-right entry when A=0.

## 5. The mixed-volume term uses only three matching differences

Write

\[
r=(K_{12}K_{34},-K_{13}K_{24},K_{14}K_{23}).
\]

Decomposability gives r1+r2+r3=0. For matching i, let S_i be the sum of its two transposition gaps, and D_i its double-transposition gap. Then

\[
\boxed{P=\sum_{i=1}^3(D_i-S_i)r_jr_k,\qquad\{i,j,k\}=\{1,2,3\}.}
\tag{7}
\]

For example, define alpha1=(a1−a2)(a3−a4), alpha2=(a1−a3)(a2−a4), alpha3=(a1−a4)(a2−a3), and similarly beta. They obey alpha2=alpha1+alpha3. Expansion gives F_a=r1 alpha2+r2 alpha1. Consequently F_aF_b=−sum_i r_jr_k alpha_i beta_i. On the other hand D_i−S_i=−Re(eta alpha_i beta_i), proving (7).

## 6. A proved sufficient matching-budget certificate

For an edge e={i,j}, let k,l be the complementary indices and put

\[
L_e=|K_{ik}K_{kj}|+|K_{il}K_{lj}|,
\qquad C_{\rm abs}=\sum_e\delta_eL_e^2.
\]

The principal three-index identities imply

\[
|\delta_{(ijk)}-\delta_{(ikj)}|
\le\delta_{ij}+\delta_{ik}+\delta_{jk}.
\]

Summing triangle contributions and applying weighted Cauchy–Schwarz gives

\[
|B|\le\sum_e\delta_e|K_e|L_e,
\qquad\boxed{B^2\le A C_{\rm abs}.}
\tag{8}
\]

Therefore the actual support quadratic is nonnegative whenever

\[
\boxed{C_0-4P\ge C_{\rm abs}.}
\tag{9}
\]

This has a particularly small geometric meaning in four dimensions. The two path products for either edge of matching i have product −r_jr_k. Because r1+r2+r3=0, at most one of r_jr_k is positive. Hence

\[
C_{\rm abs}-C_0=4\sum_i(r_jr_k)_+S_i.
\]

Thus (9) is exactly

\[
\boxed{P+\sum_i(r_jr_k)_+S_i\le0.}
\tag{10}
\]

For nonzero r there is just one cancelling matching. This is a proved sufficient condition, not a necessary condition and not a consequence established here of the full permutation support inequalities.

An explicit sum of squares follows. Let R=sum_e delta_e |K_e|L_e. If R>0, put lambda=B/R, so |lambda|≤1. Then, writing C=C0−4P,

\[
A+2Bt+Ct^2
=\sum_e\delta_e(|K_e|+\lambda L_et)^2
 +(1-\lambda^2)C_{\rm abs}t^2+(C-C_{\rm abs})t^2.
\]

All terms are nonnegative under (9). If R=0, B=0 and the conclusion is immediate.

The condition has nondegenerate actual examples. For K with upper entries (−1,−3,9,1,−5,−6), take

\[
a=(-2i,-3+i,-3-i,2+2i),\quad
b=(-2,2+3i,-3+3i,-3-2i),\quad\eta=1.
\]

Here h=48, all m_i are nonzero, r=(6,−15,9), S=(120,120,240), D=(360,420,160), and P=−9000. The budget is −9000+54·120=−2520<0. The exact quadratic coefficients are (81280,−134880,2254880). See `analysis/rank_two_budget_certificate.json`.

## 7. Extension of the compressed formulas to every n

Equation (1) is valid for all n. After diagonalizing J, the determinant is a Laurent polynomial with powers of exp(i theta) from −2 to 2. Its derivative at theta=0 vanishes because tr((I tensor J)N)=sum_i tr(P_i')tr(JW_i)=0. With t=tan(theta/2), its support numerator is therefore t² times a quadratic, just as in dimension four.

Equation (5) remains valid with n rows in S and V. For the q2 mixed-volume term, Cauchy–Binet gives

\[
\zeta\det N
=\sum_{|I|=4}\eta\left(\prod_{j\notin I}m_j\right)
F_a(Y_I)F_b(Y_I).
\]

Thus the all-n real rank-two direction has the same four-dimensional compressed algebra, with a sum of coherent four-index mixed-volume terms. This is not a positive gluing of four-dimensional support certificates: their external complex factors and their shared two-path terms still require control.

## What remains

The universal inequality in (6) is unproved. Condition (10) covers a specific, nonempty region but can fail on valid spectral inputs. The independent coefficient-law attempt for real a and F_a=0 also remains unproved. Finally, a rank-two Cayley theorem based at a maximizing permutation would not by itself imply MOC in all directions for every fixed rank-two matrix: right multiplication by the maximizing permutation can change the rank of the Cayley generator.
