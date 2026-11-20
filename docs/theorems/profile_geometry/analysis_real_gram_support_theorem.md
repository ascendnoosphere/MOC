# A proved directional MOC theorem for real complex-bilinear Gram data

This is a restricted support theorem, valid in every matrix dimension. It does not prove unrestricted complex MOC. The restriction concerns the exact Clifford Gram matrix and the phase of the support direction; it is not a restriction of the mixing matrix to real entries.

## Statement

Let a,b be complex spectra, let z_pi=product_i(a_i+b_pi(i)), and suppose z_id is nonzero. Construct the rank-one idempotents and complex-bilinear Gram matrix from `analysis_clifford_idempotent_reformulation.md`:

\[
P_i=\frac1{a_i+b_i}\begin{pmatrix}b_i&a_ib_i\\1&a_i\end{pmatrix},
\qquad Q_i=2P_i-I=\nu_i\cdot\sigma,
\qquad G_{ij}=\nu_i\cdot\nu_j.
\]

Assume G is real symmetric. Let eta be a support direction satisfying

\[
\zeta=\eta z_{id}>0\quad\hbox{real},
\qquad \operatorname{Re}(\eta z_\pi)\le\zeta\quad\hbox{for every }\pi.
\]

Then, for every U in U(n),

\[
\boxed{\operatorname{Re}\{\eta\det(D_a+UD_bU^*)\}\le\zeta.}
\]

The proof separates the possible inertias of G. It uses the classical Hermitian determinant theorem of Fiedler in the split real branch, and a direct compression argument in the positive branch.

## 1. Positive-semidefinite G

Choose real unit vectors nu_i in R3 with this Gram matrix. Their projectors P_i=(I+nu_i·sigma)/2 are Hermitian rank-one projections. Choose unit spinors x_i with P_i=x_i x_i*. The normalized multiplier matrix can then be chosen as the correlation matrix

\[
C_{ij}=x_i^*x_j.
\]

This choice has the same cycle traces as the original data after choosing a coherent orientation. In rank three there are two global orientation choices, and either can be obtained by reflecting the real realization. In lower rank all triple volumes vanish. Thus every normalized permutation product, and hence the determinant expansion for each fixed U, agrees with the original data.

Define the isometry V:C^n→C^n tensor C² by V e_i=e_i tensor x_i. Then

\[
C\circ U=V^*(U\otimes I_2)V.
\]

Consequently its operator norm is at most one. Every singular value is at most one, so

\[
\left|\frac{\det(C\circ U)}{\det U}\right|\le1.
\]

The normalized target determinant is det(C∘U)/det U. Multiplying the real-part inequality by the positive number zeta proves the stated support inequality. In this branch the modulus bound is stronger than the particular support conclusion; it still does not establish all other support directions of the permutation polygon.

## 2. At most two positive and at most one negative Gram directions

By real congruence, G has a realization

\[
\nu_i=(x_i,iy_i,z_i),\qquad x_i,y_i,z_i\in\mathbb R.
\]

The vectors obey x_i²−y_i²+z_i²=1. The Pauli matrices therefore give

\[
Q_i=\begin{pmatrix}z_i&x_i+y_i\\x_i-y_i&-z_i\end{pmatrix},
\]

which is real, and P_i=(I+Q_i)/2 is a real rank-one trace-one idempotent. Choose the global orientation to agree with the original triple volumes. The same Clifford trace recursions then reproduce every cycle trace. If the Gram rank is below three, the triple volumes are all zero and no orientation choice is needed.

A generic common matrix S in GL(2,R) makes every lower-left entry of S P_i S^{-1} nonzero: each excluded condition is a proper real algebraic condition, and finitely many such conditions cannot exhaust GL(2,R). Write each transformed idempotent as

\[
\begin{pmatrix}p_i&q_i\\r_i&1-p_i\end{pmatrix},\qquad r_i\ne0.
\]

The spectra

\[
a_i'=(1-p_i)/r_i,\qquad b_i'=p_i/r_i
\]

are real and recover those idempotents exactly. Therefore all normalized permutation products and the normalized target determinant agree with those for this real spectral pair.

Fiedler's Hermitian determinant theorem states that det(D_a'+UD_b'U*) lies between the smallest and largest real permutation products. Multiplication by the nonzero real number 1/z_id' preserves convex-hull membership, including when it reverses the endpoints. Thus the normalized determinant lies in the interval of the normalized permutation products. Their maximum is at most one by the support hypothesis. The desired inequality follows.

This branch actually proves full convex-hull membership for the normalized idempotent data, independently of the phase of eta, because every cycle product is real. The complete theorem retains the phase assumption because the positive Gram branch only supplied the radial support bound.

### Rank-deficient bilinear spans

No isometry between possibly degenerate vector spans is assumed here. If the Gram rank is below three, every triple determinant of the original vectors is zero: the square of that determinant is the corresponding principal Gram determinant, and three independent vectors in C3 would give a nonzero square. All triple volumes therefore vanish. Clifford trace expansion expresses every longer cycle trace through pair contractions and triple volumes, so the replacement realization has exactly the same cycle traces even when the original span has an isotropic radical. The determinant is a linear combination of the permutation cycle products for each fixed U. This is why matching the cycle data suffices in the degenerate case.

## 3. The remaining inertia is excluded by transposition gaps

Since G has rank at most three and diagonal one, the only remaining possible inertia is one positive and two negative eigenvalues. Realize G by timelike unit vectors w_i=(t_i,u_i) in R^(1,2):

\[
t_i^2-\|u_i\|^2=1,
\qquad G_{ij}=t_it_j-u_i\cdot u_j.
\]

The transposition support gaps are

\[
\delta_{ij}=\frac{\zeta}{2}(1-G_{ij})\ge0,
\]

so G_ij≤1. Two vectors on the same sheet have the same sign of t. Write |t_i|=cosh r_i and ||u_i||=sinh r_i. Then

\[
G_{ij}\ge\cosh r_i\cosh r_j-\sinh r_i\sinh r_j
=\cosh(r_i-r_j)\ge1.
\]

Equality throughout forces the two vectors to be identical: their radial parameters and spatial directions agree. Consequently all vectors on either sheet must coincide. There are at most two distinct vectors, making the Gram rank at most two. This contradicts inertia (1,2).

These three cases exhaust all real symmetric matrices of rank at most three with diagonal one. The theorem is proved.

## Source and boundary of the argument

The invoked Hermitian result is M. Fiedler, “Bounds for the determinant of the sum of Hermitian matrices,” Proceedings of the American Mathematical Society 30 (1971), 27–31; DOI 10.1090/S0002-9939-1971-0286814-1. Its statement is also recalled in the introduction of the primary research paper by N. Bebiano and J. da Providência, “A Fiedler-type theorem for the determinant of J-positive matrices,” Mathematical Inequalities & Applications 19 (2016), 663–669:

https://files.ele-math.com/articles/mia-19-47.pdf

No priority claim is made for this reformulation or support slice. General actual spectral data have genuinely complex Gram matrices, and an arbitrary polygon support direction does not satisfy eta z_id>0. The inertia proof does not cross either of these boundaries.
