# A one-sided principal-minor theorem in dimension four

**Theorem.** Let \(A\) be a Hermitian matrix of order four with eigenvalues \(a_1,\ldots,a_4\). There is a probability distribution \(\lambda\) on permutations such that, simultaneously for every \(b\in\mathbb C^4\),
\[
\det(A+\operatorname{diag} b)=\sum_{\pi\in S_4}\lambda_\pi\prod_{j=1}^4(a_j+b_{\pi(j)}).
\]
The distribution may depend on \(A\). Consequently MOC holds at order four whenever one spectrum lies on a generalized circle. The other spectrum and the relative eigenbasis are arbitrary.

## The projection of the permutation polytope

Normalize the four distinct real eigenvalues to \((0,x,y,1)\) with \(0<x<y<1\). An affine change of variables in the polynomial identity reverses this normalization. Repeated eigenvalues follow by continuity and compactness of the probability simplex. Write \(A=U\operatorname{diag}(0,x,y,1)U^*\) and \(Q_{I,J}=|\det U[I,J]|^2\).

Choose eigenvalue labels independently with inclusion probabilities \((0,x,y,1)\). Given the chosen set \(J\), select a row set \(I\) with probability \(Q_{I,J}\). Cauchy–Binet, or expansion of \(\det(I-A+A\operatorname{diag}z)\), gives the inclusion probabilities \(\Pr[T\subseteq I]=\det A[T,T]\). For a random permutation \(\pi\) independent of the eigenvalue selection, replace \(I\) by \(\pi(J)\). Equality of these set distributions implies the theorem by expansion in \(b\).

At size one the selected label is \(4\). At size three the missing label is \(1\). The two possible size-two label sets are \(42\) and \(43\). Their conditional probabilities are \(p=x(1-y)/(x+y-2xy)\) and \(1-p\), with \(0<p<1/2\). It suffices to match every singleton \(Q_{i,j}\) and the six coordinates
\[
p Q_{I,42}+(1-p)Q_{I,43},\qquad |I|=2.
\]
The comparison points for permutations replace \(Q_{I,J}\) by \(1_{I=\pi(J)}\).

All linear identities on the full permutation indicator vectors transfer to unitary minor vectors. Indeed, the complex measure formed by the Leibniz terms of \(\det U\) divided by \(\det U\) has mass one. Summing terms under \(\pi(J)=I\) gives \(Q_{I,J}\) by the complementary-minor identity.

## The analytic inequality

Put \(Q_0=Q_{34,34}\), \(Q_1=Q_{23,23}\) and
\[
F=Q_{2,3}+Q_{3,2}+Q_0-Q_{24,13}.
\]
Every real orthogonal mixer of order four satisfies
\[
F+Q_1+2\sqrt{Q_0Q_1}\ge0. \tag{1}
\]
Row signs reduce to determinant one. Use unit real quaternions \(q,r\) so that the rotation is left multiplication by \(q\) and right multiplication by \(r\), using the coordinate order \(1,i,j,k\). Put \(P_i=q_i^2,\ R_i=r_i^2,\ s_i=P_i+R_i\) with \(i=0,1,2,3\). Direct multiplication gives the signed minors
\[
d_0=P_0+P_1+R_0+R_1-1,\quad d_1=1-P_1-P_2-R_1-R_2,\quad v=R_0+R_2-P_0-P_2.
\]
Their squares are \(Q_0,Q_1,Q_{24,13}\), respectively. The two singleton squares sum to
\[
2[(q_0r_3-q_3r_0)^2+(q_1r_2+q_2r_1)^2]\ge2(D_0^2+D_1^2),
\]
where \(D_0=\sqrt{P_3R_0}-\sqrt{P_0R_3}\) and \(D_1=\sqrt{P_1R_2}-\sqrt{P_2R_1}\). Also
\[
(|d_0|+|d_1|)^2=\max\{(s_0-s_2)^2,(s_1-s_3)^2\}.
\]
The lower bound for the singleton squares is invariant under \(P\leftrightarrow R\). Assume \(v\ge0\). Set
\[
u=R_2-P_0,\quad t=R_0-P_2,\quad w=P_3-R_1,\quad z=P_1-R_3.
\]
Then \(u+t=w+z=v\), and
\[
v^2-(s_0-s_2)^2=4ut,\qquad v^2-(s_1-s_3)^2=4wz.
\]
If either product is nonpositive, (1) follows. Otherwise all four variables are positive. The geometric mean inequality \(\sqrt{(a+b)(c+d)}\ge\sqrt{ac}+\sqrt{bd}\), applied twice, gives
\[
D_0+D_1\ge\sqrt{wt}+\sqrt{zu}\ge2(utwz)^{1/4}.
\]
Thus \(2(D_0^2+D_1^2)\ge4\min(ut,wz)\), proving (1).

For nonnegative coefficients \(w_0,w_1,w_f\) with \(w_1\ge w_f\) and \(w_0(w_1-w_f)=w_f^2\), (1) implies
\[
w_0Q_0+w_1Q_1+w_f F\ge
(\sqrt{w_0Q_0}-\sqrt{(w_1-w_f)Q_1})^2\ge0. \tag{2}
\]
All row and column permutations of (2) hold.

## Passage to complex unitaries

Make one anchor row real using column phases. On its real orthogonal complement, the three other rows yield positive semidefinite real effects \(E_i=\operatorname{Re}(u_i u_i^*)\) with trace one and sum equal to the three-dimensional identity. Every extreme triple consists of three orthogonal rank-one projections. Indeed, if all ranks are at least two, the real spaces of symmetric perturbations on their ranges have total dimension at least nine. The trace and sum constraints impose at most eight independent equations. Perturbation in both signs contradicts extremality. If a trace-one effect has rank one, it is a projection. The other two sum to the identity on its two-dimensional complement and commute. Their spectral decomposition splits them into a mixture of two ordered orthogonal frames.

Every singleton and every anchored pair coordinate depends affinely on these effects. Every nonanchored pair is complementary to an anchored pair, and triple minors reduce to singletons. Thus a complex unitary profile is a convex combination of real orthogonal profiles. Applying (2) before averaging proves it for the original complex mixer. This argument also appears in the supplied archive in algebra_unitary_realification.md.

## Exact finite completeness

The companion moc4_hermitian_certificate.py uses Python's standard library. It checks all arithmetic below with integers or rational numbers.

The full permutation profiles have affine dimension thirteen. Their cone of nonnegative affine costs has 82 generating rays. There are 16 singleton coordinates, 18 pair coordinates up to complementation, and 48 distinct row and column relabelings of \(F\). The checker verifies completeness independently. It forms intersections of their supporting zero sets up to row and column relabeling. Each intersection is a face of the actual hull. All maximal chains have the same length, which attains the upper bound from the ambient dimension. Strict face inclusions then identify the actual dimension of each intersection. Within each candidate face, every ridge belongs to exactly two listed facets. By induction on dimension each listed facet contains all its true proper faces. Connectedness of the actual facet adjacency graph implies that the list is complete. The respective orbit counts in dimensions zero through thirteen are \(1,4,9,36,77,169,233,246,167,87,31,10,3,1\).

A rational row reduction gives ten independent constant and singleton coordinates and four additional pair coordinates. The projected cost space has dimension twelve including the constant, so it imposes two linear equations on the full fourteen-dimensional space. Write \(h=p/(1-2p)>0\). For the two pair rows chosen in the basis, if \(c_0,c_1\) are the coefficients on the two middle labels, the residual equation is \((1+h)c_0-hc_1=0\). The checker verifies the corresponding identities for all six pair rows.

A projected facet cost is a nonnegative combination of full facet rays whose weighted residual vectors in \(\mathbb R^2\) sum to zero. Every nonnegative dependence is a sum of support-minimal positive dependences, each of size at most three. A projected facet vanishes on at least eleven permutation vertices, since the projected polytope has affine dimension eleven. Every full facet ray with positive weight therefore vanishes on those same vertices.

The checker enumerates every support of at most three rays whose common zero set contains at least eleven vertices and which includes a mixed ray. One-ray and two-ray supports give no new condition for generic \(h>0\). With three rays their positive kernel weights, up to scaling, are their three cyclic two-by-two determinants. These are polynomials of degree at most two in \(h\). Every nonzero polynomial whose sign is needed has coefficients of one sign. The 96 surviving supports each have exactly eleven common zero vertices. Each is a relabeling of \(Q_0,Q_1,F\), with polynomial weights satisfying (2). Supports consisting entirely of ordinary rays are nonnegative on every unitary. Generic parameter values suffice, as membership in a convex hull with finitely many continuously varying vertices is closed. Thus the proposed unitary profile belongs to the projected permutation hull. This proves the theorem.

## Consequences

Apply the same Möbius map to \(\sigma(A)\) and \(-\sigma(B)\). The determinant and all comparison vertices acquire one common nonzero multiplier, when neither spectrum meets the pole. A generalized circle containing one spectrum can be mapped to the real line by choosing a pole on it away from the finitely many spectral values. This proves the generalized-circle case.

Theorem 19 in Y. Shitov, *A further sufficient condition for the determinantal conjecture*, lifts the Hermitian dimension-four base case to all orders when \(A\) is Hermitian and at most four eigenvalues of \(B\) are nonreal. Möbius covariance extends this to a common generalized circle containing all \(a_i\) and at least \(n-4\) of the reflected values \(-b_j\). The proof leaves unrestricted order four with two nonconcyclic spectra unresolved.
