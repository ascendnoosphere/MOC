# Independent audit of the nonarchimedean determinant range

**Verdict: the proposed exact range theorem is correct with inverse conjugation by integral invertible matrices.** This is a valued-field analogue, not the complex Marcus–de Oliveira conjecture.

Let \(K\) be any nonarchimedean valued field, with valuation ring \(\mathcal O=\{x:|x|\le1\}\). No completeness or local compactness is needed. Let \(A=\operatorname{diag}(a_i)\) and \(B=\operatorname{diag}(b_i)\), with entries in \(K\), and define

\[
z_\pi=\prod_j(a_{\pi(j)}+b_j),\qquad
R=\max_\pi|z_\pi-z_{\pi_0}|
\]

for any fixed permutation \(\pi_0\). Then

\[
\{\det(A+UBU^{-1}):U\in GL_n(\mathcal O)\}
=\{z\in K:|z-z_{\pi_0}|\le R\}.
\]

The same range results from \(SL_n(\mathcal O)\).

For containment, determinant expansion gives

\[
\det(A+UBU^{-1})=\sum_\pi c_\pi z_\pi,
\quad c_\pi=\frac{\operatorname{sgn}(\pi)\prod_jU_{\pi(j),j}}{\det U}.
\]

Every \(c_\pi\in\mathcal O\), because \(\det U\) is a unit, and \(\sum c_\pi=1\). The ultrametric inequality gives the stated containment. The radius \(R\) equals the diameter of the finite vertex set and is independent of the choice of center vertex.

For the reverse inclusion, connect permutation vertices using transposition edges. The graph is connected. Along any path the ultrametric distance between endpoints is no greater than the largest edge distance. Therefore some transposition edge has distance exactly \(R\). Let its vertices be \(z_\pi,z_\tau\).

Conjugate the corresponding two diagonal positions using

\[
G(t)=\begin{pmatrix}1&1\\t&1+t\end{pmatrix},\qquad t\in\mathcal O.
\]

Its determinant is one. A direct 2-by-2 calculation, with the other diagonal factors fixed, gives

\[
\det(A+G(t)P_\pi B P_\pi^{-1}G(t)^{-1})
=(1+t)z_\pi-tz_\tau.
\]

If \(R>0\), these values fill

\[
z_\pi+(z_\pi-z_\tau)\mathcal O
=\{z:|z-z_\pi|\le R\}.
\]

The radius is attained by a field element, so no issue about missing values in the value group arises. If \(R=0\), containment already says that the range is the singleton vertex. This also handles \(n=1\).

Finally, multiply any \(U\in GL_n(\mathcal O)\) on the right by a diagonal unit matrix of determinant \((\det U)^{-1}\). This leaves \(UBU^{-1}\) unchanged and makes the conjugator have determinant one. Thus the \(GL\) and \(SL\) ranges coincide.

All signs, the transposition interpolation, the determinant-unit condition, and the degenerate cases were independently checked. Replacing \(U^{-1}\) by an adjoint, imposing a p-adic unitary group, or interpreting the ball as an ordinary real convex hull would change the theorem and is not justified by this proof.
