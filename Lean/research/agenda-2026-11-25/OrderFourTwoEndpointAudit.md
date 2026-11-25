# The order-four two-endpoint theorem and the separate contact step

The supplied 66-page [Zheng preprint](https://doi.org/10.13140/RG.2.2.36790.25923) states two different claims. Theorem 1.2 concerns the squared minors of a unitary matrix. Proposition 4.4 concerns the sign of an actual spectral support objective on real orthogonal matrices. The first is a reduction for the second, not a proof of it.

## A checked replacement for the Picard-curve argument

Dephase one row of a unitary \(U\in U(4)\) so that its entries are real. This preserves every squared minor. Complete that row to a real orthogonal basis. In that basis the remaining unitary block is a \(3\times3\) matrix \(W\). Its real row effects are the real symmetric matrices
\[
  E_i=\operatorname{Re}(w_i^*w_i),
\]
where \(w_i\) is a row of \(W\). Each \(E_i\) is positive semidefinite of trace one and rank at most two, and \(\sum_i E_i=I_3\).

The key improvement over a finite convex mixture is that **two real bases suffice**. If one effect has rank one, it is an orthogonal projection. The remaining effects are complementary on its orthogonal plane. Diagonalizing on that plane gives a mixture of two bases that exchange the two complementary axes. If the original tuple has all effects of rank two, choose a real orthonormal two-column frame \(X_i\) for each effect:
\[
  E_i=X_i\,\operatorname{diag}(p_i,q_i)\,X_i^t,\qquad
  p_i,q_i>0,\qquad p_i+q_i=1.
\]
A traceless symmetric perturbation in each plane gives six real variables. The zero-sum constraint takes values in the five-dimensional space of traceless symmetric \(3\times3\) matrices. A nonzero zero-sum perturbation exists. Move both ways along it as far as positivity permits. The compressed \(2\times2\) determinants bound the interval, and at each endpoint at least one effect is rank one.

At an endpoint write \(F_i=X_iH_iX_i^t\), and let \(A=F_i\) be one rank-one effect. It is a projection, so \(F_jA=F_kA=0\) for the other two indices. If both \(H_j,H_k\) were invertible, premultiplication by \(X_j^t,X_k^t\) would give \(X_j^tA=X_k^tA=0\); hence \(E_jA=E_kA=0\). It follows that \(E_iA=A\). Applying \(X_i^t\) shows
\[
  \operatorname{diag}(p_i,q_i)X_i^tA=X_i^tA.
\]
Both \(p_i\) and \(q_i\) are strictly less than one, so \(X_i^tA=0\) and then \(A=0\), contrary to trace one. Thus another endpoint effect has rank one. Two rank-one effects in such a triple necessarily give one orthogonal basis tuple. The two ends of the interval are therefore basis tuples, not two further convex mixtures.

The existing fixed-row transport takes the same basis weights to the squared singleton minors and squared two-minors containing the selected row. Complementary minors then cover the other two-minors and the three-minors. The empty and full minors are constant. This proves the two-endpoint squared-minor statement without invoking elliptic curves, density, or computation on contact sets.

## Paper audit

The Picard proof in §2 is a separate route, with no dependence on the exceptional-contact supplement. It uses the smooth elliptic quartic cut out by the quadrics through the eight ordered columns, the degree-two linear system on its Picard curve, and a real circle selected by Gale duality and conjugation. The rank and sign of the diagonal relation are needed to recover real orthogonal representatives at its endpoints. In the extracted text several conjugation bars are not visible. The unitary identity is \(U^{-t}=\overline U\); the relevant Gale relation is to the conjugate configuration, not to the same configuration.

Proposition 4.4 assumes an **actual** point of the matching-profile cone, nonnegative projected gaps, and at least six zero gap labels. It does not assume exactly six, distinct matching values, simple spectra, or positive cone coefficients. It invokes the minor-facet reduction for one collection of orbit types and Proposition 4.3 for another. The supplied PDF contains one detailed exceptional case, \(T_{85}\), which itself uses preceding cases \(T_{40},T_{55},T_{81}\). Appendices F and G describe which checks and proof dependencies appear in the separate materials. They do not provide the omitted derivations.

The [author's research page](https://denzelzheng.com/mathematics/) points to the [preprint DOI](https://doi.org/10.13140/RG.2.2.36790.25923). Its publication record exposed one author-uploaded full text. I did not locate separate files for supplements S0, S1 or S2 there or on the research page. That is a retrieval limitation, not evidence against the claim. The repo's sharper seven-contact reduction lowers the remaining proof scope; it does not verify the exceptional terminal inequalities.
