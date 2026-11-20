# A conditional local-to-open theorem for complex MOC

## Status and scope

This note supplies a proof of a local theorem, subject to independent review. It does not prove unrestricted MOC. No historical priority is claimed.

The key point is that a solved spectral degeneration can imply a genuine open set of solved spectra if every exposed equality locus is contained in a solved block family and the support is strictly concave in directions normal to that family. This argument does not imply that the open set extends across an arbitrary later degenerate contact.

## 1. Statement

Assume complex MOC holds in every dimension less than n. Fix

\[
A_0=\operatorname{diag}(a,b,c,\ldots,c),\qquad
B_0(U)=U\operatorname{diag}(\beta_1,\ldots,\beta_n)U^*.
\]

For ordered distinct labels i,k define

\[
g_{ik}=(a+\beta_i)(b+\beta_k)
\prod_{j\ne i,k}(c+\beta_j).
\tag{1}
\]

**Theorem.** Suppose the n(n−1) complex numbers g_ik are pairwise distinct and no three are collinear over R. Then an open neighborhood of the spectral pair

\[
((a,b,c,\ldots,c),(\beta_1,\ldots,\beta_n))
\]

in C^n×C^n satisfies MOC(n), for every relative unitary U.

In particular, the lower-dimensional hypothesis is satisfied for n=4 by the elementary dimension-at-most-three minor law. Hence the theorem gives an open set of full complex MOC4 instances around each rank-two perturbation of a scalar matrix satisfying the stated finite general-position condition.

The result is invariant under relabeling. The genericity assumption is an explicit sufficient condition, not a claim that the remaining nongeneric cases fail MOC.

## 2. Exact oriented-row law at the base spectrum

Work in the eigenbasis of B. Let r,s be the two orthonormal vectors giving the exceptional eigenspaces of A_0. Put

\[
q_{ik}=|r_is_k-r_ks_i|^2\quad(i<k).
\]

There exists a probability law w_ik on ordered distinct labels with

\[
w_{ik}+w_{ki}=q_{ik},\quad
\sum_{k\ne i}w_{ik}=|r_i|^2,\quad
\sum_{i\ne k}w_{ik}=|s_k|^2.
\tag{2}
\]

For completeness, this is a fractional orientation of edges with masses q. The necessary and sufficient outgoing-degree cuts are

\[
q(S)\le\sum_{i\in S}|r_i|^2.
\]

Cauchy–Binet verifies them because

\[
q(S)=\|r_S\|^2\|s_S\|^2-|\langle r_S,s_S\rangle|^2
\le\|r_S\|^2.
\]

Total edge mass is one, and the degree identity gives the incoming marginals. The orientation feasibility assertion also follows from the elementary capacitated-flow cut theorem.

Set α=a−c, δ=b−c, Q=∏_j(c+β_j), and temporarily assume c+β_j≠0. With γ_j=(c+β_j)^{-1}, the determinant lemma gives

\[
\frac{\det(A_0+B_0(U))}{Q}
=1+\alpha\sum_i|r_i|^2\gamma_i
+\delta\sum_k|s_k|^2\gamma_k
+\alpha\delta\sum_{i<k}q_{ik}\gamma_i\gamma_k.
\]

Using (2), this equals

\[
\sum_{i\ne k}w_{ik}(1+\alpha\gamma_i)(1+\delta\gamma_k).
\]

Multiplication by Q proves the exact identity

\[
\boxed{\det(A_0+B_0(U))=\sum_{i\ne k}w_{ik}g_{ik}.}
\tag{3}
\]

Both sides are polynomial in the spectra, so zeros of c+β_j are included. The law w depends on r,s and not on the spectra.

## 3. All exposed equality loci

Fix η with |η|=1, write G_ik=Re(ηg_ik), and let h=max G_ik. By the general-position assumption, the exposed maximizer set F contains one or two ordered pairs. Let

\[
\Delta=\min_{(i,k)\notin F}(h-G_{ik})>0.
\]

Equation (3) gives

\[
h-\operatorname{Re}(\eta\det(A_0+B_0(U)))
\ge\Delta\sum_{(i,k)\notin F}w_{ik}.
\tag{4}
\]

At equality, every law in (3) has support contained in F.

### One ordered pair

If F={(i,k)}, the marginals force r=e^{iθ}e_i and s=e^{iφ}e_k. The other n−2 rows form an arbitrary U(n−2) block. Moreover,

\[
h-\operatorname{Re}(\eta d_0(U))
\ge\frac\Delta2(2-|r_i|^2-|s_k|^2).
\tag{5}
\]

### Two pairs with the same first label

If F={(i,k),(i,l)}, equality forces r=e^{iθ}e_i and s∈span(e_k,e_l). The equality locus is contained in the larger solved block family S_i in which r is a coordinate vector and the other n−1 rows are unrestricted. Equation (4) gives

\[
h-\operatorname{Re}(\eta d_0(U))\ge\Delta(1-|r_i|^2).
\tag{6}
\]

The case of a common second label is identical, with s fixed.

### Reversed pairs

If F={(i,k),(k,i)}, the marginals and orthogonality force r,s to be an orthonormal basis of span(e_i,e_k). The remaining vectors lie in its complement. This is a U(2)×U(n−2) block family. Equation (4) yields

\[
h-\operatorname{Re}(\eta d_0(U))
\ge\frac\Delta2\left(
\sum_{j\notin\{i,k\}}|r_j|^2+
\sum_{j\notin\{i,k\}}|s_j|^2\right).
\tag{7}
\]

### All other two-pair faces

Write F={(i,k),(j,l)} with distinct first labels, distinct second labels, and without reversal. If the law puts masses θ,1−θ on these pairs, the marginals force

\[
|r_i|^2=|s_k|^2=\theta,\quad
|r_j|^2=|s_l|^2=1-\theta.
\]

If {i,j} and {k,l} intersect in exactly one label, orthogonality has only one potentially nonzero term and forces θ(1−θ)=0. If the two sets are disjoint, the minor q_ik equals θ² but (2) makes it θ, again forcing θ∈{0,1}. Intersection in two labels would be precisely the reversed case already removed. Hence the equality locus is the disjoint union of the two one-pair block families.

This classification is valid for complex r,s; no realification is used.

## 4. The transverse Hessian is strictly negative

For the one-pair, shared-label and reversed cases, inequalities (5)–(7) directly give a strictly negative support Hessian in every direction normal to the indicated block family, at its maximizing points. Each right-hand side is a positive definite quadratic form on that normal space to second order.

For the remaining two-pair case, consider a maximizing component with r=e_i,s=e_k after phase gauge. A tangent variation has

\[
\dot r_k=z,\qquad\dot s_i=-\bar z.
\]

An expansion of (3), or directly of the rank-two determinant formula, gives

\[
\begin{aligned}
h-\operatorname{Re}(\eta d_0(U(t)))
=t^2\bigg[& (h-G_{ki})|z|^2\\
&+\sum_{j\ne i,k}(h-G_{jk})|\dot r_j|^2\\
&+\sum_{j\ne i,k}(h-G_{ij})|\dot s_j|^2\bigg]+O(t^3).
\end{aligned}
\tag{8}
\]

There are no mixed quadratic terms. At this component the second-order ordered masses are

\[
w_{ki}=t^2|z|^2,quad
w_{jk}=t^2|\dot r_j|^2,quad
w_{ij}=t^2|\dot s_j|^2,
\]

with the corresponding mass removed from w_ik, to second order. The same expansion follows directly by expanding the q coefficients and the two singleton marginals, so it does not depend on choosing a differentiable orientation law.

The other maximizing pair is neither reversed nor shares an index in the corresponding position. Thus every coefficient displayed in (8) is strictly positive. The only zero modes change the complementary U(n−2) block or phases already included in the block family.

Compactness of each equality locus supplies a uniform negative bound on the normal Hessian there.

## 5. Why every perturbed objective still has zero normal derivative

Let S be any of the block families above, specified by a partition of the row labels and a matching partition of the column labels. For arbitrary perturbed diagonal spectra a',β', a matrix U∈S makes

\[
D_{a'}+UD_{\beta'}U^*
\]

block diagonal in the row partition. A tangent vector normal to S is generated by a skew-Hermitian matrix with off-block entries. Its first variation of UD_β'U* is off-block.

The derivative of the determinant is tr(adj(C)\dot C). The adjugate of a block-diagonal matrix is block diagonal, including singular cases by polynomial continuation. Therefore this trace is zero. Taking Re η preserves zero.

Consequently, for every spectral perturbation and support phase, the support objective has exactly zero first derivative in every normal direction at every point of S. This is an algebraic identity, not an assumption about generic stationarity.

## 6. Why the block families remain solved under perturbation

Every block has dimension less than n, except scalar factors, and the lower-dimensional hypothesis gives a positive permutation law in each block. Multiplying these laws gives a positive law on full permutations preserving the block partition. Thus, for every U∈S and every perturbed spectral pair,

\[
\operatorname{Re}(\eta d(U))\le
\max_{\pi\in S_n}\operatorname{Re}(\eta z_\pi).
\tag{9}
\]

For n=4 the largest block is three-dimensional. The dimension-three law itself is elementary: complementary minors reduce all squared minors to |U_ij|²; a Birkhoff decomposition of that doubly stochastic matrix preserves every coefficient in the determinant expansion.

## 7. Local spectral stability at one support phase

Take the finitely many block families covering the equality locus for a fixed η. Use normal tubular coordinates U=exp(K)U_0 near a family S, where K is normal to S and U_0∈S.

At base maximizing points, the normal Hessian is strictly negative by Section 4. By continuity, it remains uniformly negative for U_0 in a sufficiently small neighborhood of the equality locus inside S, for small K, and for sufficiently small spectral and phase perturbations. The linear term in K is identically zero by Section 5.

Taylor's theorem with its integral remainder therefore gives

\[
F_{a',\beta',\eta'}(\exp(K)U_0)
\le F_{a',\beta',\eta'}(U_0),
\tag{10}
\]

with strict inequality for nonzero small K. The right side is bounded by the permutation support by (9).

Outside these neighborhoods of the base equality locus, the base support gap is uniformly positive because U(n) is compact. Both the determinant objective and the finite permutation maximum vary uniformly continuously with the spectra and phase. After shrinking the perturbation neighborhood, the positive gap remains positive on this complement.

This proves MOC support stability near the fixed base phase. The argument does not require a chosen permutation to remain the unique support maximizer under perturbation.

## 8. Uniformity over the support circle

Apply Section 7 to every |η|=1. The base support circle is compact, so finitely many of the resulting phase neighborhoods cover it. Intersect their spectral neighborhoods. This intersection is an open neighborhood of the base spectral pair. Every support direction for every spectral pair in it is controlled by one member of the finite cover.

The separation characterization of planar convex hulls now proves MOC on the entire spectral neighborhood. This completes the theorem.

## 9. The corresponding CH support neighborhood

In the four-dimensional coefficient normalization, the solved line λ_0=λ_1=κ has vertices

\[
g_{ik}=\beta_i\prod_{j\ne i,k}(1+\beta_j),
\]

and the same oriented-row law applies to rows 1 and 3. Under the distinctness and no-three-collinear condition on these twelve points, the identical block and compactness argument supplies ε(β)>0 such that

\[
D_0+tD_1\in\operatorname{conv}\{D_{0,\pi}+tD_{1,\pi}:\pi\in S_4\}
\quad\text{whenever }|t-1|<\varepsilon(\beta).
\]

This controls all complex support phases and all U∈U(4). A finite Möbius normalization translates it to a neighborhood of a double eigenvalue in the first spectrum, with the other three eigenvalues and the transformed second spectrum fixed.

The condition is nonempty. For β=(5+4i,−8+18i,−9−6i,−5−12i), the twelve values g_ik are distinct and their 220 triple orientation determinants are all nonzero by exact integer arithmetic.

## 10. The precise continuation limitation

The proof uses a special equality-locus theorem at a scalar-plus-rank-two spectrum. At a later point on an arbitrary spectral path, a support maximizer may be a genuinely noncommuting relative unitary outside every proper block family. A zero or positive normal Hessian at such a contact is not excluded by the argument above.

The finite cover in Section 8 covers support phases at one base spectral pair. It is not a finite cover of all spectra. Iterating local neighborhoods without a theorem classifying every possible first-failure contact would be a gap.
