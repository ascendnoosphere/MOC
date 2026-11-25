# Contact transfer with a varying determinant gap

**Status.** Paper proof of a stronger terminal reduction, with an independent adversarial review. The exact affine-line case is Lean-checked in `ContactAffineRigidity.lean`. The compactified-curve argument below is not Lean-checked. The terminal inequality remains open.

## Statement

Let \(n\ge2\). Fix a strict witness, its mixer \(U\), its support phase \(\eta\ne0\), a maximizing matching \(r\), and the set \(T\) of contact labels. If \(|T|\le 2n-2\), there is another strict witness with the same \(U,\eta,r\), a strictly larger contact set containing \(T\), and the same complex differences \(P_r-P_q\) for \(q\in T\). The determinant gap can change. Thus MOC in order \(n\) is equivalent to its support bound on exact profiles with at least \(2n-1\) contact labels. Products need not be nonzero or distinct. More generally, a contact-maximal strict witness must have at least \(2n-2\) independent contact-difference functions on the exact profile locus.

## Profile facts and tangent identity

Let \(X\subset\mathbb C^{S_n}\) be the exact matching-profile locus. It is Euclidean-closed and prime affine, with dimension \(2n-2\) (`MatchingProfileClosed.lean`, `GlobalContactSlice.lean`, `ProfileDimension.lean`). It is a complex cone: multiply both spectra by a common \(n\)th root of the required profile factor.

For the fixed mixer let \(w_\sigma=\operatorname{realSignedWeight}(U,\sigma)\). The signed expansion gives the complex-linear functions
\[
G(P)=\sum_\sigma w_\sigma\eta(P_\sigma-P_r),\qquad
F_\sigma(P)=\eta(P_r-P_\sigma).
\]
At the strict witness, \(\Re G>0\) and \(\Re F_\sigma\ge0\), with equality on precisely \(T\). Exact collinear profiles satisfy MOC, including lines missing the origin (`CollinearKernelSupport.lean`). Also, if \(d_\sigma=c+\sum_j Q_j(\sigma j)\), the signed expectation \(\sum_\sigma w_\sigma d_\sigma\) belongs to the hull of the entries of \(d\), whether or not \(d\) is exact. The Birkhoff law for the singleton marginals \(|U_{ij}|^2\) has the same expectation (`Weights.lean`, `holds_of_singleton_expansion`).

**Tangent identity.** Suppose \(Q^{(s)}=1+\epsilon_s d^{(s)}\in X\), where \(\epsilon_s\ne0\), \(\epsilon_s\to0\), and \(d^{(s)}\to d\) coordinatewise. Then \(d\) has a singleton expansion.

Fix an anchor \(o\). For a column \(j\) and row \(i\), put \(\alpha(j,i)=\beta(j,i)=\mathrm{id}\) if \(j=o\) or \(i=o\); otherwise put \(\alpha(j,i)=(j\ i)\) and \(\beta(j,i)=(j\ i)(o\ j)\). Composition acts right to left. For an exact profile \(Q\) with every coordinate nonzero, the swap identity gives
\[
\frac{Q_{\alpha(j,i)}}{Q_{\beta(j,i)}}=
\frac{(a_i+b_j)(a_o+b_o)}{(a_i+b_o)(a_o+b_j)}.
\]
Every entry is nonzero since it belongs to a nonzero matching. Multiplying the quotients over \((j,\sigma j)\) and comparing with the identity matching gives
\[
Q_\sigma\prod_j Q_{\beta(j,\sigma j)}\prod_j Q_{\alpha(j,j)}
=Q_{\mathrm{id}}\prod_j Q_{\alpha(j,\sigma j)}\prod_j Q_{\beta(j,j)}.
\]
This identity is `translation_eval_relation` in `GeneralContactReduction.lean`. All coordinates of \(Q^{(s)}\) are eventually nonzero. Substitute \(Q^{(s)}\) in the identity, subtract 1 from both sides, and divide by \(\epsilon_s\). For finitely many convergent \(u_k^{(s)}\), the quotient \((\prod_k(1+\epsilon_s u_k^{(s)})-1)/\epsilon_s\) tends to \(\sum_k u_k\): the degree-one terms give this sum and every higher term retains a factor of \(\epsilon_s\). Therefore
\[
d_\sigma=d_{\mathrm{id}}
+\sum_j \bigl(d_{\alpha(j,\sigma j)}-d_{\beta(j,\sigma j)}\bigr)
-\sum_j \bigl(d_{\alpha(j,j)}-d_{\beta(j,j)}\bigr).
\]
This is the asserted singleton expansion. Lean checks this limit in
[`singleton_expansion_of_matching_profile_tangent_at_one`](MOC/GeneralContactReduction.lean).
It uses a filter limit and does not require a smooth lift to spectra.

## Varying-gap continuation

Pin only \(P_r-P_q\) for \(q\in T\setminus\{r\}\). There are \(|T|-1<2n-2\) equations. The [checked curve selector](MOC/GlobalContactSlice.lean), `exists_prime_profile_curve_fixing_observables`, supplies an irreducible affine curve \(C\subset X\) through the strict witness inside this slice. There is no smoothness or transversality requirement at the witness. If \(G\) is constant on \(C\), the checked fixed-gap argument applies (`AffineContactCurve.lean`). A translation-only variation cannot be the whole curve, by the checked translation obstruction.

Suppose \(G\) is nonconstant. Let \(Y\) be the nonsingular projective model of \(C\). The affine normalization lies in \(Y\) with finite complement \(E\), maps onto \(C\), and carries the pulled-back regular profile coordinates. All coordinates extend meromorphically to \(Y\). See [Stacks Project, normalization](https://stacks.math.columbia.edu/tag/0BXQ), [Curves](https://stacks.math.columbia.edu/tag/0A22), and [nonsingular projective models](https://stacks.math.columbia.edu/tag/0BY1). Let \(y_0\) be a lift of the initial witness in the affine normalization. Let \(\Omega\) be the connected component containing \(y_0\) of \(\{\Re G>0\}\) in the complement of the poles of \(G\). Deleting \(E\) from \(\Omega\) leaves it connected: a connected open real surface remains path connected after deleting finitely many points.

Assume no point of \(C\) gives a strict witness with an additional contact and all the old ones. Then every \(\Re F_\sigma\ge0\) on \(\Omega\setminus E\). Otherwise the continuous minimum of the deficits outside \(T\) would take a negative value there after being positive at \(y_0\). A zero of this minimum gives precisely the required strict profile: all projected deficits are nonnegative, the old deficits are zero, and the gap is still positive.

The closure of \(\Omega\) meets a pole of \(G\). Otherwise the harmonic function \(\Re G\) would attain a positive maximum on the compact closure. Every boundary point is regular and has \(\Re G=0\), since \(\Re G>0\) at a regular point gives a connected neighborhood in the positive set. Hence the maximum is interior. The harmonic maximum principle and analytic continuation would make \(G\) constant, a contradiction.

At a pole of order \(m\ge1\), choose a small local coordinate \(t\) such that \(G=t^{-m}\). This uses a local analytic \(m\)th root of the nonvanishing unit in \(G^{-1}\). In a small punctured disk the positive region consists of \(m\) open sectors of angle \(\pi/m\). At least one meets \(\Omega\), and that entire connected sector lies in \(\Omega\). Shrink the disk to exclude other points of \(E\) and rotate \(t\) by an \(m\)th root of unity to center the sector on the positive real ray.

If \(F_\sigma\) has a pole of order \(\ell>0\) with leading coefficient \(\gamma\ne0\), then on each ray \(|\theta|<\pi/(2m)\),
\[
\lim_{u\downarrow0}u^\ell\Re F_\sigma(ue^{i\theta})
=\Re(\gamma e^{-i\ell\theta})\ge0.
\]
For \(\ell>m\), the argument \(-\ell\theta\) varies over an interval longer than \(\pi\), so it cannot fit in a single cosine-nonnegative half-circle after the constant phase shift. For \(\ell=m\), the interval has length exactly \(\pi\); its center must be a cosine maximum, so \(\gamma>0\) is real. If the order is less than \(m\), or the function is regular, its quotient by \(G\) tends to 0. This proves that on the central ray \(F_\sigma/G\to c_\sigma\in\mathbb R_{\ge0}\). Every old locked difference gives \(c_q=0\).

Now the meromorphic function \(P_r/G\) has either a finite limit or a pole. Both cases contradict the strict gap:

1. If \(P_r/G\) has a finite limit, all coordinates \(P_\sigma/G\) converge because \((P_r-P_\sigma)/G=F_\sigma/(\eta G)\) converges. The limit \(d\) is exact by cone closedness. Its coordinates are collinear, since \(\eta(d_r-d_\sigma)=c_\sigma\in\mathbb R\); the pivot remains maximal, and \(G(d)=1\). The collinear comparison forbids this.
2. If \(P_r/G\) has a pole, put \(\epsilon=G/P_r\) and \(d^{(t)}_\sigma=(P_\sigma-P_r)/G\) on the central ray near zero. Then \(P/P_r=1+\epsilon d^{(t)}\in X\) with \(\epsilon\ne0\) tending to zero and \(d^{(t)}\to d\). The tangent identity gives a singleton expansion for \(d\). Again \(\eta(d_r-d_\sigma)=c_\sigma\ge0\) and \(G(d)=1\). The singleton comparison forbids this.

A new contact must occur. Repeating this step until the count exceeds \(2n-2\) proves the claimed reduction.

The same proof applies when the count is large but the differences have
rank less than \(2n-2\). Pin a basis of the span of actual profile
differences rather than all the labels. Their values then pin every old
difference on the exact locus, by complex linearity. The basis selection
is the one used in the [fixed-gap rank lemma](MOC/ContactDifferenceRank.lean);
here there is no extra gap equation. Hence a witness with maximal
contact count has rank at least \(2n-2\).

## Formalization boundary

The existing transfer strategy follows D. Zheng, *The Marcus–de Oliveira conjecture for n = 4*, Theorem 3.6, [DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923). The varying-gap argument above is separate. The
[limit obstruction](MOC/ContactAsymptoticObstruction.lean) proves a contradiction in
both cases of the common-coordinate dichotomy from the stated limit inputs.
The [positive-component lemma](MOC/PositiveComponentBoundary.lean) also
checks the compactness step conditional on no positive local maximum.
The remaining Lean inputs are the compactified model and its analytic
maximum principle, meromorphic pole normalization, and the angular
comparison. The affine-line specialization is Lean-checked and implies that at a contact-maximal witness any free partner entry changes an old complex contact difference, without a determinant-gap alternative.
