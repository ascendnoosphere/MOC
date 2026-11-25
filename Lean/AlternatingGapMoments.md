# Alternating gap moments

This is a necessary condition on any realizable matching profile, independent of the mixer. No permutation enumeration or numerical fitting enters the proofs.

Let \(p_\sigma=\prod_i(a_{\sigma(i)}+b_i)\), \(d_\sigma=H-\operatorname{Re}(\eta p_\sigma)\). The Lean results in [AlternatingGapMoments.lean](MOC/AlternatingGapMoments.lean) are:

* If \((r+1)(s+1)<n\), the alternating mixed moment \(\sum_\sigma\operatorname{sgn}(\sigma)p_\sigma(a,b)^r p_\sigma(c,d)^s\) vanishes for any four spectra. Its determinant kernel has a binomial factorization of width \((r+1)(s+1)\).
* For \(n\ge4\),
  \[
  \sum_\sigma\operatorname{sgn}(\sigma)d_\sigma^2
  =\tfrac12|\eta|^2\det\bigl(|a_i+b_j|^2\bigr).
  \]
  The constant and linear terms vanish by determinant kernels of widths one and two. In \(2(\operatorname{Re}z)^2=\operatorname{Re}(z^2)+|z|^2\), the first summand has width three. The remaining planar squared-distance kernel has width four.
* For \(n=4\) write \(\Delta(a)=\det[1,\operatorname{Re}a_i,\operatorname{Im}a_i,|a_i|^2]_i\). The second moment is \(-2|\eta|^2\Delta(a)\Delta(b)\). For \(\eta\ne0\) it vanishes exactly when one spectrum lies on a generalized circle. The converse proof extracts a nonzero circle equation from a kernel vector; coincident labels are allowed.
* For \(n\ge5\), the even and odd gap second moments agree. [Lean also checks this on every partial matching fibre with at least five free labels](MOC/AlternatingGapFibre.lean), with no assumption on the product over fixed labels.

The relevant external context is the Hadamard-product rank factorization of G. P. H. Styan, [DOI](https://doi.org/10.1016/0024-3795(73)90023-2), and the squared-distance lift of J. C. Gower, [DOI](https://doi.org/10.1016/0024-3795(85)90187-9). For current literature on feature dimension and higher powers of Euclidean distance matrices, see B. Horvat, A. Orbanić and I. Kavkler, [open preprint DOI](https://doi.org/10.48550/arXiv.2607.09671). The individual matrix-rank bounds used here are proved directly; no exact-rank theorem for symmetric distance matrices is assumed. The lifted determinant is the usual planar incircle test; see J. R. Shewchuk, [DOI](https://doi.org/10.1007/PL00009321) and [author copy](https://people.eecs.berkeley.edu/~jrs/jrspapers.html). This development uses no floating-point implementation or sign predicate from that work.

**Further consequences on paper.** For a real degree-\(k\) polynomial in \(d_\sigma\), its alternating average vanishes whenever \(\max_{r+s\le k}(r+1)(s+1)=\lfloor(k+2)^2/4\rfloor<n\), by expanding into matching products and their conjugates. If one parity's gap values are restricted to \(t\) values and the degree- \(2t\) budget holds, the other parity has gaps only in the same set: use the nonnegative squared polynomial vanishing at the \(t\) values. If one parity class has only a single positive gap, agreement of degrees one and two forces exactly one positive gap of the same value on the other; apply \((\sum x)^2-\sum x^2=2\sum_{i<j}x_i x_j\) to the nonnegative gaps. These are checks on a prospective terminal profile, not a bound for arbitrary feasible gap profiles or a solution of the conjecture.

For the order-four \(T_{85}\) discussion in [Zheng's preprint](https://doi.org/10.13140/RG.2.2.36790.25923), the formula supplies a nonzero quadratic invariant if both spectra are nonconcyclic. This alone does not force a forbidden gap sign on the remaining positive-height branch, and it is not a proof of Proposition 4.4.
