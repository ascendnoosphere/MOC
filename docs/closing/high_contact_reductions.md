# Contact-transfer and zero-capacity reductions for complex MOC

**Scope:** This note proves a contact-transfer theorem for the full problem, with arbitrary unitary mixing. It does not resolve unrestricted MOC. The remaining terminal configurations are genuine configurations of distinct spectra and distinct matching products; their positivity has not been proved. No priority claim is made for the theorem.

For subsequent order-four closures, see the [verified-results overview](../geometry/MOC4_Verified_Results.md). The [closing index](README.md) groups the original derivations and independent audits.

## The conjecture and the result

Fix a unitary matrix \(U\in U(n)\), and write
\[
 d_U(a,b)=\det(\operatorname{diag}a+U\operatorname{diag}b\,U^*),
 \qquad z_\pi(a,b)=\prod_{i=1}^n(a_i+b_{\pi(i)}).
\]
MOC asserts \(d_U(a,b)\in\operatorname{conv}\{z_\pi(a,b)\}\).

**Contact-transfer theorem, \(n\ge4\).** Suppose there is a strict violation in a support direction \(|\eta|=1\):
\[
 g=\Re(\eta d_U(a,b))-\max_\pi\Re(\eta z_\pi(a,b))>0.
\]
Then there are finite complex spectra \(a',b'\), with the **same \(U\), the same \(\eta\), and the same positive gap \(g\)**, for which all \(n!\) matching products are nonzero and pairwise distinct, and at least \(2n-2\) of them lie on the supporting line
\[
 \Re(\eta z)=\max_\pi\Re(\eta z_\pi(a',b')).
\]
In particular, a strict counterexample in order four would also exist at spectra with at least six distinct products on one supporting line. This theorem concerns the whole unitary group, not a restricted circuit family.

Pairwise distinct matching products also force each individual spectrum to have distinct eigenvalues: repeating an eigenvalue makes two products related by a transposition equal.

## Proof

### 1. The matching cone has complex dimension \(2n-2\)

For a matrix \(C=(c_{ij})\) of rank at most two, let
\[
 Z(C)_\pi=\prod_i c_{i,\pi(i)},
\]
and let \(Y\subset\mathbb C^{n!}\) be the Zariski closure of these vectors. The rank-at-most-two matrix variety is irreducible of dimension \(4n-4\).

On its open subset with no zero entries, the matching-product vector determines every rectangle cross-ratio: divide the products of two permutations differing only by the assignments in two rows. Equality of all these ratios implies
\[
 C'=\operatorname{diag}(r)\,C\,\operatorname{diag}(s).
\]
Equality of the matching products themselves adds \(\prod_i r_i\prod_j s_j=1\). After removing the redundant scaling \((r,s)\mapsto(tr,t^{-1}s)\), this fiber has dimension \(2n-2\). Hence
\[
 \dim_{\mathbb C}Y=(4n-4)-(2n-2)=2n-2=:D.
\]

These matching coordinates are actual finite spectral coordinates on a dense Zariski-open subset. Indeed, a generic rank-two factorization can be written
\[
 c_{ij}=x_i s_j+y_i t_j
       =y_i s_j\left(\frac{x_i}{y_i}+\frac{t_j}{s_j}\right),
\]
with all displayed denominators nonzero, after a generic change of basis in the two-dimensional factor space. Every matching product acquires the same nonzero factor \(L=\prod_i y_i\prod_j s_j\). Absorb \(L\) into the spectra using any complex \(n\)-th root. Constructibility of the image supplies a dense Zariski-open subset \(O\subset Y\) with finite spectral realizations. We may take \(O\) invariant under nonzero common scaling.

### 2. A quartet prevents translation curves

Choose four matching coordinates obtained by independently swapping two disjoint pairs of assignments, holding all other assignments fixed. They have the form
\[
 z_{00}=R x_0y_0,\quad z_{01}=R x_0y_1,\quad
 z_{10}=R x_1y_0,\quad z_{11}=R x_1y_1.
\]
Consequently
\[
 z_{00}z_{11}-z_{01}z_{10}=0,
 \qquad \Gamma=z_{00}+z_{11}-z_{01}-z_{10}
                 =R(x_0-x_1)(y_0-y_1).
\]
The polynomial \(\Gamma\) is generically nonzero. Adding a common scalar \(c\) to all four coordinates changes the left-hand side of the quadratic identity by exactly \(c\Gamma\). Thus a nonconstant curve in \(Y\) on which all matching-coordinate differences are constant is impossible wherever this chosen \(\Gamma\ne0\).

Shrink \(O\) to also require \(\Gamma\ne0\), and all matching coordinates nonzero and pairwise distinct. A strict counterexample can be perturbed into this open set. If the perturbation changes its positive gap from \(g\) to \(g'\), scaling both spectra by the positive number \((g/g')^{1/n}\) restores the gap \(g\).

### 3. Keep the actual violation fixed on a complex curve

For the fixed unitary \(U\), define the complex linear functional
\[
 L_U(z)=\sum_{\pi\in S_n}
 \frac{\operatorname{sgn}(\pi)\prod_i u_{i,\pi(i)}}{\det U}\,z_\pi.
\]
The determinant expansion gives \(L_U(Z(a,b))=d_U(a,b)\). The coefficients sum to one. Their positivity is neither asserted nor used.

Let \(p\in O\) be a strict counterexample, and suppose exactly \(k<D\) matching labels are active on its supporting line. Choose one active label \(\pi_0\). Inside \(Y\), impose the following \(k\) complex affine equations:

1. Fix \(z_\pi-z_{\pi_0}\) at its value at \(p\), for each of the other \(k-1\) active labels.
2. Fix \(L_U(z)-z_{\pi_0}\) at its value at \(p\).

Every component of this fiber through \(p\) has dimension at least \(D-k\ge1\). Select an irreducible algebraic curve through \(p\) in the fiber, normalize it, and compactify the normalization to a compact Riemann surface. Remove the finitely many points at infinity and the finitely many points mapping outside \(O\). The remaining surface \(S\) is connected, and all matching coordinates are meromorphic on its compactification.

The old active labels remain tied throughout \(S\); they remain active wherever \(\pi_0\) is maximizing. At every such point the actual support gap stays exactly \(g\), because \(L_U-z_{\pi_0}\) was fixed as a complex number.

### 4. The curve must reach another finite support contact

For each formerly inactive label, set
\[
 \delta_\pi(z)=\Re\{\eta(z_{\pi_0}-z_\pi)\}.
\]
Let \(\Omega\) be the component containing the chosen lift of \(p\) of the open set where every such deficit is strictly positive.

If \(\Omega\) has a boundary point in \(S\), continuity makes all deficits nonnegative there, with at least one formerly inactive deficit zero. This is a finite, actual spectral configuration in \(O\), with a new support contact and the same positive violation.

Suppose instead that \(\Omega\) has no boundary in \(S\). Connectedness gives \(\Omega=S\). Each meromorphic function \(\eta(z_{\pi_0}-z_\pi)\) then has nonnegative real part on all of \(S\). A pole on the compactification would force its real part to take both signs arbitrarily close to that pole. Therefore it has no poles, and is constant on the compact surface. All matching-coordinate differences are constant.

The curve must consequently be a common translation of its value at \(p\). The quartet identity and \(\Gamma(p)\ne0\) force that translation to be constant. This contradicts the choice of a nonconstant curve in \(Y\).

A finite new contact therefore exists. Repeat the argument until at least \(D=2n-2\) labels are active. Every step stays in \(O\), preserves \(U\) and \(\eta\), and preserves the gap \(g\). This proves the theorem.

## Why this does not yet close MOC

The next proof obligation is **every such terminal spectral configuration satisfies MOC for every unitary \(U\)**. The transfer theorem localizes that obligation; the closing inequality remains open in general.

High contact does not itself force repeated spectra, zero products, or coincident matching products. Moreover, the transfer mechanism also applies to other complex linear functionals of the matching coordinates. It does not use the special unitary restrictions on the coefficients strongly enough to prove terminal positivity. Those restrictions must enter the closing inequality.

## One boundary class was excluded

For the order-four cycle with gates \((12),(34)\) followed by \((13),(24)\), let \(\delta_s\ge0\) be its sixteen actual spectral support deficits, indexed by \(s\in\{0,1\}^4\), and let \(\bar s\) be the bitwise complement. Define
\[
 B=2\sum_{\{s,\bar s\}}\sqrt{\delta_s\delta_{\bar s}},
 \qquad K=\sum_s(-1)^{|s|}\delta_s.
\]
The algebraic branch established the boundary implication
\[
 \boxed{B=0\quad\Longrightarrow\quad K=0.}
\]
Its proof uses the supplied volume's complete 82-ray cone description. This round derives the required degree-18 polynomial bound directly from a rank-four Hessian identity and verifies its vanishing on actual spectral data. The finite part covers all 96 relevant zero-budget faces by two symmetry types and verifies strictly nonzero polynomial factorizations whenever their alternating gap is nonzero. The checker performs 67,298 exact interpolation evaluations; the proved degree bound makes these a polynomial identity certificate, not numerical evidence.

This excludes an entire boundary obstruction. It does not prove \(B\ge|K|\) for positive \(B\), and the cycle inequality itself would still require further work to settle unrestricted MOC. The precise hypotheses, factorizations, imported results, and verification code are included in the bundle.

It also excludes every zero-capacity obstruction in this order-four cycle: pairwise arithmetic–geometric mean gives
\[
 \operatorname{Cap}(\delta):=\inf_{x\in\mathbb R^4}
 \sum_s\delta_s e^{\langle2s-\mathbf1,x\rangle}\ge B.
\]
Thus \(\operatorname{Cap}(\delta)=0\) forces \(K=0\) for actual spectral data.

## Verification and companion material

The accompanying bundle contains independent derivations of the contact argument, exact polynomial verification of the quartet identity, the cycle-capacity extension, and exact stationary-matrix checks. The theorem above is a mathematical argument; the algebraic-geometry steps are justified in the proof, rather than inferred from numerical tests.

