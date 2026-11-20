# Independent referee notes: broader MOC classes

This is an independent mathematical audit of the team's second round of results. It is not a claim of formal verification or literature priority. The unrestricted Marcus–de Oliveira conjecture has not been proved or disproved here.

## 1. Strongest elementary result: a zero paired sum in dimension four

**Verdict: the proof passes.** For arbitrary normal 4-by-4 matrices, MOC holds if an eigenvalue of one is the negative of an eigenvalue of the other. This condition is equivalent to at least one permutation vertex being zero. It does not require a common eigenvector.

After relabeling and opposite scalar shifts, take

\[
A=\operatorname{diag}(0,a_1,a_2,a_3),\qquad
B=\operatorname{diag}(0,b_1,b_2,b_3).
\]

Let \(T=\{1,2,3\}\), and for an arbitrary \(U\in U(4)\) set

\[
r=1-|U_{00}|^2,\quad x_i=|U_{i0}|^2,\quad y_\ell=|U_{0\ell}|^2,
\qquad Q_{i\ell}=|\det U_{\{0,i\},T\setminus\{\ell\}}|^2.
\]

The exact identities are

\[
\sum_\ell Q_{i\ell}=r-x_i,\qquad
\sum_i Q_{i\ell}=r-y_\ell,\qquad
\sum_i x_i=\sum_\ell y_\ell=r.
\]

The row identity follows by Cauchy–Binet from the Gram matrix \(I_2-vv^*\), with \(v=(U_{00},U_{i0})^T\). The column identity follows by complementary unitary minors and the same argument. Thus, if \(r>0\),

\[
D=\frac1r\begin{pmatrix}Q&x\\ y^T&0\end{pmatrix}
\]

is doubly stochastic. Every permutation in a Birkhoff decomposition of \(D\) avoids its bottom-right zero entry; its upper-left block is a size-two matching of \(K_{3,3}\). The induced matching law has edge marginals \(Q_{i\ell}/r\), missing-row marginals \(x_i/r\), and missing-column marginals \(y_\ell/r\).

For a matching with edges \((i_1,\ell_1),(i_2,\ell_2)\), missing row \(h\), and missing column \(k\), define

\[
\pi(0)=h,\qquad \pi(k)=0,\qquad
\pi(\ell_1)=i_2,\qquad \pi(\ell_2)=i_1.
\]

This crossing is essential. It bijects the 18 size-two matchings and the 18 permutations with \(\pi(0)\ne0\). Its vertex expands as

\[
z_\pi=a_Tb_k+a_hb_T+
\sum_{(i,\ell)\in M}a_{T\setminus\{i\}}b_{T\setminus\{\ell\}}.
\]

Meanwhile, the determinant's squared-minor expansion reduces exactly to

\[
d=a_T\sum_\ell y_\ell b_\ell+
\sum_{i,\ell}Q_{i\ell}a_{T\setminus\{i\}}b_{T\setminus\{\ell\}}+
b_T\sum_i x_i a_i.
\]

Thus the matching law, multiplied by \(r\), gives \(d\). Put the remaining mass \(1-r\) on the identity permutation, whose vertex is zero. All weights are nonnegative and normalized. If \(r=0\), all displayed coefficients vanish and \(d=0\), so the result is immediate.

This proves the claim by a genuine probability construction. It reproduces only the 15 squared minors that occur after setting \(a_0=b_0=0\); it never assumes the false existence of a simultaneous nonnegative law for every minor of an arbitrary unitary.

I independently checked the surviving coefficient indices, both marginal identities, the matching/permutation bijection, the missing-row and missing-column interpretation, and the degenerate case. The exact checker `certificates/zero_paired_sum_n4/verify_zero_paired_sum.py` also passes all 18 combinatorial identities and a rational Birkhoff decomposition for the previously obstructive quaternion matrix.

**Scope:** This supersedes the narrower all-unitary family \(a=(0,1,2,t)\), \(b=(0,1,z,2+z)\); those two statements should not be counted as two independent gains. It does not cover arbitrary spectra in dimension four, or arbitrary relative unitary matrices in higher dimensions.

## 2. Generic large scalar shifts in every dimension

**Verdict: the complete proof in `proofs/large_shift_all_dimensions.md` passes this informal audit.**

For fixed spectra, form the trace-assignment polygon from

\[
s_\pi=\sum_i a_i b_{\pi(i)}.
\]

Assume it is two-dimensional, each exposed vertex corresponds to exactly one permutation, and each edge contains exactly two assignment points. Then some finite \(R(a,b)\) has the property that MOC holds for \(sI+A\) and \(B\), for every complex \(|s|>R\) and every unitary relative basis.

The important proof checks are these:

1. After subtracting common Taylor coefficients from \(\det(I+t(A+UBU^*))\) and dividing by \(t^2\), the normalized objective converges in \(C^2\), uniformly in complex argument, to \(-\operatorname{tr}(AUBU^*)\).
2. Birkhoff's theorem classifies leading maximizing doubly stochastic matrices. A two-permutation exposed edge has a single relative cycle. A cycle of length at least three has no interior unistochastic point, because two rows would share exactly one nonzero column. A transposition instead gives a genuine \(U(2)\) block manifold.
3. Leading maximizers have strictly negative Hessians normal to these compact manifolds. For the block case, the elementary Birkhoff gap bound gives a uniform estimate in terms of the squared entries outside the permitted block support. This estimate remains valid at block endpoints.
4. Exact determinant objectives are normally stationary on these same fixed block manifolds for every perturbation parameter and support direction. The adjugate stays block diagonal even at singular matrices, so there is no hidden invertibility assumption.
5. A compact tubular-neighborhood argument prevents nearby maxima from leaving the manifolds. A finite cover of the support-direction circle gives one threshold uniform over all directions and all unitaries.
6. On these manifolds the determinant is either a permutation vertex or a two-vertex convex combination.

The stronger hypothesis that all trace-assignment points are distinct and no three collinear is open and dense. Its proof uses the fact that a holomorphic rational function taking only real values must be constant, which would otherwise make three distinct permutation matrices collinear.

**Scope:** This theorem supplies an existential threshold, not a numerical bound. It changes the spectra by a sufficiently large scalar shift and therefore does not prove the original unshifted pair. No assertion of literature priority has been established.

## 3. Fourier bases in dimensions six, seven, and eight

**Verdict: exact common nonnegative minor laws have been independently verified.** The construction data are in `certificates/fourier/exact_fourier_laws.json`. The laws are supported on explicit affine-action orbits of permutations and have rational or cyclotomic orbit masses.

To avoid merely rerunning the author's code, I wrote `certificates/fourier/check_fourier_gram.py`. It computes squared Fourier minors as Gram determinants over the exact cyclotomic field, uses the supplied masses without solving for them, and counts each permutation event directly. The original construction instead computes a determinant and its conjugate. The independent integer-arithmetic checks pass:

| Dimension | Minor equations checked for \(k\le n/2\) | Result |
|---|---:|---|
| 6 | 662 | All exact equalities hold |
| 7 | 1716 | All exact equalities hold |
| 8 | 8885 | All exact equalities hold |

Complementary unitary minors give the remaining equations. All orbit masses are strictly positive and sum to one; for dimension seven their positivity follows from elementary rational bounds for \(2\cos(2\pi/7)\), and for dimension eight from \(5/4<\sqrt2<3/2\).

Consequently MOC holds for arbitrary complex spectra with these Fourier relative bases. The output records are `certificates/fourier/fourier_gram_audit.json` and the author's exact certificate files. This is one constructive method with several verified dimensions; whether one calls the dimensions separate “classes” is a matter of bookkeeping, not a mathematical doubling of an established catalogue.

## 4. Full neighborhoods of the Fourier bases in dimensions five and seven

**Verdict: the common-law perturbation argument and explicit radii pass.**

For any unitary matrix, the real signed weights

\[
\rho_\pi(U)=\Re\left(\frac{\operatorname{sgn}(\pi)\prod_jU_{\pi(j),j}}{\det U}\right)
\]

have total mass one and reproduce every squared minor. This follows directly from determinant expansion and Jacobi's complementary-minor identity. If a strictly positive common law \(p^0\) is known at \(U_0\), then

\[
p_\pi(U)=p^0_\pi+\rho_\pi(U)-\rho_\pi(U_0)
\]

still reproduces all minors. Positivity holds in a full neighborhood, not just on a special family of unitaries.

For \(F_n\), an entrywise perturbation bound \(\max_{ij}|U_{ij}-(F_n)_{ij}|\le\delta\) gives

\[
|\rho_\pi(U)-\rho_\pi(F_n)|
\le n\delta\left[(n^{-1/2}+\delta)^{n-1}+n^{-(n-1)/2}\right].
\]

The first term is a product telescoping estimate. The second follows from the determinant column-telescoping estimate \(|\det U-\det F_n|\le n\sqrt n\delta\), using unit column norms.

For \(n=5\), the law

\[
p^0_\pi=\frac{1-1/\sqrt5}{120}
+\frac1{10\sqrt5}\mathbf1_{\{\pi(j)=\pm2j+b\pmod5\}}
\]

is strictly positive. Its singleton and pair marginals can be checked directly from the ten indicated affine maps; complementary minors give all degrees. The bound at \(\delta=1/100\) is smaller than its minimum weight.

For \(n=7\), the explicit law in `certificates/fourier/exact_interior7.json` mixes four affine-action orbits with a uniform law of mass

\[
\kappa=(9-3t-3t^2)/7,\qquad t=2\cos(2\pi/7).
\]

The bound \(31/25<t<5/4\) gives \(\kappa>9/112\), hence each permutation weight exceeds \(1/62720\). The perturbation bound at \(\delta=1/3000\) is smaller. I independently checked all 1716 minor identities for this strictly positive law by the Gram-determinant method; the record is `certificates/fourier/fourier_gram_audit.json` (final entry).

Thus arbitrary spectra are covered on explicit full-dimensional open neighborhoods in \(U(5)\) and \(U(7)\).


## 6. Literature checks and limits

Primary sources consulted include Shitov's 2025 theorem and introductory list of known cases (`https://www.mathnet.ru/eng/im9292`), Drury's 1999 Householder theorem (`https://www.sciencedirect.com/science/article/pii/S0024379599001731`), Drury's 2006 essentially-Hermitian paper (`https://journals.uwyo.edu/index.php/ela/article/download/403/403/403`), Kovačec's 1994 multiplicity result (`https://www.sciencedirect.com/science/article/pii/0024379594901074`), and Li–Poon–Sze's paper on ranks and determinants from unitary orbits (`https://cklixx.people.wm.edu/detrank.pdf`).

The last paper discusses common eigenvalues in rank and sharp-point results; the passages examined do not supply the zero-paired-sum inclusion above. Searches of the available primary literature and surveys did not locate that exact statement or the generic large-shift theorem. This search is incomplete and does not justify claiming either theorem as new to the literature.

The strongest result for a short final explanation is the zero-paired-sum theorem: its proof is elementary, exact, and constructs the probability distribution explicitly. The large-shift theorem is broader in dimension but requires a longer stability argument. Fourier laws and their open neighborhoods provide separately checkable all-spectra relative-basis classes.
