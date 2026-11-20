## Round 020: the same support gap has a coherent quadratic proof

### Spectral data and matrix definitions

The specified spectra and phase are those displayed in the retained [full-unitary companion theorem](polyhedral_certificate_separation.md):
\[
a=\left(0,\frac12,1,\frac{15-3i}{26}\right),\quad
b=\left(\frac{-2+i}{3},\frac{-11+3i}{26},\frac{-14-6i}{29},-\frac23\right),\quad
\eta=\frac{819-351i}{128},\quad h=\frac3{64}.
\]
Its Section 3 gives the equivalent coefficient-hull parameters \(\beta,\lambda_0,\lambda_1\). All 54 rational parameters and all 32 PSD blocks are retained in the [exact quadratic certificate](../../../data/certificates/theorems/support_certificates/polyhedral_counter_quadratic_exact.json); the [finite spectral certificate](../../../data/certificates/theorems/support_certificates/polyhedral_enlarged_counter_exact.json) supplies the original spectral-product correspondence.

For the real unit anchor \(v\), put \(p_\beta=\prod_j\beta_j\), \(w=D_\beta v\), and
\[
T_\beta=(1+\textstyle\sum_j\beta_jv_j^2)D_\beta-ww^T.
\]
In the proof below, \(M=\operatorname{Re}(\lambda_1T_\beta)|_{v^\perp}\) and \(L=\operatorname{Re}(\lambda_0p_\beta T_{1/\beta})|_{v^\perp}\); the latter is called \(N\) in the retained [fixed-row SDP formulation](../profile_geometry/verified_results.md#the-exact-fixed-row-sdp).

The correction matrices \(K_\nu\) are covariance factors of the certificate's diagonal and pair blocks, not additional unspecified witness data. Their covariance, the two slack forms, and the budget are reconstructed from the saved parameters by `blocks(z)` and `polynomial_identities(z)` in the retained [standalone verifier](../../../code/theorems/support_certificates/polyhedral_counter_quadratic_verify.py). In its indexing, `z[:4]` and `z[4:8]` give the coefficient vectors of \(\alpha\) and \(\gamma\) against \((v_j^2)_j\); `z[8:20]`, `z[20:26]`, and `z[38:44]` determine the pair and diagonal correction covariances. Any factors of those same PSD covariance blocks give the displayed sum defining \(Y\). This is a theorem for this specified spectral direction, not all directions or unrestricted MOC.

The 54 rational parameters in `polyhedral_counter_quadratic_exact.json`
reconstruct exactly the 32 listed positive semidefinite blocks. The independent
code checks all 100 nonempty principal minors of those blocks, including the
singular ones; every minor is nonnegative. It also verifies the correspondence
between the CH coefficients and all 24 original finite spectral products.
The author's standalone verifier independently expands the two slack
polynomial identities and the scalar budget identity.

Here is why these finite identities prove the full complex unitary bound.
Write the rows as \(r,v,s,t\). Column phases make the anchor \(v\) real.
On \(H=v^\perp\), the constructed correction has the form

\[
Y=P\left(\sum_\nu K_\nu vv^T K_\nu^T\right)P\succeq0,
\qquad P=I-vv^T.
\]

The positive correction blocks are exactly covariance matrices for its
diagonal and pair character components. The first and second slack Gram
conditions give

\[
Y+\alpha I_H-M\succeq0,
\qquad
Y+\gamma I_H-L\succeq0.
\]

For example, setting \(e_i=r_iv_i\), each real homogeneous slack is

\[
e^TGe+
\sum_{i<j}(r_iv_j,r_jv_i)
\begin{pmatrix}D_{ij}&t_{ij}\\t_{ij}&D_{ji}\end{pmatrix}
\binom{r_iv_j}{r_jv_i}.
\]

The allocation terms cancel because
\(r_iv_jr_jv_i=e_ie_j\). Orthogonality imposes \(\sum_i e_i=0\), so
positivity of \(E^TGE\) is exactly the required positivity of the diagonal
part on that subspace. The real symmetric forms are also positive on the
complexification; equivalently one applies the same forms to the real and
imaginary parts.

The budget matrix is \(B=T+N\), with \(T\succeq0\) and \(N\) entrywise
nonnegative. For \(p_i=v_i^2\), its exact identity is

\[
h-\operatorname{tr}Y-\alpha-\gamma=p^TBp\ge0.
\]

Since \(r,s,t\) form a complex orthonormal basis of \(H\),

\[
r^*Mr+s^*Ls
\le\alpha+\gamma+r^*Yr+s^*Ys
=\alpha+\gamma+\operatorname{tr}Y-t^*Yt\le h.
\]

This establishes the support bound for every \(U\in U(4)\). This proves the actual support inequality for the specified spectral data.


## Round 024: the elliptic finite-jet criterion and exact old-point instance

The general theorem in `global_bridge_geometry.md` is valid. At a local
support maximum of \(f=c\cdot\Phi\), one has \(df=0\) and
\(\operatorname{Hess}f\preceq0\). The asserted operator identity gives

\[
\operatorname{tr}(W\operatorname{Hess}f)+v\cdot df=0.
\]

If \(W\succ0\), then the trace identity forces
\(\operatorname{Hess}f=0\). Indeed, conjugating the negative semidefinite
Hessian by \(W^{1/2}\) gives a negative semidefinite matrix of trace zero.
If the combined first and second derivatives span the translated affine
hull, the coefficient \(c\) is then constant on that affine hull. This
excludes every nontrivial relative supporting hyperplane. Compactness gives
a support hyperplane at every relative boundary point, proving relative
interiority.

The drift term makes the operator statement compatible with a change of
tangent coordinates. The proof is entirely finite dimensional and local;
it does not assume an elliptic differential equation on a neighborhood.

For `global_bridge_elliptic_exact.json`, the independent verifier constructs
the entry derivatives from \(\exp(\sum t_iK_i)O\), and differentiates each
two-minor by the product rule. It does not reuse the author's compound
representation generators. It verifies orthogonality and determinant one,
all 52 operator equations, trace \(W=1\), and exact positive LDL pivots of
\(W-I/1500\). The ranks are exactly

\[
\operatorname{rank}G=6,\qquad
\operatorname{rank}(G,H)=13,\qquad
\operatorname{rank}(\text{operator equations plus trace})=14.
\]

The profile affine dimension is 13, so the spanning hypothesis is met.
The seven normal Hessian directions are therefore annihilated by a strictly
positive quadratic form in the stated sense.

The same rational orthogonal point already had a positive fourteen-permutation
profile law in the prior campaign. The new result is a general finite-jet
mechanism and a different certificate at this point; its interiority is not
a newly discovered fact. It proves nothing about every inaccessible point.

