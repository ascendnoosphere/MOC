## 1. Polynomial model and canonical gauge — VALID

The coordinate convention is
\[
(T_{11},T_{22},T_{33},\Re T_{12},\Im T_{12},
 \Re T_{13},\Im T_{13},\Re T_{23},\Im T_{23}),
\]
with upper-triangular entries \(T_{ij}=x+iy\), not \(x-iy\). This matters for the plane signs. The implementation agrees with that convention at `organized/research/rational_sinkhorn_certificates.py:105–106`.

The compound model is consistent with the Cayley chart. Writing \(C=\operatorname{adj}T\), \(d=\det T\),
\[
\delta_-=1-\operatorname{tr}C+i(d-\operatorname{tr}T),
\]
\[
N_+=(1+\operatorname{tr}C-id)I-2C
       +i(2T-\operatorname{tr}T\,I),
\]
gives \(V=N_+/\delta_-\). The wedge-square numerator is \(J\overline{N_+}J\); the ordering and signs of \(J\) match the ordered pair basis \((12,13,23)\). Taking squared moduli of the resulting minor numerators produces the matrices used by the verifiers (`organized/research/rational_sinkhorn_certificates.py:117–131`).

There is also no missing factor of two in the gauge conversion. For a raw matrix \(M\), quartic terms are
\[
c^TM_{cc}c+2d\,M_{td}^Tt.
\]
Using \(dt=\operatorname{coords}(\operatorname{adj}C)\) yields
\[
D_0=M_{cc}+2\sum_jM_{t_jd}L_j.
\]
Restoring a \(t\)-to-\(d\) Gram block \(u\) consequently requires
\[
D(u)=D_0-2L(u),
\]
exactly as stated in `universal_sos_mechanism_lemmas.md` and implemented in `organized/research/verify_cofactor_plane_bounds.py:19–20`.

The cubic freedom \(K\) changes only the \(t,c\) cross-block; it cannot change \(D(u)\). This follows from the homogeneous-degree separation and the identities \(TC=CT=dI\), \(\operatorname{adj}C=dT\), not from an optimizer.


## 3. Three cofactor planes — VALID

Let \(\delta_+\) correspond to the first listed cycle and \(\delta_-\) to its inverse. The correct formulas for the actual imaginary-coordinate entry \(e_{\Im ij}\) are:

| Plane | Ordered inverse pair | \(e_{\Im ij}\) |
|---|---|---|
| \(C_{12}\) | \((1243),(1342)\) | \((\delta_--\delta_+)/2\) |
| \(C_{13}\) | \((1324),(1423)\) | \(-(\delta_--\delta_+)/2\) |
| \(C_{23}\) | \((1234),(1432)\) | \(-(\delta_--\delta_+)/2\) |

The zero-based image tuples in `organized/research/verify_cofactor_plane_bounds.py:22` represent exactly these cycles and their inverses. The computed signs agree.

**Minor presentation improvement:** the heading “Sign of \(e_*=(\delta_--\delta_+)/2\)” is ambiguous: the sign of that numerical difference is not fixed. It should say “Multiplier relating \(e_{\Im ij}\) to \((\delta_--\delta_+)/2\).” The mathematics and verifier use the correct interpretation (`organized/research/COFACTOR_PLANE_BOUNDS.md:13–17`).

For every plane, with remaining index \(k\), the checked identities are
\[
A_{kk}=g,\quad D_{rr}=2g,\quad D_{ri}=0,\quad
D_{ii}=2S-2g,\quad e_r=0,
\]
where \(S=\delta_++\delta_-\). These are linear coefficient identities, checked on every one of the 70 formal compound directions, not spectral fits (`organized/research/verify_cofactor_plane_bounds.py:17–28`).

Directly taking the adjugate of the plane matrix gives
\[
\ell_v=-(x^2+y^2)\operatorname{coords}E_{kk}.
\]
Hence, for \(g>0\),
\[
\sqrt{\ell_v^TA\ell_v}=\sqrt g\,(x^2+y^2).
\]
Substitution therefore gives exactly
\[
\mathcal R(v)=4g^2x^2+(2gS-e_{\Im ij}^2)y^2.
\]

### The analytic bound has verified premises

Nonnegative original support gaps imply
\[
|\delta_--\delta_+|\le\delta_-+\delta_+,
\qquad S\ge2|e_{\Im ij}|.
\]

The other premise is not established merely by the new plane verifier’s `PASS`. I separately checked the signed-three-cycle identities coefficientwise against all 70 compound directions:
\[
g=\frac18\sum_{\sigma\text{ a 3-cycle}}\Delta_\sigma,
\qquad
e_{\Im ij}=\frac14\sum_\sigma s_{\sigma,ij}\Delta_\sigma,
\quad s_{\sigma,ij}\in\{-1,1\}.
\]
These agree with the boundary argument and sign table at `universal_sos_boundary_completion_lemmas.md`. Since every \(\Delta_\sigma\ge0\),
\[
|e_{\Im ij}|\le\frac14\sum_\sigma\Delta_\sigma=2g.
\]
Consequently,
\[
e_{\Im ij}^2\le2g|e_{\Im ij}|\le gS,
\]
and
\[
\boxed{\mathcal R(v)\ge4g^2x^2+gS\,y^2\ge0.}
\]
Thus the proof at `organized/research/COFACTOR_PLANE_BOUNDS.md:38–51` is sound.

