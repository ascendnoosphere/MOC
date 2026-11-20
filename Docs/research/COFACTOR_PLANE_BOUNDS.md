# The scalar Schur bound on three individual complex cofactor planes

This closes a necessary Gram-completion test on each of three two-real-dimensional coordinate planes. It is **not** a support theorem for all unitaries, not the bound on their mixed span, and not a simultaneous PSD completion.

The first plane was derived in the [trace-oracle report](projector_trace_schur_lemmas.md). The main agent independently checked the identities for all three planes over every one of the 70 formal identity-contact compound coefficient directions.

## Statement and exact coefficient identities

Assume identity supports at the original 24-product height and \(g>0\). Let \(C\) have just \(C_{ij}=x+iy\), \(C_{ji}=x-iy\) nonzero, and put \(v=\operatorname{coords}C\). Write \(k\) for the remaining diagonal index.

Use the following inverse four-cycle pairs, with original support gaps \(\delta_+,\delta_-\), and let \(S=\delta_++\delta_-\):

| Plane | Ordered inverse four-cycle pair | Multiplier relating \(e_{\Im ij}\) to \((\delta_--\delta_+)/2\) |
|---|---|---:|
| \(C_{12}\) | \((1243),(1342)\) | + |
| \(C_{13}\) | \((1324),(1423)\) | − |
| \(C_{23}\) | \((1234),(1432)\) | − |

Here \(\delta_+\) belongs to the first listed cycle and \(\delta_-\) to the second. The multiplier does not affect the squared inequality. [Independent mathematical audit](u_zero_and_planes_independent_review.md): VALID. In each plane the canonical coefficients satisfy
\[
 A_{kk}=g,\qquad
 (D_0)_{\Re ij,\Re ij}=2g,\qquad
 (D_0)_{\Re ij,\Im ij}=0,
\]
\[
 (D_0)_{\Im ij,\Im ij}+2g=2S,\qquad
 e_{\Re ij}=0.
\]
Also
\[
 \ell_v=\operatorname{coords}\operatorname{adj}C
 =-(x^2+y^2)\operatorname{coords}E_{kk}.
\]
These are exact coefficient identities, not fits to spectral samples.

## Analytic inequality

For the scalar necessary condition define
\[
 \mathcal R(v)=g\,v^TD_0v+
 2g^{3/2}\sqrt{\ell_v^TA\ell_v}-(e^Tv)^2.
\]
The identities above give
\[
 \mathcal R(v)=4g^2x^2+(2gS-e_*^2)y^2.
\]
The original supporting inequalities give \(S\ge2|e_*|\). The already-proved signed three-cycle formula gives \(|e_*|\le2g\). Therefore
\[
 e_*^2\le2g|e_*|\le gS,
\qquad
 \boxed{\mathcal R(v)\ge4g^2x^2+gS\,y^2\ge0.}
\]

The branch \(g=0\) is separately covered by the [complete boundary completion](universal_sos_boundary_completion_lemmas.md).

