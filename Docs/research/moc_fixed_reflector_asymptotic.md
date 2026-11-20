# Why a fixed number of random reflectors becomes a weak large-n test

The sweep in `code/research/moc_campaign_large.py` uses at most eight
Householder reflectors. This allows every dimension through 1000 to be sampled,
but it creates a specific asymptotic bias. For two independent, identically
distributed circular spectra, the determinant becomes small relative to the
natural permutation product as dimension grows with reflector count fixed.
The following statement explains that bias. It does not establish MOC.

**Proposition.** Fix an integer r >= 1. Let the pairs `(a_i,b_i)` be independent
and identically distributed, with `a_i` and `b_i` independent standard circular
complex Gaussian variables. The same conclusion holds if both variables are
uniform in the unit disk. Independently choose r uniform unit vectors
`v_1,...,v_r` in C^n, and put

\[
 U_n=\prod_{j=1}^r(I-2v_jv_j^*),\qquad
 A_n=\operatorname{diag}(a_1,\ldots,a_n),\quad
 B_n=\operatorname{diag}(b_1,\ldots,b_n).
\]

Then, as n tends to infinity with r fixed,

\[
 \frac{\det(A_n+U_nB_nU_n^*)}{\prod_{i=1}^n(a_i+b_i)}
 \longrightarrow 0
 \quad\text{in probability}.
\]

The denominator is nonzero almost surely. Under the natural coupling obtained
by normalizing the first n coordinates of fixed independent infinite Gaussian
sequences, convergence holds almost surely.

**Proof.** Write `V=[v_1 ... v_r]`. Multiplying the reflectors gives
`U=I+VTV*`, where T is upper triangular, its diagonal entries are -2, and

\[
 T_{1:j-1,j}=-2T_{1:j-1,1:j-1}V_{1:j-1}^*v_j.
\]

The law of large numbers gives `V*V -> I_r`, so `T -> -2I_r`.
Set `D=A+B` and define

\[
 G=V^*BV,\quad Q=V^*D^{-1}V,\quad
 Q_b=V^*D^{-1}BV,\quad Q_{bb}=V^*D^{-1}B^2V.
\]

For any integrable function f of a spectral pair, independent normalized
Gaussian vectors satisfy

\[
 V^*\operatorname{diag}(f(a_i,b_i))V
 \longrightarrow \mathbb E[f(a,b)]I_r.
\]

To see this entrywise, write `v_j=g_j/||g_j||`. The numerator divided by n is
the average of independent integrable variables
`conj(g_ij) g_ik f(a_i,b_i)`. Its limit is
`delta_jk E[f(a,b)]`, while both normalization factors divided by `sqrt(n)`
tend to one.

The needed reciprocal terms are integrable. For the disk law, all numerators
are bounded and the planar singularity `1/|a+b|` is locally integrable. For the
Gaussian law, put `d=a+b` and `e=a-b`; d and e are independent Gaussian
variables, and expand `b=(d-e)/2`. Finite Gaussian moments and
`E[1/|d|]<infinity` then give integrability of `1/d`, `b/d`, and `b^2/d`.

Simultaneous circular rotation of a and b gives

\[
 \mathbb E[b]=\mathbb E[(a+b)^{-1}]
 =\mathbb E[b^2/(a+b)]=0.
\]

Exchangeability, together with `a/(a+b)+b/(a+b)=1`, gives
`E[b/(a+b)]=1/2`. Consequently,

\[
 G\to0,\qquad Q\to0,\qquad Q_b\to\tfrac12I_r,
 \qquad Q_{bb}\to0.
\]

The determinant lemma gives the exact identity

\[
 \frac{\det(A+UBU^*)}{\det D}=\det(I_{2r}+MS),
\]

where

\[
 M=\begin{pmatrix}TGT^*&T\\T^*&0\end{pmatrix},
 \qquad
 S=\begin{pmatrix}Q&Q_b\\Q_b&Q_{bb}\end{pmatrix}.
\]

Indeed, `UBU*-B=WMC` with `W=[V,BV]` and
`C=[V*;V*B]`, and `S=CD^{-1}W`. No conjugate of b appears in S because B
is a general complex diagonal matrix.

The limits above yield

\[
 M\longrightarrow\begin{pmatrix}0&-2I_r\\-2I_r&0\end{pmatrix},
 \qquad
 S\longrightarrow\begin{pmatrix}0&\tfrac12I_r\\\tfrac12I_r&0\end{pmatrix}.
\]

Thus `I_{2r}+MS -> 0`, and continuity of the determinant proves the claim.

The proposition gives no rate. Reciprocal terms have heavy tails, so assigning
an ordinary finite-variance central-limit rate without further work would be
unjustified. It also gives no containment statement for the permutation hull.
Its practical consequence is that increasing n while holding reflector count
at 2, 4, or 8 changes the numerical experiment: it drives the determinant
toward zero relative to one available permutation vertex. Tests of difficult
unrestricted behavior therefore need full unitary mixing and targeted
boundary optimization in addition to this broad dimension sweep.

A separate Gaussian probe used 12 trials for each pair `(n,r)`. Its median
natural logarithm of the absolute determinant ratio was:

| n | r = 2 | r = 4 | r = 8 |
|---:|---:|---:|---:|
| 100 | -4.017 | -6.305 | -10.202 |
| 1000 | -6.844 | -13.836 | -23.963 |
| 10000 | -10.998 | -21.980 | -38.791 |

Run `python code/research/moc_fixed_reflector_probe.py` to reproduce this table.
The raw output is
`build/moc_campaign_20261031/fixed_reflector_asymptotic_probe.json`.
These 108 auxiliary computations illustrate the proposition; they are separate
from the MOC containment dataset because they do not sample permutation hulls.
