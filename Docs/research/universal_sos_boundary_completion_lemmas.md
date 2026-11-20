## 1. Notation and the spectral gap identity

Keep the **original** height
\[
h=\max_{\pi\in S_4}\Re\!\left(\eta z_\pi\right),
\qquad
z_\pi=\prod_{i=1}^4(a_i+b_{\pi(i)}).
\]
Assume identity supports, and set
\[
\Delta_\pi=h-\Re(\eta z_\pi)\ge0,\qquad \Delta_{\mathrm{id}}=0.
\]

Use the stated Hadamard/Cayley chart and coordinates
\[
c=(C_{11},C_{22},C_{33},
       \Re C_{12},\Im C_{12},
       \Re C_{13},\Im C_{13},
       \Re C_{23},\Im C_{23}),
\qquad C=\operatorname{adj}T.
\]
These are exactly the coordinate conventions in
`organized/research/rational_sinkhorn_certificates.py:105–106`.

The matrix \((a_i+b_j)\) has rank at most two. Consequently, fixing the fourth pairing and alternating over any three indices gives
\[
z_{\mathrm{id}}+z_{(ijk)}+z_{(ikj)}
=z_{(ij)}+z_{(ik)}+z_{(jk)}.
\]
Taking support gaps yields the exact identity
\[
\boxed{\Delta_{(ijk)}+\Delta_{(ikj)}
=\Delta_{(ij)}+\Delta_{(ik)}+\Delta_{(jk)}.}
\tag{1}
\]

Sum (1) over the four triples. Every transposition occurs twice:
\[
\sum_{\sigma\text{ a 3-cycle}}\Delta_\sigma
=2\sum_{i<j}\Delta_{(ij)}.
\]
The reflection-average formula therefore sharpens to
\[
\boxed{
g=\frac18\sum_{\sigma\text{ a 3-cycle}}\Delta_\sigma
=\frac14\sum_{i<j}\Delta_{(ij)}.
}
\tag{2}
\]

The existing obstruction script checks the reflection average and quadratic gap formula separately; see
`organized/research/test_universal_schur_obstruction.py:80–89`.
Equation (2) supplies their exact spectral linkage.

Because all gaps are nonnegative,
\[
g=0
\quad\Longrightarrow\quad
\Delta_{(ij)}=0
\quad\text{and}\quad
\Delta_{\sigma}=0
\quad\text{for every 3-cycle }\sigma.
\tag{3}
\]
In particular, the forced quadratic block
\[
t^TAt=4\sum_{i<j}\Delta_{(ij)}
             |(YTY^T)_{ij}|^2
\]
vanishes identically: \(A=0\).

## 2. The forced quintic vector is controlled by the same gaps

There is also an exact identity for \(e\), valid before assuming \(g=0\).

All coordinates of \(e\) vanish except those paired with
\[
(\Im C_{12},\Im C_{13},\Im C_{23}).
\]
Denote these three coordinates by \(\widehat e\). Then
\[
\boxed{
\widehat e=\frac14\sum_{\sigma\text{ a 3-cycle}}
                    \Delta_\sigma s_\sigma,
}
\tag{4}
\]
where the signs are:

| \(\sigma\) | \(s_\sigma\) |
|---|---|
| \((234)\) | \((+1,-1,+1)\) |
| \((243)\) | \((-1,+1,-1)\) |
| \((123)\) | \((-1,-1,+1)\) |
| \((124)\) | \((-1,+1,+1)\) |
| \((132)\) | \((+1,+1,-1)\) |
| \((134)\) | \((+1,+1,+1)\) |
| \((142)\) | \((+1,-1,-1)\) |
| \((143)\) | \((-1,-1,-1)\) |

The convention is \(G_5=2d\,e^Tc\), as in the existing block decomposition.

### Verification of (4)

The linear compound numerators are implemented in
`organized/research/rational_sinkhorn_certificates.py:117–133`.
For each of the 70 compound terms, I extracted its coefficient of \(c_jd\) and verified (4) exactly against its permutation indicators.

This was an identity check in **70 independent formal compound coefficients**, not evaluation at selected spectra. The \(g\)-identity (2) passed the same coefficientwise check.

Combining (2) and (4),
\[
g>0\quad\Longrightarrow\quad
\frac{\widehat e}{2g}
=
\sum_\sigma
\frac{\Delta_\sigma}{8g}s_\sigma
\in[-1,1]^3.
\]
Thus
\[
\boxed{
|e_{\Im C_{ij}}|\le2g,\qquad
\|e\|_2\le2\sqrt3\,g.
}
\tag{5}
\]
More importantly,
\[
\boxed{g=0\Longrightarrow e=0.}
\tag{6}
\]

This rules out the proposed odd-leading-degree failure mechanism under actual identity-support hypotheses. It is not merely that no example was found: the relevant coefficient must vanish identically.

## 3. Exact completion on the boundary

Let the three double-transposition gaps be
\[
d_1=\Delta_{(12)(34)},\qquad
d_2=\Delta_{(13)(24)},\qquad
d_3=\Delta_{(14)(23)}.
\]
Define
\[
\alpha=\frac{d_1+d_2-d_3}{2},\qquad
\beta =\frac{d_1+d_3-d_2}{2},\qquad
\gamma=\frac{d_2+d_3-d_1}{2}.
\tag{7}
\]

Under (3), the translated three-index alternating identities give:

| Permutations | Their common gap |
|---|---:|
| \((1243),(1342)\) | \(\alpha\) |
| \((1234),(1432)\) | \(\beta\) |
| \((1324),(1423)\) | \(\gamma\) |

For example, fixing \(1\mapsto2\) in the alternating identity gives
\[
d_1=\Delta_{(1234)}+\Delta_{(1243)};
\]
the other fixed pairings give the remaining equations and inverse-pair equalities.

These are gaps of the **original permutation products**, so
\[
\alpha,\beta,\gamma\ge0.
\tag{8}
\]
Equivalently, the three double-transposition gaps satisfy the triangle inequalities.

### Six-square identity

The boundary polynomial is exactly
\[
\boxed{
\begin{aligned}
G(T)={}&
\alpha\left[(C_{11}-C_{22})^2
                         +4(\Im C_{12})^2\right]\\
&+\beta\left[(C_{22}-C_{33})^2
                         +4(\Im C_{23})^2\right]\\
&+\gamma\left[(C_{11}-C_{33})^2
                         +4(\Im C_{13})^2\right].
\end{aligned}
}
\tag{9}
\]

Thus \(G\) is purely quartic on this branch. There are no residual cubic or quintic terms.

Here is the explicit \(D_0\). On \((C_{11},C_{22},C_{33})\), it is
\[
\begin{pmatrix}
\alpha+\gamma&-\alpha&-\gamma\\
-\alpha&\alpha+\beta&-\beta\\
-\gamma&-\beta&\beta+\gamma
\end{pmatrix}.
\tag{10}
\]
Its other nonzero entries are
\[
(D_0)_{\Im C_{12},\Im C_{12}}=4\alpha,\quad
(D_0)_{\Im C_{13},\Im C_{13}}=4\gamma,\quad
(D_0)_{\Im C_{23},\Im C_{23}}=4\beta.
\tag{11}
\]
All rows and columns corresponding to real off-diagonal cofactor coordinates vanish.

The matrix (10) is a weighted graph Laplacian, and (11) is nonnegative diagonal. Hence \(D_0\succeq0\).

### Exact algebraic verification of (9)

I checked the full identity using the compound numerators, including the polynomial relations among \(t,c,d\):

1. Assign 70 independent real coefficients \(w_{IJ}\) to the compound terms.
2. Form their 24 permutation values through
   \[
   Z_{(I,J),\pi}=\mathbf1_{\pi(I)=J}.
   \]
3. Let \(R\) contain the 14 gap constraints for the six transpositions and eight 3-cycles.
4. Expand the difference between the canonical polynomial and the right-hand side of (9).

The exact output was:

- contact-constraint rank: **10**;
- coefficient-nullspace dimension: **60**;
- **all 838 polynomial coefficient rows** of the difference annihilate that nullspace;
- the three four-cycle identifications in the table also hold exactly on it.

Therefore (9) is a universal algebraic identity conditional on those contact equalities. This finite symbolic calculation proves an identity for unrestricted parameters; it is **not** another finite spectral test.

The arbitrary formal coefficients are used only to verify the identity. Positivity in the application comes from the actual spectral gaps (8), not from an arbitrary-cost example.

## 4. Recovery of the requested 25-parameter completion

For \(g=0\), the construction is
\[
\boxed{
u=0,\qquad K=-B_0,\qquad
X=
\begin{pmatrix}
0&0&0\\
0&D_0&0\\
0&0&0
\end{pmatrix}\succeq0.
}
\tag{12}
\]

This is admissible:

- \(A=0\) by (2) and the forced quadratic formula.
- \(e=0\) by (4).
- Equation (9) gives \(G_3=0\). Consequently \(t^TB_0c=0\), so \(-B_0\) belongs to the allowed 16-dimensional cubic Gram kernel.
- \(u=0\) leaves \(D_0-2L(u)=D_0\).
- Equations (10)–(11) prove \(D_0\succeq0\).

The Laplacian has rank at most two, and the imaginary-coordinate block has rank at most three. Thus
\[
\operatorname{rank}X\le5.
\]

This is an explicit completion, not just a necessary inequality.

It also retains the original comparison height: for every finite Hermitian \(T\),
\[
\det(I+T^2)>0,\qquad
h-\Re(\eta F(W(T)))=\frac{G(T)}{\det(I+T^2)}\ge0.
\]
Continuity extends the support inequality across the Cayley-chart boundary. The existing global balanced-plane reduction then supplies the corresponding full-unitary statement for these spectral/support data.

