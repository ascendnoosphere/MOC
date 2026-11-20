## Notation

For

\[
U(q)=
\begin{pmatrix}
c&u&v&w\\-u&c&w&-v\\-v&-w&c&u\\-w&v&-u&c
\end{pmatrix},
\qquad q=(c,u,v,w),\quad \|q\|=1,
\]

let δπ=h−Re(ηzπ)≥0 be the permutation support gaps. Write

\[
d=(\delta_{\rm id},\delta_{(12)(34)},
\delta_{(13)(24)},\delta_{(14)(23)}),
\]

\[
\begin{array}{lll}
e_{01}=\delta_{12}+\delta_{34},&
e_{02}=\delta_{13}+\delta_{24},&
e_{03}=\delta_{14}+\delta_{23},\\
e_{12}=\delta_{1243}+\delta_{1342},&
e_{13}=\delta_{1234}+\delta_{1432},&
e_{23}=\delta_{1324}+\delta_{1423}.
\end{array}
\]

The strings in this display denote cycles, not one-line permutations. Put

\[
\alpha_1=(a_1-a_2)(a_3-a_4),\quad
\alpha_2=(a_1-a_3)(a_2-a_4),
\]

and define β₁,β₂ similarly. The exact interference is

\[
T=-2(\alpha_1\beta_2-\alpha_2\beta_1),\qquad
\chi=\operatorname{Re}(\eta T).
\]

The support deficit is the homogeneous quartic

\[
F(q)=\sum_i d_iq_i^4+
\sum_{i<j}e_{ij}q_i^2q_j^2-\chi q_0q_1q_2q_3.
\]

Thus its positivity is equivalent to

\[
|\chi|\le\operatorname{cap}(d,e)
=\inf_{\substack{x_i>0\\\prod x_i=1}}
\left(\sum_i d_ix_i^2+\sum_{i<j}e_{ij}x_ix_j\right).
\]

The stronger proposed bound is

\[
B=4(d_0d_1d_2d_3)^{1/4}
+2\left(\sqrt{e_{01}e_{23}}+
\sqrt{e_{02}e_{13}}+\sqrt{e_{03}e_{12}}\right).
\]

Always B≤cap. The remaining conjectural implication is that actual spectra and all twenty-four gap inequalities imply |χ|≤B, or at least |χ|≤cap.


## Round 043 — Reduce the even coefficients from ten to seven parameters

### Exact identities

Set

\[
p=\alpha_1\beta_1,\quad
q=\alpha_2\beta_2,\quad
r=(\alpha_2-\alpha_1)(\beta_2-\beta_1).
\]

Direct factoring of matching products gives

\[
p=z_{\rm id}+z_{(12)(34)}-z_{12}-z_{34},
\]

\[
p=z_{(13)(24)}+z_{(14)(23)}-z_{1324}-z_{1423}.
\]

The analogous identities hold for q and r. Thus, with P=Re(ηp), Q=Re(ηq), S=Re(ηr),

\[
\begin{array}{ll}
e_{01}=P+d_0+d_1,&e_{23}=P+d_2+d_3,\\
e_{02}=Q+d_0+d_2,&e_{13}=Q+d_1+d_3,\\
e_{03}=S+d_0+d_3,&e_{12}=S+d_1+d_2.
\end{array}
\tag{43.1}
\]

These signs agree with the independent derivation by the root.

### Consequence

The even quartic can be written as

\[
\begin{aligned}
F_{\rm even}(q)
={}&\left(\sum_i d_iq_i^2\right)\left(\sum_iq_i^2\right)\\
&+P(q_0^2q_1^2+q_2^2q_3^2)
+Q(q_0^2q_2^2+q_1^2q_3^2)\\
&+S(q_0^2q_3^2+q_1^2q_2^2).
\end{aligned}
\]

### Status

This is an exact smaller coefficient space, retaining the diagonal vertex geometry. P,Q,S can be negative; replacing their signed terms by independently nonnegative ones would discard valid cases.


## Round 045 — One zero diagonal reduces capacity to a three-variable cubic

### Proposed mechanism

Exploit a facet containing a vertex from the quaternion diagonal class.

Assume d₀=0. Put

\[
x_0=t,\qquad x_i=y_i t^{-1/3}\ (i=1,2,3),
\qquad y_1y_2y_3=1.
\]

Define

\[
A(y)=\sum_{i=1}^3 d_i y_i^2+
\sum_{1\le i<j\le3}e_{ij}y_i y_j,
\qquad
L(y)=\sum_{i=1}^3 e_{0i}y_i.
\]

The objective becomes

\[
A(y)t^{-2/3}+L(y)t^{2/3}.
\]

Minimizing over t gives

\[
\boxed{\operatorname{cap}(d,e)
=2\inf_{\prod y_i=1}\sqrt{A(y)L(y)}.}
\tag{45.1}
\]

### Result

The remaining optimization is a homogeneous cubic capacity in three positive variables. The formula remains valid when coefficients vanish, by taking limits.

This is a connection to rank-three mathematics, not a proof of a Jordan determinant representation.

## Round 046 — Two zero diagonal gaps reduce capacity to one positive variable

### Proposed mechanism

A facet tying two quaternion diagonal vertices satisfies d₀=d₁=0 after the permissible quaternion coordinate exchange.

Write

\[
x_0=\sqrt{ts},\quad x_1=\sqrt{t/s},\quad
x_2=\sqrt{r/t},\quad x_3=1/\sqrt{rt}.
\]

The product constraint is automatic. Minimizing first in s and then in t yields

\[
\boxed{
\begin{aligned}
\operatorname{cap}(d,e)=\inf_{r>0}\bigg[
&2\sqrt{e_{01}(e_{23}+d_2r+d_3/r)}\\
&+2\sqrt{
e_{02}e_{12}r+e_{03}e_{13}/r+
e_{02}e_{13}+e_{03}e_{12}}
\bigg].
\end{aligned}}
\tag{46.1}
\]

### Proof of the eliminations

The s-dependent terms are
C(r)√s+D(r)/√s, whose infimum is 2√(C(r)D(r)).
The t-dependent terms are
e₀₁t+(e₂₃+d₂r+d₃/r)/t, giving the other square root.

### Status

This is an exact scalar reduction on this contact type, including zero coefficients through limits. A proof that the actual spectral χ is bounded by (46.1) remains open.

## Round 047 — The capacity has fourteen basic balancing patterns

### Proposed mechanism

Classify the monomial support before searching for a certificate.

Associate a loop at i to d_i x_i² and an edge ij to e_ij x_i x_j. A positive capacity exists exactly when the center exponent (1/2,1/2,1/2,1/2) belongs to the convex hull of supported exponents.

### Proof

A balanced convex combination gives a strictly positive weighted AM–GM bound. If no combination exists, a separating vector in the hyperplane Σy_i=0 makes every supported monomial tend to zero along x_i=exp(−ty_i). Thus the capacity vanishes.

The extreme fractional matching patterns on four vertices are:

- four loops;
- one edge and two remaining loops;
- two disjoint edges;
- a triangle and the remaining loop.

There are respectively 1,6,3,4 patterns, for fourteen in total. Even cycles admit an alternating perturbation and do not add extreme patterns.

Besides the bounds used in B, this gives

\[
\operatorname{cap}\ge
2\sqrt2\,\sqrt{e_{ij}}\,(d_kd_l)^{1/4},
\]

and

\[
\operatorname{cap}\ge
4(d_l e_{ij}e_{ik}e_{jk})^{1/4}.
\]

### Result

A failure of B would not necessarily refute the true capacity inequality. The omitted edge-plus-loops and triangle-plus-loop certificates can remain positive when B vanishes.

## Round 048 — Eliminate the triangle part of the B=0 boundary

### Proposed mechanism

Classify the hardest apparent degeneracies of the stronger bound.

If B=0, the supported edge graph has no pair of disjoint edges. A graph on four vertices with this property is contained in a star or a triangle.

Consider the triangle on vertices 1,2,3, so e₀₁=e₀₂=e₀₃=0. Nonnegative gaps imply that all six transposition gaps vanish.

For any triple of indices, the rank-two three-minor identity gives

\[
\delta_{\text{cycle}}+\delta_{\text{reverse cycle}}
=\sum_{\text{three transpositions on the triple}}
\delta_{\text{transposition}}-d_0.
\]

The left side is nonnegative, so d₀=0, and both three-cycle gaps vanish. Applying this to all four triples makes all eight three-cycle gaps zero. Since χ is a signed sum of their projections,

\[
\boxed{\chi=0.}
\]

Quaternion basis permutations give the other triangle placements.

### Result

The stronger bound is proved on every triangle-supported B=0 boundary. The unresolved zero-bound pattern is the star direction associated with the common-law obstruction.


## Round 050 — Prove an exact nonzero-chirality SOS when a=(s,s,t,t)

### Proposed restricted theorem

Let the first spectrum have two values, each repeated twice, while the second spectrum is arbitrary complex.

For a two-element set J of column indices define

\[
Z_J=\prod_{j\in J}(s+b_j)\prod_{j\notin J}(t+b_j),
\quad \Delta_J=h-\operatorname{Re}(\eta Z_J)\ge0.
\]

Put

\[
D_0=\Delta_{12},\quad D_2=\Delta_{34},\quad
K_+=\Delta_{13}+\Delta_{24},\quad
K_-=\Delta_{14}+\Delta_{23}.
\]

### Derivation

The relevant 2×2 minors of the first two rows of U(q) are

\[
c^2+u^2,\quad -(v^2+w^2),\quad
cw+uv\ \text{twice},\quad uw-cv\ \text{twice}.
\]

Cauchy–Binet gives the exact support identity

\[
\boxed{
F(q)=
D_0(c^2+u^2)^2+
D_2(v^2+w^2)^2+
K_+(cw+uv)^2+
K_-(uw-cv)^2.}
\tag{50.1}
\]

### Result

The full isoclinic support inequality is proved on this spectral class by a positive sum of four squares. Chirality need not vanish. Thus this extends beyond the matched-cross-ratio theorem.

## Round 051 — Prove the stronger bound B for that repeated-spectrum class

### Derivation from Round 050

Comparison of coefficients gives

\[
d=(D_0,D_0,D_2,D_2),
\]

\[
e_{01}=2D_0,\quad e_{23}=2D_2,\quad
e_{03}=e_{12}=K_+,\quad e_{02}=e_{13}=K_-,
\]

and

\[
\chi=2(K_--K_+).
\]

Therefore

\[
B=8\sqrt{D_0D_2}+2(K_++K_-)
\ge2|K_--K_+|=|\chi|.
\]

### Equality conditions

Equality requires D₀D₂=0 and at least one of K₊,K₋ to vanish. Since each K is a sum of two nonnegative gaps, this creates additional simultaneous support contacts.

### Result

The stronger proposed spectral inequality is proved for a=(s,s,t,t), with arbitrary complex b and every support functional. Corresponding paired labels follow by tracking the quaternion basis transformation.

## Round 052 — The projection law proves the associated all-dimensional restricted MOC theorem

### Proposed extension

The preceding SOS is the quaternion realization of a more general positive law.

Let A=tI+(s−t)P, where P=QQ* is an orthogonal projection of rank k and Q*Q=I_k. Put B=diag(b).

For generic diagonal D=B+tI, the determinant lemma and Cauchy–Binet give

\[
\begin{aligned}
\det(D+(s-t)P)
&=\det D\,
\det\left(Q^*(I+(s-t)D^{-1})Q\right)\\
&=\sum_{|J|=k}|\det Q[J]|^2
\prod_{j\in J}(s+b_j)
\prod_{j\notin J}(t+b_j).
\end{aligned}
\]

The identity extends through singular D polynomially. The weights are nonnegative and sum to det(Q*Q)=1.

### Result

Whenever one normal matrix has at most two distinct eigenvalues, this supplies an all-dimensional MOC law. This is an explicit derivation, not a claim of a historically new theorem.

It also shows why the repeated-spectrum isoclinic SOS has enough positive coefficients even when its chiral term is nonzero.


## Round 054 — Isolate the new rank-four Jordan polarization invariant

### Proposed mechanism

Determine exactly which term first escapes the frame-overlap proof.

Let x,y belong to the complexification of a rank-four Euclidean Jordan algebra. Write a=tr x, b=tr y, S=tr(x∘y), and σ₂(x)=((tr x)²−tr x²)/2.

The mixed degree-(2,2) part of det(x+y), obtained from the fourth Newton identity, is

\[
\begin{aligned}
E_{22}={}&
\sigma_2(x)\sigma_2(y)-abS
+a\,\operatorname{tr}(x\circ y^2)
+b\,\operatorname{tr}(x^2\circ y)\\
&+\tfrac12 S^2
-\tfrac12\operatorname{tr}(x^2\circ y^2)
-\operatorname{tr}\bigl((x\circ y)^2\bigr).
\end{aligned}
\tag{54.1}
\]

For the quartic trace term, the key expansion is

\[
[\operatorname{tr}(x+y)^4]_{22}
=2\operatorname{tr}(x^2\circ y^2)
+4\operatorname{tr}((x\circ y)^2),
\]

using (x+y)²=x²+y²+2x∘y and trace associativity.

### Result

Frame overlaps determine the terms linear in either frame’s spectral coordinates. The new squared-product trace in (54.1) carries the middle-degree coupling. On complex elements it is a complex square, not a nonnegative real norm.

The rank-three positive law does not control this invariant automatically. Formula (54.1) identifies the precise additional polarization term a rank-four Jordan certificate must address.


## Round 056 — Exact sharpness on an actual coefficient-hull supporting face

### Exact sharpness model

The following actual spectral data give an exact sharp case:

\[
\beta=(-5-2i,-5-4i,-5-4i,-5-5i),
\]

\[
t=5+4i,\qquad \lambda_0=1-9i,\qquad
\lambda_1=41-41i,\qquad h=0.
\]

The corresponding support gaps are nonnegative integers. In lexicographic one-line permutation order they are

\[
(80,0,80,0,0,0,82,0,0,0,0,82,
82,0,0,0,0,82,0,0,0,80,0,80).
\]

Thus

\[
d=(80,0,0,80),\qquad
e=(82,0,160,0,0,82),\qquad \chi=-164.
\]

Consequently B=164=|χ|.

### Exact quartic certificate

Here

\[
\boxed{F(q)=80(c^2+w^2)^2+82(cu+vw)^2.}
\tag{56.1}
\]

### Result

This is an actual spectral support with nonzero chirality and exact saturation of the proposed stronger bound. Finite spectra follow from the established coefficient-hull recovery.

