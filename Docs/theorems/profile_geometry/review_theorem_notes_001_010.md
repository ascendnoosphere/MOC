## Round 006 — The conormal argument for the cubic is a valid general theorem

**Result: proved algebraic lemma; its spectral application has a coordinate-identification requirement.**

Let C be a cubic on a real or complex vector space V, H its Hessian, and X a reduced algebraic subvariety. Suppose H has constant maximal rank r on a neighborhood of c within X, with rank H(c)=r. Put N=ker H(c). Then

\[
n^T H(v)n'=0
\quad(n,n'\in N,\ v\in T_cX).
\]

To prove this, use a nonzero r-minor to choose rational local sections n(x) of the Hessian kernel. Differentiate H(x)n(x)=0 along v in the Zariski tangent space, and left-multiply by n' in N. The derivative of n(x) disappears because n'^T H(c)=0. Cubic symmetry identifies the remaining term as n'^T H(v)n. Rational sections are legitimate even at a singular point of X: their defining identities hold in the localized coordinate ring and can be differentiated along Zariski tangent vectors.

Consequently the restricted-gradient map

\[
L:\operatorname{Sym}(N)\longrightarrow V^*,\qquad
L(T)_j=\tfrac12\operatorname{tr}(N^T H(e_j)NT),
\]

has image in the conormal space (T_cX)^perp. In particular

\[
\operatorname{rank}L\le\operatorname{codim}T_cX
\le\operatorname{codim}X.
\]

This supplies the exact missing mechanism behind the algebra researcher's observed rank-two image. If the fourteen-coordinate cubic is identified with the cubic studied by Howard–Millson–Snowden–Vakil, and its relevant secant cone X has affine dimension 12 while its gradient image has dimension 10, the generic tangent-rank estimate forces Hessian rank at most 12 on X; closure extends that bound. At a rank-12 point, the lemma gives rank L at most 2.

The differential argument is sound. The substantive verification still required for its application is the exact coordinate identification of the 49-term polynomial with that source's cubic and the precise secant variety being used. An isomorphism suggested by matching dimensions is insufficient on its own. This audit does not silently promote that identification to an established fact.


## Round 009 — The zero-block obstruction extends to a global linear penalty with some finite constant

**Result: proved existence theorem, exact connection to the signed-law obstruction; the optimal constant is open here.**

For R in SO(6) split into two-by-two blocks, write m_ij=||R_ij||_F^2 and h_ij=det R_ij. Define

\[
F=\sum_i(m_{ii}+6h_{ii}),\qquad
D=m_{12}+m_{23}+m_{31}.
\]

The analyst's classification of D=0 is correct. Write the six allowed blocks as [[A,0,B],[C,E,0],[0,G,H]]. Column orthogonality gives A*B=0, while AA*+BB*=I. Thus AA* and BB* are orthogonal complementary projections, and every nonzero block is a partial isometry. The rank equations force a common diagonal rank r in {0,1,2}. For r=0, F=0. For r=1, F=3. For r=2, orientation forces the three diagonal determinant signs to have product +1, so F is either 0 or 24. Therefore F>=0 on D=0.

There is in fact a constant C<infinity such that

\[
\boxed{F+C D\ge0\quad\hbox{for every }R\in SO(6).}
\]

**Proof.** The zero set of both D and F consists of two kinds of smooth compact block submanifolds: reverse cyclic block permutations, and block diagonal matrices with exactly two negative block determinant signs. At either kind, the first derivative of F on SO(6) is zero. For block diagonal matrices, diagonal block norms and determinants have zero first derivative under infinitesimal orthogonal motion; off-diagonal variations do not contribute at first order. At reverse cyclic block permutations, every diagonal block is zero, so both its squared norm and determinant vanish to second order.

In local coordinates R=exp(K)R_0, the differential of the three forbidden blocks observes each of the three independent off-diagonal two-by-two skew blocks of K exactly once, multiplied by an orthogonal block. Thus its kernel is precisely the tangent space of the relevant block submanifold. On normal directions D is a uniformly positive definite quadratic form. Compactness gives D>=c times the squared distance locally, while the vanishing first derivative gives |F|<=c' times the same squared distance. A finite penalty therefore works near these zero strata.

At the remaining points of D=0, F is strictly positive, so positivity persists on a neighborhood. The complement of these neighborhoods is compact and has D bounded below by a positive constant; increasing C handles it. QED.

For a useful algebraic interpretation, let E=m_13+m_21+m_32 and t=tr p. The tetrahedral identity gives tr h=t-1, and the row/column sums give tr m=6-D-E. The Holden obstruction parameter in this convention is

\[
c=(m_{12}-m_{21})/2=(D-E)/6.
\]

Consequently

\[
F+C D=6(t+c)+(C-2)D.
\]

Thus the penalty controls the negative signed mass h_+=max(0,-(t+c)/4) by 24h_+ <= (C-2)D. The value C=2 is already false because t+c can be negative at an actual unitary; this is the known common-law obstruction. The root investigator's targeted searches suggest a small explicit constant may work, but no numerical candidate is promoted here to a universal theorem. An explicit best constant and a usable sum-of-squares proof remain worthwhile targets.

