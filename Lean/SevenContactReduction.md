# A uniform seven-contact reduction in order four

Status: new mathematical proof of the reduction below, with exact
finite and polynomial checks. This replaces the *six-contact curve
transfer* part of the supplementary reconstruction, not all remaining
contact inequalities. Fifteen of the 100 exceptional seven-contact
orbits are certified; 85 remain. The unrestricted order-four theorem
is not claimed independently certified. No Lean axiom or unchecked
Lean declaration has been added.

The starting point is Zheng's six-contact reduction, independently
generalized to all orders in OrderFiveContactReduction.md. We use the
existing order-four real orthogonal minor mixture theorem and the
audited 82-facet classification. The proof below does not need any
of the missing exceptional-contact supplementary proofs.

## 1. Strict positive probability laws at coincidence spectra

Call a unitary matrix generic here when all its entries and all its
two-by-two minors are nonzero. Such matrices form a dense open subset
of U(4): each of the finitely many minor functions is nonzero at a
suitable permutation matrix, hence its real-analytic zero set has
empty interior. Strict violation of a support inequality is open.
Thus, in proving an existence reduction for a hypothetical failure,
we may perturb the fixed unitary so it is generic.

For a fixed unitary of this type, the following two order-four
common-law constructions can be made strictly positive on *every*
one of the 24 permutations. The laws need not be the same for the
two different coincidence conditions.

### 1.1 Repeated entry within one spectrum

Use the rank-two flow proof of Zheng's Lemma B.2, which is also an
elementary consequence of the two exceptional columns. Let \(p,q\)
be those two orthonormal columns, let \(a_i=|p_i|^2\) and
\(w_{ij}=|p_iq_j-p_jq_i|^2\) for unordered pairs. The total edge
mass is one, the total desired first-endpoint mass is one, and
for every nonempty proper subset \(S\) of the four labels,
\[
\sum_{i<j,\ i,j\in S} w_{ij}
=\|p_S\|^2\|q_S\|^2-|\langle p_S,q_S\rangle|^2
<\sum_{i\in S}a_i.
\]
The inequality is strict because \(p_S\ne0\) and \(\|q_S\|^2<1\).
All \(a_i,w_{ij}>0\). Allocate a small positive amount \(\epsilon\)
of every edge's mass to each endpoint first. The remaining demands
are \(a_i-3\epsilon\) and edge masses \(w_{ij}-2\epsilon\).
Their totals agree, their entries remain positive, and all the
proper-subset flow inequalities remain valid by their strict slack.
The max-flow/min-cut theorem gives an allocation of the remaining
mass. Thus every ordered pair of distinct exceptional positions
has positive probability. Split that probability positively between
the two permutations of the repeated entries. The principal-minor
expansion in Lemma B.2 now gives a single full-support law for all
spectra in this coincidence family. Transposition gives the other
spectrum.

### 1.2 One opposite eigenvalue pair

Use the doubly stochastic matrix in Zheng's Theorem B.1, or the
equivalent anchored-twist construction in MOC/FourCoincidence.lean.
With the coincident labels numbered 0, its entry at (0,0) is zero,
and every other entry is positive: they are normalized singleton
or two-minor squared moduli of the generic unitary. A doubly
stochastic matrix positive on all allowed entries of a face admits
a Birkhoff decomposition assigning positive mass to every permutation
of that face. Indeed, subtract a sufficiently small positive
multiple of the sum of all those permutation matrices and apply
Birkhoff to the normalized residual matrix.

The anchored-twist involution bijects the permutations that do
not fix 0. The mass \(s=1-|U_{00}|^2>0\) can therefore be distributed
positively to every such permutation. The remaining mass
\(|U_{00}|^2>0\) can be split positively among all six permutations
fixing 0. All their products are zero in the coincidence family,
so this splitting does not change the determinant identity.

Consequently, whenever at least two of the eight spectral points
coincide, a nonconstant projected matching gap profile with all
gaps nonnegative has strictly positive evaluation at the fixed
generic unitary. In fact every permutation has positive probability,
and at least one gap is positive.

The same strict positivity holds for every entry-type gap profile
\(p_\sigma=c+\sum_i Q_{i,\sigma(i)}\). All entries of
\((|U_{ij}|^2)\) are positive, so the Birkhoff argument above
gives a law with all 24 weights positive.

## 2. The finite exceptional complex-equality analysis

Use the notation of Zheng's Appendix E and the minimum-support
convention. Let \(X_4\) be the exact complex matching-profile cone
of dimension six. A strict violation at a six-contact profile
must have its contact set contained in the zero set of at least
one of the 48 nonminor facets (otherwise the gap has a minor
decomposition).

The exact checker research/zheng_seven_contact_certificate.py
enumerates the orbits under independent row and column permutations
and inversion. It verifies that of the 90 exceptional six-contact
orbits, 87 contain two permutations differing by a transposition.
The other three are precisely T88, T89, T90, with index sets
\[
\begin{split}
T_{88}&=\{1,5,6,10,13,14\},\\
T_{89}&=\{2,5,9,10,13,14\},\\
T_{90}&=\{1,5,6,9,14,18\}.
\end{split}
\]
All 48 nonminor zero sets lie in a single symmetry orbit, also
checked exactly.

We need a statement about **complex equality** of the six contact
products, not merely equality of their real parts. Suppose all
six products are equal as complex numbers in a nonconstant
matching profile. For the 87 swap-containing cases, if all eight
spectral points were distinct, the difference between the two
transposition-adjacent matching products would be a product of
four nonzero brackets, impossible. Hence there is a coincidence,
and Section 1 applies.

For the three other cases, first dispose of any coincidence by
Section 1. In the regular case use the normalized rank-two kernel
\[
K_{ij}=1+x_i y_j,\quad x=(0,1,a,b),\quad y=(0,c,d,e).
\]
All its entries are nonzero, the four x coordinates are distinct,
and the four y coordinates are distinct. The common scalar
multiplying all normalized products is immaterial for the
complex equalities. Write \(p_k\) for the normalized products.

### T89

The equalities \(p_9=p_{13}\), \(p_5=p_{10}\) and \(p_2=p_{14}\)
give, after cancellation of nonzero factors,
\[
d=bc,\qquad
(1+ad)(1+d)=1+bd,\qquad
(1+d)(1+ac)=1+c.
\]
Since \(c,d\ne0\), the second gives \(b=1+a+ad\), the third
\(b=d/c=1-a-ad\). Hence \(b=1\), contrary to distinctness.

### T90

The equalities \(p_6=p_{14}\), \(p_1=p_{14}\), \(p_9=p_{14}\),
\(p_{18}=p_{14}\) give
\[
c=ad,\quad
(1+ae)(1+bd)=1+be,\quad
1+d=(1+c)(1+bd),\quad
1+ac=(1+c)(1+ae).
\]
Consequently \(b=(1-a)/(1+ad)\) and \(e=d(a-1)/(1+ad)\).
Substitution gives
\[
p_5-p_1=-2d(a-1)^2.
\]
The equality of these contacts is impossible since \(d\ne0\) and
\(a\ne1\). The polynomial substitution is checked exactly.

### T88

From the six complex equalities, cancel nonzero factors to obtain
\[
c=ad,\quad (1+ae)(1+bd)=1+be,\quad
1+e=(1+c)(1+ae),\quad
(1+e)(1+bc)=1+be,\quad
1+ae=(1+c)(1+e).
\]
The last and the third force \((1+c)^2=1\). Since \(c\ne0\),
\(c=-2\). Substitution into the remaining equalities yields
\[
d=-2/a,\quad e=-2/(a+1),\quad b=a/(a+1),
\quad a^2-a+1=0.
\]
For example the last equation follows by substituting in
\((1+e)(1+bc)=1+be\), whose left minus right becomes
\(-2(a^2-a+1)/(a+1)^2\).

Thus there are only two regular normalized profiles, conjugate to
each other. The checker reduces every matching product modulo
\(a^2-a+1\) exactly. The common contact value is \(-1/3\), and
\[
\frac32(p-p_1\mathbf1)=(1-a)A+aB,
\]
where the two real profiles have the exact facet decompositions
\[
A=f_1+f_{10}+f_{34}+f_{59},\qquad
B=f_1+f_{10}+f_{30}+f_{59}.
\]
The coefficient of \(1-a\) in the profile at index 3 is one,
and the coefficient of \(a\) at index 4 is one (the other
coefficient at each of these indices is zero). Consequently for
any common complex scalar multiplying the profile, nonnegative
real gaps require the projected two coefficients to be
nonnegative. If the projected gap is nonzero, at least one is
positive.

After reversing columns, these two profiles become
\(h_{\mathrm{id},\pm}\) plus the three anchored principal
two-minor indicators. We prove their evaluations nonnegative,
and strictly positive for generic unitaries, in Section 3.

## 3. A quaternion inequality for the exceptional profile

Let \(O=L(q)R(r)\) be a real special orthogonal four-matrix in its
unit-quaternion left-right representation. This representation
is already formalized in MOC/FourQuaternionRotation.lean.
Write \(x_i=q_i^2,\ y_i=r_i^2\), so \(x,y\) are probability
vectors of length four. Put
\[
S=\sum_{i=1}^3\det O[\{0,i\},\{0,i\}]^2.
\]
Direct polynomial expansion, verified by the new exact checker,
gives
\[
S=\sum_{i=0}^3(x_i+y_i-1/2)^2,\qquad
\frac12\sum_i O_{ii}^2=2\sum_i x_i y_i,
\]
and for the author's mixed split contrast \(d_{\mathrm{id}}\),
\[
\frac12\Phi_{d_{\mathrm{id}}}(O)
=4(r_0r_1r_2r_3-q_0q_1q_2q_3).
\]
For the first identity, the three principal minors before
squaring equal \(x_0+x_i+y_0+y_i-1\); the three squares sum
to the displayed expression since the four \(x_i+y_i-1/2\)
sum to zero.

We claim the following purely real inequality:
\[
\boxed{
E(x,y):=\sum_i(x_i+y_i-1/2)^2+2\sum_i x_i y_i
-4\left(\sqrt{\prod_i x_i}+\sqrt{\prod_i y_i}\right)\ge0.
}\tag{1}
\]
Moreover equality requires \(x_i+y_i=1/2\) for every i.

Proof: minimize the continuous function on the product of the two
compact probability simplices. If one vector has exactly one zero,
this cannot be a minimum: move a small positive amount \(t\)
from a positive coordinate to its zero coordinate. Its product
square root increases by a positive constant times \(\sqrt t\)
to leading order, whereas all polynomial terms change by \(O(t)\).
The other vector and its product are fixed.

If one vector has support one, say \(x=(1,0,0,0)\), the first
square alone is at least \(1/4\), whereas
\(4\sqrt{\prod y_i}\le1/4\) by AM--GM. Equality in both bounds
would require simultaneously \(y_0=0\) and \(y_i=1/4\) for all
i, impossible.

If one vector has support two, write
\(x=(a,1-a,0,0)\), \(y=(c,d,e,f)\), and put \(s=c+d\).
Completing the square gives the exact identity
\[
S+2x\cdot y
=2(a-(1/2-c+d))^2+1/2+6cd-2ef.
\]
Use \(ef\le(1-s)^2/4\) and \(\sqrt{cd}\le s/2\):
\[
\begin{split}
E(x,y)&\ge1/2+6cd-2ef-4\sqrt{cdef}\\
&\ge s-s^2/2+6cd-2(1-s)\sqrt{cd}\\
&\ge s^2/2+6cd\ge0.
\end{split}
\]
If equality holds then \(s=0\), the other two coordinates
must satisfy \(e=f=1/2\), and the completed square requires
\(a=1/2\). Thus \(S=0\). The cases with x and y interchanged
are identical.

It remains to check interior minima. Write \(P=\sqrt{\prod x_i}\),
\(Q=\sqrt{\prod y_i}\), both positive. The Lagrange multiplier
equations, subtracting those for distinct indices i,j, give
\[
\left(1+\frac{P}{x_i x_j}\right)(x_i-x_j)+2(y_i-y_j)=0,\qquad
\left(1+\frac{Q}{y_i y_j}\right)(y_i-y_j)+2(x_i-x_j)=0.
\]
Thus x and y have identical equality groups and opposite strict
orderings. If \(x_i\ne x_j\), then
\[
\left(1+\frac{P}{x_i x_j}\right)
\left(1+\frac{Q}{y_i y_j}\right)=4.
\]
If the complementary pair k,l also has distinct values, the same
equation holds with both ratios inverted. Combining the two
equations gives that both ratios equal one, by their positivity.
In particular \(x_i x_j=x_k x_l\).

If x has at least three distinct values, order its coordinates
decreasingly. There is a complementary partition into pairs,
both having distinct values, whose products are unequal:
for four distinct values choose the two largest versus the
two smallest; for a repeated top or bottom value pair the
two equal entries with the other two distinct values;
for a repeated middle value pair the largest with one middle
value and the smallest with the other. This contradicts
the previous equation. Hence there are at most two distinct
values. Uniform vectors give equality with \(S=0\).

If the multiplicities are 2+2, write
\(x=(a,a,b,b), y=(c,c,d,d)\), \(a+b=c+d=1/2\).
Substitution gives \(E=2(2a+2c-1)^2\), with equality only
if \(S=0\).

For multiplicities 1+3, interchange x and y if needed to make
the exceptional x coordinate larger. Write
\[
x=(u^2,1,1,1)/(u^2+3),\quad
y=(v^2,1,1,1)/(v^2+3),\quad u>1,\ v<1 .
\]
The stationarity equation gives \((1+1/u)(1+1/v)=4\), hence
\(v=(u+1)/(3u-1)\). Direct rational substitution, checked exactly,
gives
\[
E=\frac{(u-1)^4(31u^4+104u^3+194u^2-104u+15)}
        {2(u^2+3)^2(7u^2-4u+1)^2}>0.
\]
The numerator's last factor is positive for \(u>1\), as
\(194u^2-104u>0\). This completes the minimum and equality
analysis, proving (1). QED.

It follows that
\[
\Phi_{h_{\mathrm{id},\pm}}(O)+S\ge E(x,y)\ge0,
\]
and equality can occur only at \(S=0\). Row sign changes leave
the squared-minor functional unchanged, so the inequality holds
for all real orthogonal matrices. The existing theorem
MOC/FourMinorTransport.lean, four_minor_mixture, expresses every
complex order-four unitary minor table as a convex mixture of
real orthogonal minor tables. The same inequality therefore
holds for all complex unitaries. If the left side is zero,
all positively weighted real components have \(S=0\), so the
complex unitary also has \(S=0\). A generic unitary has \(S>0\).
This proves the strict positivity of both T88 profiles in
Section 2 whenever the nonnegative projected gap is nonzero.

## 4. Seven-contact reduction: the proof

**Theorem.** If MOC fails in order four, then it fails at a pair
of spectra having at least seven permutation labels on one
supporting line. The relative unitary of this counterexample
can be chosen generic.

This is a strict strengthening of the six-contact reduction.
It does not assert that the determinant bound holds at all
seven-contact data.

Proof: perturb the initial violating relative unitary to a
generic one, preserving the strict violation. Fix that unitary
throughout the proof. Its real signed weights \(w_\sigma\)
give the determinant as a linear functional of the complex
matching profile, and the weights sum to one.

Apply the six-contact theorem from OrderFiveContactReduction.md,
or Zheng's Theorem 3.6 (the former already works for complex
unitaries). If seven contacts have already occurred, stop.
Otherwise there are exactly six, called T, and choose a contact
\(\pi\in T\). Use the minimum-support convention and put
\[
g_\sigma=\Re(p_\sigma-p_\pi)\ge0,\qquad
L=\sum_\sigma w_\sigma g_\sigma<0.
\]
If T belongs to a minor-only contact cone, the gap is nonnegative
at the fixed unitary, contrary to strict violation. Thus T
belongs to one of the 90 exceptional orbits above.

Fix the five *complex* values \(p_\tau-p_\pi\), \(\tau\in
T\setminus\{\pi\}\), on the six-dimensional irreducible affine
matching cone \(X_4\). Unlike the six-contact proof, do NOT fix
the sum of all differences. Every irreducible component of this
affine section through the current point has dimension at
least one. If every complex difference were constant on such
a component, it would be a full line in the translation
direction, and the elementary translation-line lemma of
OrderFiveContactReduction.md would make the gap entry-type,
contradicting the violation. Choose an irreducible affine curve
through the current point on which some difference is nonconstant
by generic linear sections, as in that note.

Normalize and complete the curve to a connected compact
Riemann surface \(\Sigma\); the matching coordinates become
meromorphic. Let D be its finite set of points at infinity and
poles. All old contacts remain contacts. Let
\(H_\sigma=p_\sigma-p_\pi\) and \(\mathcal L=\sum w_\sigma
H_\sigma\), so \(L=\Re\mathcal L\).
Assume for contradiction that the curve has no new contact
with all gaps nonnegative and \(L<0\). Let \(\Omega\) be the
connected component containing the starting point of
\(\{g_\sigma>0\text{ for }\sigma\notin T,\ L<0\}\) in
\(\Sigma\setminus D\). Every boundary point there has \(L=0\):
otherwise all gaps are nonnegative and either all new gaps are
positive (an interior point), or some new gap vanishes (a new
strictly violating contact).

In particular \(\Omega\) is a whole connected component of
\(\{L<0\}\) in the punctured surface. Indeed it is relatively
open and closed in that set. Extend the positive harmonic
function \(-L\) by zero off \(\Omega\); call the result v.
It is subharmonic on the punctured surface by the gluing lemma.
It remains to show v is bounded above near the removed points.

### 4.1 Leading complex difference at a pole

Let \(t\) be a local coordinate at a pole of \(\mathcal L\).
At least one \(H_\sigma\) has a pole. Let \(m\ge1\) be the
maximum pole order among the complex differences, and
\(d_\sigma=\lim_{t\to0}t^m H_\sigma(t)\). This vector is nonzero
and \(d_\pi=0\).

Let \(M\ge m\) be the maximum pole order among the matching
coordinates. If \(M=m\), the leading vector
\(p^*=\lim t^m p(t)\) belongs to the closed cone \(X_4\);
\(d=p^*-p^*_\pi\mathbf1\) is nonzero. Its old contact products
are all equal as complex numbers, because their differences
were fixed and vanish after multiplying by \(t^m\).
Sections 1--3 show that for every scalar \(\lambda\) such that
all \(\Re(\lambda d_\sigma)\ge0\) and some are positive,
\[
\sum_\sigma w_\sigma\Re(\lambda d_\sigma)>0.\tag{2}
\]
This includes any coincidence in a finite spectral
representation of \(p^*\), all swap-containing cases, and
the three remaining regular cases handled above.

If \(M>m\), the leading matching vector is constant and nonzero,
say \(t^Mp_\sigma\to c\ne0\) for every \(\sigma\).
All matching coordinates are nonzero for sufficiently small
nonzero t. Recover the anchor-normalized kernel from ratios of
two matching products as in the translation-line lemma. For
each nonanchor position choose a pair \(\sigma,\tau\) related
by exchanging the anchor assignment with that position.
Then
\[
\widetilde K_{ij}(t)=\frac{p_\sigma(t)}{p_\tau(t)}
=1+t^{M-m}(d_\sigma-d_\tau)/c+o(t^{M-m}).
\]
The common matching scale has leading term \(ct^{-M}\).
Multiplying the normalized entries and taking differences
between two permutations gives at order \(t^{-m}\)
\[
d_\sigma=\sum_i Q_{i,\sigma(i)}-\sum_i Q_{i,\pi(i)}
\]
with fixed coefficients \(Q_{ij}=d_{\sigma_{ij}}-d_{\tau_{ij}}\)
(and zeros in the anchor row/column). Thus the leading
difference is entry-type. The strict Birkhoff law of Section 1
again proves (2).

### 4.2 A negative component cannot accumulate at a pole

For any fixed angle \(\theta\), as \(t=\rho e^{i\theta}\to0\),
\[
\rho^m g_\sigma(t)\longrightarrow
\Re(e^{-im\theta}d_\sigma).
\]
If a small radial interval of angle \(\theta\) belongs to
\(\Omega\), all these limiting numbers are nonnegative.
Except for finitely many angles, they are not all zero:
choose one nonzero \(d_\sigma\) and its real part has only
finitely many angular zeros. By (2), at every such angle the
limiting value of \(\rho^m L\) is strictly positive. This
contradicts \(L<0\) in \(\Omega\).

To see why an entire angular interval is relevant, if
\(\mathcal L\) has a pole of order \(k\), choose an analytic
local coordinate \(s=t(1+O(t))\) such that
\(\mathcal L=c' s^{-k}\), \(c'\ne0\). This is possible by
taking a local analytic kth root of the nonvanishing factor.
The local negative set \(\{\Re\mathcal L<0\}\) is a union of
k open sectors of angular width \(\pi/k\) in the s coordinate.
Since \(\Omega\) is a whole negative component, if it
accumulated at this pole it would contain one of these
local sectors: there are finitely many, and each is connected.
In the original t coordinate that sector contains every
sufficiently small radial interval for all angles in a
nonempty open subinterval of its limiting angular sector.
Choose an angle outside the finite exceptional set above,
a contradiction. Hence \(\Omega\) cannot accumulate at any
pole of \(\mathcal L\).

At a removed point where \(\mathcal L\) has no pole it is
bounded. At its poles v vanishes in a punctured neighborhood,
by the preceding argument. Thus v is locally bounded above
near all the removed points.

The removable-singularity theorem for subharmonic functions
extends v to all of \(\Sigma\). A subharmonic function on a
connected compact surface is constant; v is positive at the
starting point, so the entire punctured surface must lie in
\(\Omega\). All \(\Re H_\sigma\) are then positive for the
new labels, forcing the meromorphic \(H_\sigma\) to have no
poles (the real part of a leading Laurent term at a pole takes
both signs). They are all constant on \(\Sigma\), contrary to
the choice of the curve.

We have proved that a new contact with all gaps nonnegative and
a strict violation must occur at a point of the affine curve.
It lies in the exact matching-profile cone and therefore has
finite complex spectral representatives. The fixed generic
unitary is unchanged, and at least seven contacts occur. QED.

## 5. Exact seven-contact boundary census and fifteen cases

All 48 mixed facets are related by the symmetry group of order
1152. Each has thirteen zero labels. Enumerating the seven-subsets
of one reference zero set and their symmetry orbits gives
exactly 100 distinct exceptional seven-contact classes. A
contact set outside these orbits is minor-only and already
proved by the facet classification and cone duality. A contact
set of size greater than seven can be treated by selecting any
seven labels.

The new exact checker certifies fifteen distinct seven-contact
orbits using the zero-height contact closure and cubic-sign
method in ZhengReconstructedSupplement.md. For every listed
case it checks a full rectangle or full three-label fiber
forcing zero height, then the closure under the rectangle and
fiber rules. It checks all supplied generator replacements
and the sign of the restricted cubic on every remaining
maximal mixed-positive support. The arguments are identical
to the uniform proof in Sections 2--4 of that previous note,
with the new seven-label sets and integer replacement table
in the checker.

Run from the repository root:

    python Lean/research/zheng_seven_contact_certificate.py

The exact identities, finite counts and all fifteen certificate
checks were executed successfully. Four CPU workers check
the cases in parallel; no numerical feasibility result is
used as a proof. The remaining 85 exceptional seven-contact
orbits are not certified by this method. This is a different
sufficient proof target from the original 90 six-contact
inequalities; the counts must not be combined as if they were
one fixed case list.

## 6. Scope of the reconstruction

The proof replaces individual six-contact pole estimates by
one theorem applicable to all 90 exceptional six-contact
orbits. It supplies the three previously untreated no-swap
complex-equality configurations and a uniform strict-positivity
mechanism at poles. It does not independently reconstruct the
whole of Zheng's supplement, nor prove every seven-contact
boundary inequality. In particular the dimension argument
cannot simply be repeated at seven contacts: fixing the six
complex differences can leave a zero-dimensional fiber.
All 100 seven-contact exceptional orbits have six linearly
independent differences in the ambient matching space;
additional spectral equations or a different geometric
argument are needed to proceed.

The paper's reported full theorem remains under review.
The proof of order five remains open, and this note does not
use order-four MOC as an axiom.
