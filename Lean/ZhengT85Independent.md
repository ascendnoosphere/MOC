# A direct reduction of the order-four $T_{85}$ case

This note treats the pattern in [Zheng, Section 5](https://doi.org/10.13140/RG.2.2.36790.25923) without the supplementary contact cone tables.
Use Zheng's lexicographic labels, put $p_j$ for the permutation
product, and put $g_j=p_j-p_0$. Use upper support, so that
$\operatorname{Re}(\eta g_j)\leq 0$. The six labels
$0,5,7,9,14,18$ are contacts.

**Theorem (T85, proof on paper).** If those six matching products
attain the upper support height in a common direction, then for every
complex unitary mixer the determinant lies on or below that supporting
line. No simplicity or nonzero pair-sum hypothesis is needed in the
statement. The proof below uses the checked reductions and the
[complete comparison of the remaining overlaps](#completion-of-the-t85-comparison).
It does not assume the supplemental proofs of T40, T55 or T81.

## Direct transfer (Lean checked)

[ZhengRectangleContact.lean](MOC/ZhengRectangleContact.lean) proves
$$
g_{18}g_9-g_5g_{14}=g_7g_{23},\qquad
g_{16}-g_{23}=g_5+g_7-g_9+g_{14}-g_{18}.
$$
These are identities in the eight spectral variables. They do not use
a facet list, the matching cubic, or arithmetic data. In a strict
witness the spectra must be simple and no sum $a_i+b_j$ can vanish,
by the existing order-four inclusion results for those cases.
In particular, $g_5\ne0$ since label 5 is a single swap.

If 23 is not a contact, multiply the quadratic by $\eta^2$. The
left-hand side is real, and $\eta g_7$ is purely imaginary. Since
$\operatorname{Re}(\eta g_{23})\ne0$, equality of imaginary parts
forces $g_7=0$. Fixing the other contact differences then determines
$g_{14}$ via the quadratic. With at most seven contacts, at most five
complex equations are needed. The varying-gap transfer produces a
strict witness with more contacts, retaining the mixer, direction,
pivot, and every old complex contact difference.

If 23 is a contact then 16 is one as well, by the linear identity.
Fixing the other contact differences determines $g_{14}$ through
the quadratic and then $g_{16}$ through the linear identity. At
eight contacts this still spends only five equations, so Lean also
gives a ninth contact in that branch.

The two branches have different support heights $H=\operatorname{Re}(\eta p_0)$.
The disjoint-swap rectangle $0,5,14,16$ gives
$$
(H-\operatorname{Re}(\eta p_{16}))|\eta p_0|^2
 = H\,\operatorname{Im}(\eta g_5)\operatorname{Im}(\eta g_{14}).
$$
Both imaginary factors and the pivot are nonzero. Thus 23 is a contact
exactly when $H=0$. In the unpaired branch $p_0=p_7$ and the other
rectangle $0,1,6,7$ gives $uv=p^2$, where
$(p,u,v)=\eta(p_0,p_1,p_6)$. The identity
$$
(\operatorname{Re}v-H)|u|^2
=(H-\operatorname{Re}u)|p|^2-H|u-p|^2
$$
rules out $H<0$: both $u$ and $v$ lie on or below the support
line, and the single-swap difference $u-p$ is nonzero. Hence the
unpaired branch has strictly positive upper height.

## The paired branch has a Lean-checked minor certificate

[ZhengPairedContacts.lean](MOC/ZhengPairedContacts.lean) checks the entire argument,
including the structural normal form, the mixed differences and their
telescoping, the nonnegative coefficients, and the squared-minor evaluation.
The two blocks are represented by a first Boolean coordinate and the
choices within each block by a second Boolean coordinate. The normal
form uses injectivity, not a list of the 24 permutations.

Let $I=\{1,3\}$ and $I^c=\{2,4\}$ in one-based labels, and let
$D$ be the group preserving the unordered pair $\{I,I^c\}$.
Its two block assignments each have two independent within-block
choices. The block-preserving labels are $0,5,14,16$; the
block-exchanging labels are $7,9,18,23$. All eight are contacts in
the paired branch.

For a permutation $\sigma$ outside $D$, put $K=\sigma^{-1}(I)$
and $J=\sigma(I)$. Each is a mixed two-set (one element per block).
Conversely every pair of mixed two-sets gives exactly one permutation:
in each source block, the point in $K$ must go to $I$ and the
point outside $K$ to $I^c$; precisely one target in each block is
in $J$, and these two targets must be filled from the source block
$I$. Thus the sixteen outside gaps form a $4\times4$ array
$C(K,J)$. The choice of one bit in each block makes each index set
a square.

Every adjacent mixed difference of $C$ is zero. To see this,
choose one swap in a source block (changing one bit of $K$) and one
swap in a target block (changing one bit of $J$). Independently
relabel the source and target by elements of $D$ to carry both
swaps to $s=(1\ 3)$ and the initial outside permutation to
$q=(2\ 3)$. Such relabeling is possible: first move the selected
blocks to $I$, then choose each within-block flip to send the two
mixed sets to those of $q$. The within-block flips preserve the
chosen swaps, and the preceding bijection determines $q$.
These relabelings preserve the condition that all of $D$ are
contacts. With row-to-column assignment, direct factorization gives
$$
p_q-p_{qs}-p_{sq}+p_{sqs}
=(a_1-a_3)(b_3-b_1)(a_2+b_2)(a_4+b_4)=p_0-p_s.
$$
Indeed the target swap first factors $(b_3-b_1)(a_4+b_4)$;
the source swap then subtracts
$(a_1-a_2)(a_3+b_2)-(a_3-a_2)(a_1+b_2)$.
The projection of $p_0-p_s$ vanishes. Telescoping over paths in
both squares proves that all mixed differences vanish.

Choose a global minimum at $(K_0,J_0)$. Then
$$
C(K,J)=u_K+v_J,\quad
u_K=C(K,J_0)-C(K_0,J_0)\ge0,\quad
v_J=C(K_0,J)\ge0.
$$
The two terms multiply the indicators of $\sigma(K)=I$ and
$\sigma(I)=J$, respectively, and those indicators also vanish
on $D$. This is a nonnegative two-minor decomposition of the
whole gap function; under any unitary, each indicator evaluates to
a squared minor. This step is the general
[support_of_minor_gap_decomposition](MOC/TwoValues.lean)
criterion, applied with direction $-\eta$. Thus the eight-label
paired branch cannot contain a strict witness, independently of
Zheng's supplementary proofs.

## Remaining target

The checked theorem [reduce_to_positive_eight](MOC/ZhengPairedContacts.lean)
reduces the six-label $T_{85}$ inequality
to strict witnesses with at least eight contacts, label 23 inactive,
strictly positive upper height, and the collision $p_0=p_7$. They do
not settle that subcase, nor other terminal patterns in Proposition
4.4 of the [preprint](https://doi.org/10.13140/RG.2.2.36790.25923).

[The collision-split theorem](MOC/ZhengRectangleContact.lean) now also
excludes simultaneous contacts at labels 1 and 6 in the positive-height
branch. [The normal form and further circle tests](GapFreeTerminalGeometry.md)
are paper arguments. [The alternating moment](AlternatingGapMoments.md)
gives a quadratic spectral invariant on that branch, not yet a support bound.


## One defect beyond the paired branch

Use the same two blocks and give each entry a coordinate `(block, bit)`
as in [ZhengPairedContacts.lean](MOC/ZhengPairedContacts.lean).
Let $K$ contain the two bit-zero positions and let $J$ contain the two
bit-one positions. The event $E(p)=1_{p(K)=J}$ says that $p$ flips the
bit at all four positions. On the block group $D$, this picks exactly
labels 16 and 23. Their common gap is $d$ by the linear identity above.
Thus every gap on $D$ is $dE(p)$, not just a bound by $d$.

For a crossing assignment $p=f\cdot\mathrm{cross}\cdot g$, the event
holds exactly when $f(i)=1_{i=g(0)}$ and $g(1)=1-g(0)$.
Consequently it marks two crossing cells, in different rows and columns.
Write $C$ for the crossing gap table and $R=C-dE$. The local mixed
difference identity applies to $E$ itself: take a matching product
with first spectrum $1_J$ and second spectrum $1_{K^c}$. Failure to
map $K$ onto $J$ makes one factor zero; a match makes all factors one.
The mixed identity therefore applies to the difference, whose
restriction to $D$ vanishes. In Lean, `single_block_defect_rectangle`
checks that $R$ is additive in its two indices.

If $R\geq0$, the minimum argument from the paired proof expresses $R$
as nonnegative row and column terms. Adding $dE$ then gives a
nonnegative subset-image certificate for every unitary; its evaluation
uses the squared-minor identity (Merikoski and Virtanen,
[DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X)).
Lean checks this in `support_of_single_block_defect`. Consequently a
strict witness must have $R(f_0,g_0)<0$ at a marked cell. Put
$t=d-C(f_0,g_0)>0$. If $f\ne f_0$ and $g\ne g_0$, the two crossed cells
$(f,g_0)$ and $(f_0,g)$ are unmarked and have nonnegative gaps. The
exact identity is
$$
C(f,g)=C(f,g_0)+C(f_0,g)+t+dE(f,g).
$$
In particular all nine cells outside the marked row and column are
strictly inactive, including the second marked cell. The Lean theorem
`crossing_contacts_confined` checks the support-gap lower bound $t$
on those nine cells. At eight or more total contacts at least two
crossing contacts must therefore come from the one row and column.

The remaining task for [Zheng's $T_{85}$ case, Section 5](https://doi.org/10.13140/RG.2.2.36790.25923)
is to bound the actual determinant in this marked-star case. The
negative entry of $R$ does not imply a negative determinant gap.

## The linear marked-star comparison is false

The marked row and column admit an exact signed decomposition. Use
$E$ for the defect event, $X$ for the indicator of crossing the
block partition, and $R_f,L_g$ for the row and column events. If the
marked cell is $(f_0,g_0)$, put $c_0=C(f_0,g_0)$ and
$t=d-c_0>0$. Then the gap at every permutation is
$$
 c_0 E + t G + \sum_{f\ne f_0} C(f,g_0)R_f
             + \sum_{g\ne g_0} C(f_0,g)L_g,\qquad
 G=E+X-R_{f_0}-L_{g_0}.
$$
This follows on the block group from $X=R_f=L_g=0$, and on
crossing cells from additivity of $C-dE$. The theorem
`gap_eq_marked_star_sum` checks the entire identity in Lean. Every
coefficient except the signed objective itself is nonnegative; the
minor theorem applies separately to the other terms.

To put $G$ in standard coordinates, use the order $00,01,10,11$
for the two bits and choose $f_0=(1,0)$, $g_0=(0,1)$, so the
original assignment is $\mathrm{flip}(f_0)\,r\,\mathrm{cross}\,\mathrm{flip}(g_0)$.
Write $A=\{0,1\}$, $B=\{0,2\}$, $S=\{0,3\}$, and
$I_{T,V}(r)=1_{r(V)=T}$. The block image condition is
$r(B)\in\{A,A^c\}$, the marked row is $r(B)=B$, the marked
column is $r(A)=A$, and the defect is $r(S)=S$. (The other
marked cell gives the same form after flipping the two inner bits.)
Thus
$$
 G=I_{S,S}+(1-I_{A,B}-I_{A^c,B})-I_{B,B}-I_{A,A}.
$$
Each row or column condition implies crossing. If both hold, $r$
fixes each intersection of the two binary partitions, so $r=1$
and the defect event holds. This proves $G\ge0$ pointwise. The six
block contacts and the seven crossing cells in the marked row and
column all have zero gap for this objective.

Nevertheless its signed unitary evaluation is negative on a whole
family of real orthogonal matrices. Let $c^2+s^2=1$ and use left
quaternion multiplication with quaternion $(c^2,cs,cs,-s^2)$
in the normalized coordinates. Write $Q$ for this matrix.
The two diagonal minors on $A,B$ are $c^2$, the diagonal minor
on $S$ is $c^4+s^4$, and the two minors with rows $A,A^c$
and columns $B$ have modulus $2c^2s^2$.
The signed evaluation is therefore
$$
 \Phi_Q(G)
 =1+(c^4+s^4)^2-8c^4s^4-2c^4
 =2s^4(1-2c^4).
$$
It is strictly negative for $s\ne0$ and $2c^4>1$.
[ZhengStarObstruction.lean](MOC/ZhengStarObstruction.lean)
checks this polynomial identity and its sign. It also proves that
even these five squared minors cannot be realized by one
nonnegative permutation law. Evaluation of the subset events uses
Merikoski and Virtanen's identities,
[DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X).

This is not a spectral counterexample. In the displayed labeling,
the two complementary swaps (labels 1 and 6 in
[Zheng, Section 5](https://doi.org/10.13140/RG.2.2.36790.25923))
lie on different arms of the marked row and column. The synthetic
ray makes both gaps zero while $d>0$, which the exact collision
identity forbids. Giving a small positive coefficient to each of the
two other row/column events that contain these swaps removes both
zero gaps, preserves at least eleven contacts, and still has negative
evaluation by continuity. Thus adding only the known
no-simultaneous-contact test does not repair the linear relaxation.
A proof must use more of the exact spectral equations to bound the
signed term against the other squared-minor contributions.

## Exact profiles avoid an open sector around the bad ray

The cubic equation alone does not rule out the bad ray. Use the
coordinates of Zheng's §5.3 with nonnegative gaps:
$\alpha_1,\ldots,\alpha_7$ are the gaps at labels
$17,15,11,6,4,12,1$, and $\beta$ is the gap at label 23 minus
the gap at label 17. Transposition exchanges the two possible
marked cells; here use the chart with $\beta>0$. The real
matching coordinates are obtained by taking the negative of the
upper projection, so the last scalar $h$ of the lift is **minus**
the upper support height. Using the opposite sign for $h$
would give a false exclusion from the cubic alone.

For $A=\alpha_4,\ B=\alpha_7,\ X=\alpha_2+\alpha_5,\
Y=\alpha_3+\alpha_6$, the matching cubic is $C_0+hQ$, where
$$
\begin{aligned}
Q&=(A-Y)(X-B)-\beta(X+Y+\beta)-\alpha_1(A+B),\\
C_0&=(A-Y-\beta)\alpha_2\alpha_5+(B-X-\beta)\alpha_3\alpha_6\\
   &\qquad-\beta(X+\beta)(Y+\beta)-\alpha_1AB .
\end{aligned}
$$
[ZhengT85Lift.lean](MOC/ZhengT85Lift.lean) checks the projected
coordinate lift directly from the bracket products, and
[FourMatchingPolarization.lean](MOC/FourMatchingPolarization.lean)
checks cubic vanishing on actual projections, including degenerate
ones. The latter uses the cubic normalization of Zheng, Appendix A
([preprint DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923)).
See Howard, Millson, Snowden and Vakil,
[DOI 10.1112/plms/pds016](https://doi.org/10.1112/plms/pds016),
for the eight-point invariant description.

Normalize by $\beta$. At $\alpha=0,\beta=1$ the only cubic root
has $h=-1$. The Hessian at that point is nonsingular:
[ZhengT85SecantObstruction.lean](MOC/ZhengT85SecantObstruction.lean)
checks its kernel by linear elimination. But the Hessian at the
real projection of an actual bracket point has rank at most 12
by Zheng's Corollary C.5. Equivalently, by the published secant
contraction of Howard, Millson, Snowden and Vakil
([DOI 10.1112/plms/pds016](https://doi.org/10.1112/plms/pds016)),
the polar map sends the 12-dimensional affine secant cone into
a 10-dimensional affine cone. At a general point its differential
on the secant tangent has a kernel of dimension at least two.
That differential is the Hessian restricted to the tangent space;
the resulting rank bound extends to the whole secant cone since
the larger minors vanish on a dense set. This geometric rank
bound is an external input, not a Lean axiom.
Near $\alpha=0$, $Q$ is nonzero and the cubic fixes
$h=-C_0/Q$ continuously. The Hessian remains nonsingular there.
Consequently there exists an open neighborhood of the bad ray
in normalized gap coordinates that contains **no actual
projected T85 profile**, regardless of the support height.
This eliminates more than the simultaneous contact at labels
1 and 6, but not the whole region of negative linear evaluation.

## Completion of the T85 comparison

The [center-and-split proof](ZhengT40PositiveOverlap.md) closes both T40
branches of the checked eight-contact reduction. It uses a spectral
secant equation and a weighted rotation comparison, not nonnegativity
on the entire linear contact cone. The last input, [the positive-height T55+20 overlap](ZhengT55PositiveOverlap.md),
uses a rational curve with fixed complex contact differences. The harmonic
minimum principle forces a strict violation onto one of five regular
boundaries. Their [exact secant and weighted rotation comparisons](ZhengT85ArmBounds.md)
rule out every violation. This closes the original six-label T85 support
inequality on paper by the [checked branch reduction](MOC/ZhengT81Bypass.lean).
The polynomial Hessian determinant factors and the curve argument are not
fully formalized in Lean. Other patterns in Proposition 4.4 remain separate.
