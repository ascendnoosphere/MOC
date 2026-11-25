# A direct reduction of the order-four $T_{85}$ case

This note treats the pattern in [Zheng, Section 5](https://doi.org/10.13140/RG.2.2.36790.25923) without the supplementary contact cone tables.
Use Zheng's lexicographic labels, put $p_j$ for the permutation
product, and put $g_j=p_j-p_0$. Use upper support, so that
$\operatorname{Re}(\eta g_j)\leq 0$. The six labels
$0,5,7,9,14,18$ are contacts.

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
