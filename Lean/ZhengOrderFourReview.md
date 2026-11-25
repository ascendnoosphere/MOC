# Lean status of Zheng’s order-four proof

The supplied 66-page [Zheng preprint](https://doi.org/10.13140/RG.2.2.36790.25923)
claims MOC in order four (Theorem 1.1). Lean checks the exact statement of
Theorem 1.2 and a sharper form of the six-contact reduction. It does not yet
check the terminal support bound in Proposition 4.4.

| Step | Lean status |
| --- | --- |
| Theorem 1.2: two real orthogonal squared-minor tables suffice | [`four_minor_two_point`](MOC/FourMinorTransport.lean) proves this for every order-four unitary. One coefficient serves all minors. [`realRowEffects_two_bases`](MOC/FourEffectDecomposition.lean) gives both bases directly, without adopting the preprint’s Picard-curve and Gale-duality argument. |
| Theorem 3.6: contact transfer | [`conjecture_four_iff_seven_orthogonal_contacts`](MOC/ZhengContactReduction.lean) reduces the full unitary conjecture to real orthogonal mixers at seven or more supporting contacts rather than six. The profile transfer keeps the mixer fixed, including when matching products vanish. |
| Proposition 4.4: terminal nonnegativity | Not verified. The supplied PDF gives one detailed exceptional case, which in turn invokes other exceptional cases. The separate supplement described in its appendices was not located at the [author’s research page](https://denzelzheng.com/mathematics/) or the [preprint record](https://doi.org/10.13140/RG.2.2.36790.25923). This does not refute the claimed result. |

The [technical audit](research/agenda-2026-11-25/OrderFourTwoEndpointAudit.md)
explains why the two ends of the effect line are both bases rather than further
mixtures. See [the proof tree](ProofTree.md) for the remaining implication.

[Independent progress on Section 5](ZhengT85Independent.md): Lean forces
eight contacts on the six-label pattern and proves the support-height
split. A symbolic two-minor decomposition now rules out the
[paired-contact branch in Lean](MOC/ZhengPairedContacts.lean). In the
positive-height branch, Lean [confines all crossing contacts to one
marked row and column](ZhengT85Independent.md#one-defect-beyond-the-paired-branch),
with a positive lower bound on each of the other nine gaps. The
positive-height comparison is now proved on paper.

The [T85 dependency repair](ZhengT40AndT85Dependencies.md) uses the checked
eight-contact reduction to remove T81 from this part of the proof.
It does not certify T81 as a standalone terminal case. Both
[positive-height T40 overlaps](ZhengT40PositiveOverlap.md) are proved
on paper, with the rotation comparison and secant-polynomial sign
step checked in Lean. The [positive-height T55+20 proof](ZhengT55PositiveOverlap.md)
completes the support comparison for T85 using the five boundary
bounds in [ZhengT85ArmBounds.md](ZhengT85ArmBounds.md). This is a
repair of Section 5, not a verification of Proposition 4.4 or a proof of
the full order-four conjecture.

## Independent coverage of the missing cases

The following is coverage of named contact sets, not an exhaustive
classification of all possible seven-contact supports. The auxiliary
seven-label propositions in Appendix G are dependencies of the original
six-label strategy; they are not stated as a complete seven-contact
catalogue.

| Group in [Appendix G](https://doi.org/10.13140/RG.2.2.36790.25923) | Independently covered | Verification scope |
| --- | --- | --- |
| I | [T1](ZhengT1Stabilizer.md) | Entire support theorem checked in [MOC.ZhengT1.support](MOC/ZhengT1Circle.lean), through an exact pole-free real-spectator chart and a common anchored law. |
| II | [T2](ZhengT2MinorCone.md), [T7](ZhengT7Direct.md), [T18–T20](ZhengEarlyRectangles.md) | All five support inequalities on paper. Lean checks chart identities or cubic signs and the nonnegative coefficients. |
| IV | [T21–T23](ZhengGroupIV.md) | All three support inequalities on paper, with checked cubic signs and constructive minor coefficients. |
| III | [T3](ZhengT3Support.md) and [T15](ZhengT15Support.md) | Both comparisons are proved on paper. Lean checks the paired-cofactor bound, the T3 cleared residue identity, and its scalar compensation. |
| V, VI | [T34 at zero height and label 13](ZhengT34Partial.md), [two standalone T40 boundaries](ZhengT40Standalone.md), [T55 with extra contact 0, 4, or 20](StandaloneT55.md), and [full T85](ZhengT85Independent.md) | Symbolic case arguments. The listed T34, T40 and T55 results do not close their entire cases. |

The [matching Hessian kernel](MOC/FourMatchingHessianKernel.lean) is now checked directly on real projections of exact bracket profiles; the individual symbolic factorizations used in the case proofs are separate.

The [stationary-pivot reduction](MOC/StationaryPivot.lean) imposes the
seven contacts and real global orbit maximality on a single witness.
The [two-rich-fibre paper proof](TwoRichPivotFibres.md) gives an
additional sufficient contact pattern, not a complete classification.

## Partial reductions on the uncovered groups

- **III:** [T10](ZhengT10Reduction.md) closes the ordinary minor branch
  and transfers the remaining branch to explicit boundary comparisons;
  [T11](ZhengT11Chart.md) gives its rational six-contact chart and
  proves the zero-height comparison on paper.
  The general T4, T5, T6, T10 and T11 bounds remain open here.
- **V:** [T40 boundary calculations](ZhengT40BoundaryBudget.md) give a
  conditional reciprocal budget and an exact mixed term, not the
  outstanding support inequality. The [real-lift obstruction](ZhengRealLiftObstruction.md)
  proves that the cubic equation and singular Hessian do not
  characterize projected spectral profiles, even at seven contacts.
- **VI:** [T55+7](ZhengT55Boundary7.md) reduces the remaining signed
  comparison at that contact to a quadratic with nonreal root or an
  explicit exceptional locus. Neither case proves the bound.

The full order-four conjecture still needs the uncovered terminal bounds
in Groups III, V and VI, or a proof that bypasses them. Nothing in this
table settles unrestricted order.
