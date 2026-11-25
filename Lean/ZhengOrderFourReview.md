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
