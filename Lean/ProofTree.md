# MOC proof tree

## Overview

Read the arrows from a proof route toward its conclusion.
**Iff** labels mark checked equivalences. A plain arrow marks a checked
sufficient implication, not a proof of its premise. Dashed arrows mark
research dependencies, not proved implications. Orange nodes are open;
green nodes describe steps that Lean has proved. The diagrams group
related routes. [ProofRoutes.lean](MOC/ProofRoutes.lean) gives the full list.

```mermaid
flowchart BT
    ALL["Unrestricted MOC · open"]:::open
    ROUTES{{"OR: choose a complete all-order route"}}
    NATIVE["Native and structural analogies<br/>exact and sufficient routes"]:::open
    ATLAS["243 evaluated atlas forms<br/>each exact, not a native-object proof"]:::open
    SPLIT{{"AND: prove all three order ranges"}}
    FOUR["Order 4 · open"]:::open
    FIVE["Order 5 · open"]:::open
    HIGH["Orders 6 and higher · open"]:::open
    LOW["Orders 0 to 3 · already proved"]:::checked
    NATIVE --> ROUTES
    ATLAS --> ROUTES
    FOUR --> SPLIT
    FIVE --> SPLIT
    HIGH --> SPLIT
    LOW -. already covered .-> SPLIT
    SPLIT --> ROUTES
    ROUTES <-->|iff| ALL
    ALL --> FOUR
    ALL --> FIVE
    classDef open fill:#fff1d6,stroke:#9a5900,color:#231500
    classDef checked fill:#ddf6e7,stroke:#287348,color:#10291a
```

## Order four: the main proof routes

```mermaid
flowchart BT
    FOUR["Order 4 · open"]:::open
    OR4{{"OR: prove one complete route"}}
    WITNESS["Exclude every regular stationary<br/>orthogonal counterexample"]:::open
    NORMAL["A normal sum at some maximizer<br/>of each support problem"]:::open
    PENCIL["A positive law for each<br/>one-entry complex pencil"]:::open
    CHART["Three-anchor kernel or<br/>principal-coisometry comparison"]:::open
    AND4{{"AND: contact route"}}
    TRANSFER["Increase the contact count<br/>below 6 · open in Lean"]:::open
    SIX["Support bound at 6 or more contacts · open"]:::open
    TESTS["Checked witness tests: Hessian,<br/>reflections and flat row planes"]:::checked
    PHASE["Checked contact tests: triple fibres,<br/>rectangles and cross ratios"]:::checked
    WITNESS --> OR4
    NORMAL --> OR4
    PENCIL --> OR4
    CHART --> OR4
    TRANSFER --> AND4
    SIX --> AND4
    AND4 --> OR4
    TESTS -. narrow the witness set .-> WITNESS
    PHASE -. restrict realizable profiles .-> SIX
    OR4 <-->|iff| FOUR
    classDef open fill:#fff1d6,stroke:#9a5900,color:#231500
    classDef checked fill:#ddf6e7,stroke:#287348,color:#10291a
```

## Order five: the main proof routes

```mermaid
flowchart BT
    FIVE["Order 5 · open"]:::open
    OR5{{"OR: prove one complete route"}}
    DENSE["Bound every regular full-support instance · open"]:::open
    PENCIL["A positive law for each one-entry pencil"]:::open
    CHART["Three-anchor kernel or<br/>principal-coisometry comparison"]:::open
    ANDN{{"AND: normal-maximizer route"}}
    FOUR["Order 4 · open"]:::open
    NORMAL["A normal sum at some maximizer<br/>of each order-five support problem"]:::open
    ANDC{{"AND: contact route"}}
    TRANSFER["Increase the contact count<br/>below 8 · open in Lean"]:::open
    EIGHT["Support bound at 8 or more contacts · open"]:::open
    ANDO{{"AND: orthogonal route"}}
    REAL["Order-five bound for orthogonal mixers · open"]:::open
    MIX["Two-table orthogonal convexification · open"]:::open
    COST["Checked pair-cost formula<br/>and objective-specific certificates"]:::checked
    DEAD["Universal positive common law<br/>refuted; not an MOC counterexample"]:::blocked
    DENSE --> OR5
    PENCIL --> OR5
    CHART --> OR5
    FOUR --> ANDN
    NORMAL --> ANDN
    TRANSFER --> ANDC
    EIGHT --> ANDC
    REAL --> ANDO
    MIX --> ANDO
    ANDN --> OR5
    ANDC --> OR5
    ANDO --> OR5
    COST -. can help on each objective .-> DENSE
    COST -. can help on each objective .-> EIGHT
    OR5 <-->|iff| FIVE
    classDef open fill:#fff1d6,stroke:#9a5900,color:#231500
    classDef checked fill:#ddf6e7,stroke:#287348,color:#10291a
    classDef blocked fill:#fae5e5,stroke:#a33434,color:#361010
```

## Shared contact gap

```mermaid
flowchart BT
    TRANSFER["Increase contacts at a strict witness"]:::open
    BOTH{{"AND: supply the curve and apply transfer"}}
    SLICE["Construct a fixed-gap curve through<br/>each low-contact witness · open in Lean"]:::open
    FIXED["Fixed-gap transfer on a supplied curve<br/>and finite iteration · checked"]:::checked
    PLANE["Connected plane root cover<br/>including exceptional fibres · checked"]:::checked
    CHART["Exact rank-one charts and<br/>translation obstruction · checked"]:::checked
    PLANE -. toward a model for the slice .-> SLICE
    CHART -. sets up the constraints .-> SLICE
    SLICE --> BOTH
    FIXED --> BOTH
    BOTH --> TRANSFER
    classDef open fill:#fff1d6,stroke:#9a5900,color:#231500
    classDef checked fill:#ddf6e7,stroke:#287348,color:#10291a
```

The [Lean tree](MOC/ProofRoutes.lean) has three roots: all finite orders,
order four, and order five. An **OR** node needs one complete branch.
An **AND** node needs every child. A branch can be open even when Lean
has proved that it would be enough.

## All finite orders

- **OR: A native comparison.** The Lean list links each included
  comparison to MOC. Examples include normalized matrix pencils,
  finite determinant paths, transport between spectral multiplicities,
  and traceless spectra. The [native audit](MOC/Reformulations/NativeAudit.lean)
  records the scope and direction of each link. It also lists analogies
  that do not give a proof of MOC.
- **OR: An evaluated atlas comparison.** Each of the 243 numbered
  links uses complex evaluation on labelled finite data. This branch
  does not identify the original native objects with MOC.
- **OR: An order split.** Prove order four **AND** order five **AND**
  all orders at least six. The cases of order at most three are already
  proved.

## Order four

The checked alternatives include:

- Prove the hull inclusion for real orthogonal mixers with complex
  spectra. It is enough to exclude every
  [regular stationary orthogonal witness](MOC/OrderFourIndependent.lean).
  Use the [second-order](MOC/OrderFourSecondVariation.lean),
  [reflection](MOC/OrderFourReflectionTest.lean), and
  [flat row-swap](MOC/OrderFourGivens.lean) tests on these witnesses.
- Show that every directional support maximum has a representative
  whose sum is normal.
- Prove the [common law for each one-entry complex pencil](MOC/ProofRoutes.lean),
  or the [three-anchor kernel bound](MOC/Reformulations/ThreeAnchorKernel.lean).
- Prove a one-contact transfer **AND** the support bound at six or more
  contacts. The [fixed-gap step](MOC/ContactCurveStep.lean) applies once
  the required curve exists. The construction of that curve is open in Lean.

## Order five

The checked alternatives include:

- Prove the hull bound for regular spectra and mixers with no zero entries.
- Prove the one-entry law separately for each pencil. One law need not
  work for different pencils.
- Prove order four **AND** show that each order-five support problem
  has a maximizer with a normal sum.
- Prove a one-contact transfer **AND** the support bound at eight or
  more contacts, for mixers with no zero entries.
- Use [subset assignment certificates](MOC/SubsetAssignmentSupport.lean)
  on individual support objectives. The [doubleton image tests](MOC/OrderFivePairMarkers.lean)
  identify which minor data a fixed law must preserve. A universal
  positive common law is not an active branch: [Drury's Householder
  counterexample](https://doi.org/10.1016/S0024-3795(99)00173-1)
  rules out that stronger property in order five. The library now has a
  [symbolic Lean proof of this obstruction](MOC/OrderFiveCommonLawObstruction.lean).
  The [explicit pair cost](MOC/OrderFivePairCost.lean) expresses every
  directional order-five objective in these coordinates.
- Prove orthogonal order five **AND** a two-table orthogonal
  convexification for complex mixers. The library does not supply the
  convexification in order five.

Each inhabited atlas sample also gives an exact evaluated comparison at
order four and at order five. This stays at the selected order and does
not imply the corresponding native claim.

An all-order branch can also close either finite-order root. This
does not reduce an all-order goal to only two orders. A refutation of
a sufficient-only branch does not refute its parent. For an exact
equivalence, proof and refutation both transfer.

## Checked steps toward the open branches

- [Local holomorphic root cover](MOC/FiniteCurveRootCover.lean):
  separable fibres of a monic plane polynomial have complete
  local holomorphic branches. The [global gluing](MOC/FiniteCurveConnected.lean)
  proves connectedness for a punctured simple-root cover of an irreducible
  plane polynomial. The [full plane zero set](MOC/FiniteCurveClosure.lean)
  is also connected, including exceptional fibres. The curve slice
  through each witness is still a separate step.
- [Cross-ratio test](MOC/ContactCrossRatios.lean):
  one four-swap pattern at nonzero height imposes a positive real
  product of two spectral cross ratios.
- [Parity corrections](MOC/FiveParityCorrection.lean):
  these changes preserve every subset-image mass. A repair must
  still make the weights nonnegative.
- [Sparse geometry](MOC/OrderFiveSparseGeometry.lean):
  a failure with at least eight mixer zeros forces an order-four
  failure. This is a reduction, not an order-five proof on dense mixers.
- [Spectral collisions on a sparse row](MOC/SparseSpectralCollision.lean):
  a three-supported row reduces to the preceding order if two of its
  supported column labels coincide. Unequal labels are not preserved
  by the same rotation.
- [Parity repair threshold](MOC/QuaternionParitySharp.lean):
  the proposed displacement-label repair has an exact scalar feasibility
  test. This excludes that repair below its threshold, not the hull
  inclusion or other possible repairs.
- [Flat disjoint row planes](MOC/OrderFourFlatPlanes.lean):
  at a strict order-four witness, two flat disjoint signed swaps must
  have a strictly losing product. Otherwise the rotations create a
  sparse column and reduce to order three.
- [Branch values](MOC/FiniteCurveBranchValues.lean): the omitted
  nonseparable fibres of a monic irreducible plane polynomial form a
  finite set. Its regular root cover is connected.
- [Reciprocal-conjugate support](MOC/ReciprocalConjugateSupport.lean):
  a Gram inequality proves the matching bound in a specified direction
  for reciprocal-conjugate spectra, in every order. It is not a bound
  in every direction for those spectra.
- [Pair assignment relaxation](MOC/PairAssignmentObstruction.lean):
  for a separated pair-cost class, a best assignment of pairs can
  beat every assignment induced by a permutation of the labels.
  This is an obstruction to the relaxation, not to MOC.

## Transfer between branches

Lean records the reverse proof for each exact branch. Two exact
branches under the same root imply each other. Any sufficient branch
implies every exact branch under its root. An all-order branch also
implies each exact branch in orders four and five. For a one-way
branch, the proof does not infer its premise from its conclusion.
The [native audit](MOC/Reformulations/NativeAudit.lean) records which
additional special-case and restricted comparisons are not root branches.
