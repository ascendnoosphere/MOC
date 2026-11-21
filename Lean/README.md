# Marcus–de Oliveira in Lean

The library defines the conjecture for two ordered complex spectra and a relative unitary eigenbasis. The determinant and the convex hull use the complex matrix determinant and real convex combinations from Mathlib. The relative-eigenbasis identity connects this formulation to the expression with two unitary diagonalizations. The all-orders claim is the open proposition `MOC.MOCIsTrue`. [Standalone claim](MOC/Claim.lean)

With [Elan](https://github.com/leanprover/elan) installed, build the full library from the repository root.

```sh
cd Lean
lake build
```

The toolchain and transitive dependencies are pinned. Where the Mathlib cache is accessible, `lake exe cache get` can prefetch dependencies. For a source build when the Mathlib cache is unavailable, run `lake build proofwidgets:release` once to fetch the pinned widget assets, then `lake --no-cache build`. The publication worker uses the build worker's audit of every proof module against the allowed foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. The workflow and receipt locations are in [AGENTS.md](../AGENTS.md).

## Literature and repository coverage

The numbers below follow the [83-entry literature review](../Docs/references/Marcus-de-Oliveira-Literature-Review.md).

| Topic | Lean source and scope |
| --- | --- |
| Marcus and de Oliveira’s formulation (2–3, 40–53) | [Core](MOC/Core.lean) defines the full statement and proves the relative-basis, identity, commuting, and opposite-shift cases. The unrestricted conjecture is a proposition. |
| Small orders and repeated spectra (2, 3, 4, 6) | [Small](MOC/Small.lean) combines the full order-two and order-three results, including the paired (2+3) case in order five. [Weights](MOC/Weights.lean) proves the case of one potentially exceptional eigenvalue of the second summand in arbitrary finite order. |
| Birkhoff, compound matrices and a common permutation law (6, 8–10, 12–13, 16–18, 32, 71, 78) | [Weights](MOC/Weights.lean) proves the all-order signed Leibniz law, its exact singleton marginals, and positive weights whenever the spectral products depend linearly on singleton assignments. [Obstruction](MOC/Obstruction.lean) verifies the repository’s rational order-four witness against a common law on squared minors. It uses the obstruction mechanism of entry 9. |
| Paired blocks (23, 25) | [Blocks](MOC/Blocks.lean) proves Rodtes's direct-sum closure. [Claim](MOC/Claim.lean) uses it to exclude proper paired block splits after independent row and column relabeling in a least-order counterexample. |
| Shifted inverses and trace of a product (3, 5, 24, 64) | [Geometry](MOC/Geometry.lean) proves the common inversion equivalence, convex-hull transport under a nonzero complex multiplier, and the trace-of-product convex inclusion. |
| Singular sums (11, 63) | [Singular](MOC/Singular.lean) uses shared spectral moments and the order-three inclusion to cover singular sums in every finite order. [Wielandt](MOC/Wielandt.lean) gives the circle-or-line criterion for an attainable eigenvalue. |
| Hermitian and circle spectra (1, 21–22) | [Collinear](MOC/Collinear.lean) covers spectra on parallel affine lines. [CircleSpectra](MOC/CircleSpectra.lean) transports this result to the tangent-circle case. |
| Repeated values and shifted supports (12, 14) | [TwoValues](MOC/TwoValues.lean) covers a summand with at most two distinct eigenvalues. [TwoExceptions](MOC/TwoExceptions.lean) covers a summand constant outside at most two labels. [RankTwoOverlap](MOC/RankTwoOverlap.lean) covers opposite scalar shifts that make the sum of support sizes at most \(n+2\). |
| Householder reflections and interlacing (19, 24) | [HouseholderFour](MOC/HouseholderFour.lean) covers rank-one phase updates through order four. [Interlacing](MOC/Interlacing.lean) proves Shitov’s partial matching hull inclusion and its finite-hull stability ingredient. |
| Recent proof claims and counterexamples (54–62) | The review records their stated scope and publication status. The library uses no proof claim from these entries as a premise. |

The all-orders reduction in [SpectralGap](MOC/SpectralGap.lean) imposes unit spectral energy, equality of the two traces, equality of their squared-norm-weighted traces, and a nonnormal sum. [SupportBlocks](MOC/SupportBlocks.lean) gives strict support expansion in a least-order counterexample. [Extremal](MOC/Extremal.lean) combines these conditions and adds the test from centered fractional-linear changes.

The repository's [case index](../Docs/Cases/README.md) gives the broader research scope. The Lean project checks the equal-trace equivalence in case D and the direct-sum mechanism. The order-four Hermitian-side theorem, rank-sum theorem, spin and quaternion Bernstein certificates, regular spectral pencil, and global mixed-facet argument still use their written proofs and separate verifiers. [Exact checks and report builds](../Docs/reproduction.md)

The [historical Lean status](../Docs/research/moc_unrestricted_lean_status.txt) describes a larger source tree from an earlier workspace. This project uses the same Lean version and Mathlib revision.
