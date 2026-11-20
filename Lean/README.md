# Marcus–de Oliveira in Lean

The library defines the conjecture for two ordered complex spectra and a relative unitary eigenbasis. The determinant and the convex hull use the complex matrix determinant and real convex combinations from Mathlib. The relative-eigenbasis identity connects this formulation to the expression with two unitary diagonalizations.

With [Elan](https://github.com/leanprover/elan) installed, build the full library from the repository root.

```sh
cd Lean
lake build
```

The toolchain and transitive dependencies are pinned. Where the Mathlib cache is accessible, `lake exe cache get` can prefetch dependencies. For a source build when the Mathlib cache is unavailable, run `lake build proofwidgets:release` once to fetch the pinned widget assets, then `lake --no-cache build`. The umbrella module imports each proof module and prints the axioms used by the main results.

## Literature and repository coverage

The numbers below follow the [83-entry literature review](../Docs/references/Marcus-de-Oliveira-Literature-Review.md).

| Topic | Lean source and scope |
| --- | --- |
| Marcus and de Oliveira’s formulation (2–3, 40–53) | [Core](MOC/Core.lean) defines the full statement and proves the relative-basis, identity, commuting, and opposite-shift cases. The unrestricted conjecture is a proposition. |
| Small orders and repeated spectra (2, 3, 4, 6) | [Weights](MOC/Weights.lean) proves orders zero through three and the case of one potentially exceptional eigenvalue of the second summand in arbitrary finite order. |
| Birkhoff, compound matrices and a common permutation law (6, 8–10, 12–13, 16–18, 32, 71, 78) | [Weights](MOC/Weights.lean) proves the all-order signed Leibniz law, its exact singleton marginals, and positive weights whenever the spectral products depend linearly on singleton assignments. [Obstruction](MOC/Obstruction.lean) verifies the repository’s rational order-four witness against a common law on squared minors. It uses the obstruction mechanism of entry 9. |
| Paired blocks (23, 25) | [Blocks](MOC/Blocks.lean) proves direct-sum closure. It applies to the repository’s 2+2 and 1+3 eigenbasis splits, and to 2+3 in order five. |
| Shifted inverses and trace of a product (3, 5, 24, 64) | [Geometry](MOC/Geometry.lean) proves the common inversion equivalence, convex-hull transport under a nonzero complex multiplier, and the trace-of-product convex inclusion. |
| Range geometry and the Hermitian bounds (1, 7, 15, 20–22, 26–39) | The definitions expose the range and its permutation hull. The general Hermitian extreme-value theorem, separate-circle theorem, external-vertices theorem, and topological results remain outside the checked proofs. |
| Remaining special cases and related work (11, 12, 14, 19, 24, 25, 63–83) | The checked cases above cover some shared ingredients. General singular sums, two-distinct-eigenvalue spectra, rank-two shifted summands, the full Householder theorem, Shitov’s interlacing argument, and the related inequalities retain their bibliography entries. |
| Recent proof claims and counterexamples (54–62) | The review records their stated scope and publication status. The library uses no proof claim from these entries as a premise. |

The repository's [case index](../Docs/Cases/README.md) gives the broader research scope. The Lean project checks the equal-trace equivalence in case D and the direct-sum mechanism. The order-four Hermitian-side theorem, rank-sum theorem, spin and quaternion Bernstein certificates, regular spectral pencil, and global mixed-facet argument still use their written proofs and separate verifiers. [Exact checks and report builds](../Docs/reproduction.md)

The [historical Lean status](../Docs/research/moc_unrestricted_lean_status.txt) describes a larger source tree from an earlier workspace. This project uses the same Lean version and Mathlib revision.
