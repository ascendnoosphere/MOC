# Marcus–de Oliveira in Lean

This Lean 4 library proves cases of the Marcus–de Oliveira conjecture (MOC).
It also proves reductions of the general problem. The library does not prove
MOC for all finite orders.

## What Lean proves

- **Orders up to three:** MOC holds for all pairs of normal matrices.
  [Proof](Lean/MOC/Small.lean)
- **Singular sums:** If the sum of the two normal matrices is singular, MOC
  holds in any finite order.
  [Proof](Lean/MOC/Singular.lean)
- **Spectra on circles or lines:** If each spectrum lies on a circle or a
  line, MOC holds in any finite order. The two spectra can lie on different
  circles or lines.
  [Proof](Lean/MOC/TwoSpectralCircles.lean)

See the [detailed list of proved cases](Lean/ProvedCases.md) for the exact
conditions and proof files.

## An equivalent statement

One reduction uses only spectra whose entries sum to zero. It also uses only
unitary changes of eigenbasis with no zero entries. In orders four and higher,
it suffices to prove that the real part of the determinant is at most the
real part of one matching product. To form a matching product, pair the
eigenvalues of the two matrices, add each pair, and multiply the sums.
A counterexample to this restricted statement also refutes MOC.
[Proof of equivalence](Lean/MOC/Reformulations/TracelessSupport.lean)

See the [proof tree](Lean/ProofTree.md) for the routes to the full conjecture and to orders four and five.

See the [source guide](Lean/README.md) for more reductions. It links to the
indexes of checked proofs, restricted results, and open questions.
See the [literature and DOI guide](Lean/Literature.md) for the sources and the
exact scope of each technique used.

## Build and check

Install [Elan](https://github.com/leanprover/elan). From the repository root,
run:

```sh
cd Lean
lake build
```

The build uses the versions in [lean-toolchain](Lean/lean-toolchain) and
[lake-manifest.json](Lean/lake-manifest.json). It checks the project proofs
and reports any axiom outside the standard Lean list.
[Proof check](Lean/MOC.lean)
