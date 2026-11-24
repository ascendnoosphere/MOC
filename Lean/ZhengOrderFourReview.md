# Review of Zheng's order-four preprint

Review date: 2026-11-24.

Source: Denzel Zheng, *The Marcus–de Oliveira conjecture for n = 4*,
preprint uploaded by the author on 2026-10-24,
[DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).
The author's [research index](https://denzelzheng.com/mathematics/) labels
the work a preprint. The reviewed user-supplied file has 66 pages and
SHA-256:

    1f3dafad5021bbeff8b4a9cbc79de45846c47c7bfb1d542167e8a8c29aa1c138

## Decision

The paper claims the complete order-four theorem for all complex spectra
and all relative unitaries. Its proof architecture is coherent, and the
specific finite computations reproduced below agree with the manuscript.
However, **the supplied main PDF is not a self-contained complete proof**.
Proposition 4.3 depends on the separate supplementary proofs of ninety
exceptional contact cases; Section 5 includes the T85 argument, but that
argument itself invokes the results for T40, T55, and T81 from the
supplement. The other eighty-nine cases, their common auxiliary
inequalities, the seven-contact subcases, and the supplemental source/data
are not present in the supplied PDF. Appendix F expressly refers to
supplementary material S0, S1, and S2. The file contains no embedded files.
The publicly accessible main preprint also did not provide those
supplementary proofs in the material inspected for this review.

Accordingly, record this as a **reported external proof, with independent
audit incomplete**. Do not add Conjecture (Fin 4) to the Lean-verified
results, insert an axiom, or infer that the remaining cases have been
verified. This is not a refutation of Zheng's theorem. The correct
next review input is the complete supplement and its verification code.

## 1. Dependency audit

| Result | Source | Review disposition |
| --- | --- | --- |
| Full theorem, order four | Theorem 1.1, Section 6 | Follows from the orthogonal reduction, six-contact theorem, and all contact inequalities. Last dependency remains unaudited. |
| Two orthogonal endpoint minor tables | Theorem 1.2, Section 2 | Plausible geometric argument using Gale duality and elliptic quartics. For the main MOC theorem, a finite convex mixture suffices. The repository already has the independent theorem four_minor_mixture in MOC/FourMinorTransport.lean, which gives that weaker, sufficient conclusion. The claim of exactly two terms is not inferred from the repository theorem. |
| Algebraic matching cone and spectral realization | Section 3.1, Appendix A | The matching-coordinate matrix and cubic identities independently checked. For the ordinary mathematical proof, the rank-two-profile closure in MOC/MatchingProfileClosed.lean and an elementary normalized-kernel chart provide an alternative construction of the cone. |
| Translation-direction exception and six-contact reduction | Lemmas 3.4–3.5, Theorem 3.6 | Argument examined; a separate proof extending it to every order, using the rank-two-profile chart and no cubic identity, is given in OrderFiveContactReduction.md. |
| 82 facets of minor polytope | Proposition 4.1 | Reproduced by independent exact computation, including completeness via a nonzero consistently oriented boundary cycle. |
| Contact cones | Lemma 4.2 | Standard finite-dimensional cone duality; the nonnegative generators are the active facets. |
| Six-contact orbit census | Section 4.2 | Exactly 214 orbits, 124 minor-only and 90 exceptional, independently reproduced. |
| Exceptional contact proof | Proposition 4.3, Appendix E/F/G | Missing essential supplement; cannot certify. |
| T85 | Section 5 | Key displayed coordinate and derivative identities independently verified. Its conclusion still uses three prior supplemental cases. |
| Coincident/repeated spectral values | Appendix B | Construction uses Birkhoff and max-flow/min-cut. Related order-four conclusions already exist in MOC/FourCoincidence.lean and MOC/TwoExceptions.lean; no new claim of independent verification of the stronger common-weight statement for every coincidence pattern. |
| One generalized-circle spectrum | Appendix C | Long separate geometric/analytic argument; not independently certified end to end. It cannot replace the missing general contact proofs. |

The independent finite mixture and other cited Lean results are already
in the repository; the Lean build was not rerun as part of this review.
The new Python checks are exact computations, not kernel-checked Lean
theorems.

## 2. Reproduced exact computations

Run from the repository root:

    python Lean/research/zheng_contact_audit.py
    python Lean/research/zheng_algebra_audit.py

These scripts require SymPy. They reconstruct the necessary coordinate
tables independently, rather than assume the missing supplementary
files. The equivalent local scripts were executed successfully.

### 2.1 Facets and contacts

Use the 24 permutations as vertices and the distinct singleton and
two-subset image-event functions as coordinate columns. Complementary
events give the same columns. Exact rational rank is 14 with the constant
function, giving an affine polytope of dimension 13.

The 34 minor functions and 48 nonminor functions of Section 4.1 were
reconstructed directly from their indicator definitions. Each is
nonnegative at every vertex; all 82 have distinct zero sets of affine
dimension 12. The nonminor profile values have the stated multiplicities
(13 zeros, 10 ones, 1 two).

An independently constructed pulling of these candidate facet sets
produces 6846 simplices. For each, the exact centered determinant is
nonzero and the vertex set belongs to exactly one candidate facet.
Orient the simplices by the determinant sign. Every coefficient in
their oriented boundary vanishes in integer arithmetic. The resulting
nonempty outward-oriented cycle covers the whole polytope boundary
by the positive-degree argument of Proposition 4.1. Thus the facet list
is complete. The modular rank calculation in the candidate generation
is not used as a certificate of completeness; the exact determinants
and cycle cancellation provide that certificate.

The adjacent left and right transpositions and inversion generate
the required action on the 134596 six-element subsets. Explicit
orbit traversal gives:

    214 orbits total
    124 orbits having only minor generators
     90 orbits allowing nonminor generators

These agree with the manuscript.

### 2.2 Matching coordinates and T85

The independent algebra script verifies:

* The fourteen noncrossing bracket polynomials in (A.1) are independent.
* Every bipartite matching polynomial is in their span, and the specified
  fourteen-row submatrix of P has determinant 1.
* The constant-profile coordinate is the last coordinate vector.
* Substitution of the bracket polynomials into each of the fourteen
  partial derivatives of C yields the zero polynomial.
* The specified partial-derivative coefficient submatrix has determinant 1.
* The seven adjacent label transpositions act by involutions on the basis
  and change the sign of C.
* The coordinate substitution (5.10) has determinant -1, gives the
  stated five contact differences, and satisfies (5.13), (5.14), (5.16)
  exactly.

These checks cover important algebraic pieces of the contact argument.
They do not certify the inequalities and Gram certificates omitted from
the main PDF. In particular they do not establish Proposition 4.3.

## 3. Recommended revision of the mathematical proof

For integration into this project, replace the need for the
elliptic-quartic construction of exactly two orthogonal endpoints by
the existing independent finite orthogonal minor mixture theorem.
Replace the special order-four translation-line argument by the
normalized-kernel translation lemma in OrderFiveContactReduction.md,
which works directly for complex unitary matrices and all orders.

The remaining order-four audit can then focus on the exact spectral
inequalities of Proposition 4.3 and their dependencies. Keep the
original preprint credited to Zheng; this review is not a rewritten
publication by its author. Do not redistribute the supplied paper as
an independently validated proof until its missing components can be
checked. The DOI above provides the public citation.

## 4. Implications for order five

Even without certifying the full order-four preprint, the contact
argument can be extended to a conditional-free result: any order-five
failure has a witness with at least eight contact permutations, keeping
the original relative unitary fixed. It does not require a real
orthogonal reduction in order five. See OrderFiveContactReduction.md.

If the full order-four theorem is ultimately certified, the existing
SparseRow theorem immediately covers order-five relative unitaries
with a row or column of degree at most two. It also covers the
complementary four-dimensional block in a proper paired block split,
and the existing smaller-order reductions can be specialized with
that theorem as a hypothesis. Do not use this conditional consequence
as a proof of order five before the hypothesis is certified.
