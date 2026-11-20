# Research notes

Start with the latest all-dimensional synthesis, then follow a topic below.
Unrestricted complex Marcus–de Oliveira (MOC) remains open in these notes.
The collection contains written reduction theorems, scoped support certificates,
exact obstructions to stronger proposed bridges, and numerical investigations.
A counterexample to a bridge or to the stronger polygon conjecture is not a
counterexample to MOC.

## Current reading order

1. [All-dimensional contact reduction](next_unrestricted_research.md) is the
   main entry point. It gives a fixed-unitary reduction to actual sources with
   at least `2n−2` supporting contacts. Equation (19), positivity on those
   high-contact sources, is the remaining assertion equivalent to MOC.
2. [Harmonic inversion and constant-source lines](next_harmonic_algebra.md)
   supplies the signed-law formula, source chart, and classification and
   positive repair of exceptional constant-parallel lines used in that reduction.
3. [Extremal geometry](next_extremal_geometry.md) treats balancing and compact
   minimizers, and proves why monotone rank-one phase moves are insufficient.
4. [Probabilistic rounding](next_probabilistic_rounding.md) gives exact flag
   disintegration and a source-dependent change of measure at one obstructed
   input. Its capped-expectation bound identifies the all-source obligation.
5. [Normal-compression mechanism](next_archive_mechanism.md) develops
   pole-dependent rank-one resolvent defects and the directional compensation
   inequality still needed for induction.

These notes distinguish written proofs from finite checks. Their reading
inventories and workspace counts describe the investigation at the time of
writing, before later cleanup.

## Global source geometry and contact reductions

For the dimension-four algebra behind the latest source chart, use
[product linkage](M8_PRODUCT_LINKAGE.md),
[HMSV compatibility](HMSV_COMPATIBILITY.md), and
[corank-two lift exactness](CORANK_TWO_LIFT_EXACTNESS.md).
The [complex-curve exit theorem](moc_global_complex_curve_exit_theorem_20261031.txt)
is the earlier dimension-four contact argument.

The [twenty-nine-face reduction](moc_twenty_nine_face_global_reduction_20261031.txt)
is conditional: its stronger all-N9 containment hypotheses were refuted by the
[exact face30 escape](moc_face30_full_sos_nonic_escape_20261031.txt).
Retain the distinction between formal nonic costs and actual spectral sources.

## Cofactors, Cayley coordinates, and variational geometry

The [four-dimensional cofactor hull](moc_four_dimensional_cofactor_hull_20261031.txt)
and [rectangular compression reduction](RECTANGULAR_COMPRESSION_REDUCTION.md)
record exact reformulations. For polynomial coordinates and optimization, see
[global Sinkhorn reduction](SINKHORN_GLOBAL_REDUCTION.md),
[real cofactor bounds](REAL_COFACTOR_BOUND.md), and
[compact mixed Hessians](moc_compact_mixed_hessian_20261031.txt).

## Matching SOS, duals, and positive kernels

Start with the [intrinsic real matching-SOS cone](moc_intrinsic_matching_sos_20261031.txt)
and its [dual geometry](moc_sos_dual_body_structure_20261031.txt).
The [auxiliary PPT cone](moc_qft_auxiliary_cone_closure_20261031.txt) gives the
related positivity construction; the [dimension-five kernel theorem](moc_n5_universal_clifford_kernel_20261031.txt)
and [independent audit](moc_n5_universal_kernel_independent_audit_20261031.txt)
record a higher-dimensional real-orthogonal result.
Universal positivity of these cones or kernels is separate from membership of
every actual support cost.

## Contact families and constructive certificates

The [mixed cancellation graph](mixed_cancellation_graph.txt) organizes canonical
caps. The [single-mixed six-contact census](single_mixed_six_contact_census.txt)
and [cap contact-subset census](moc_cap34_contact_subset_census_20261031.txt)
provide navigation into the many `eight_*`, `six_*`, and `residual_face*` notes.
Representative uniform results are the
[normal Klein-four theorem](moc_normal_v4_uniform_triangle_sos_theorem_20261031.txt)
and [actual H-contact theorem](moc_klein_actual_ordinary_theorem_20261031.txt).
For the star face, use the [block-Gram equations](moc_star_block_gram_affine_20261031.txt)
and [source-Cauchy certificate](moc_star_cauchy_primary_exact_20261031.txt).

## Exact route boundaries

Keep these counterexamples with the mechanisms they delimit:

- [Actual failure of the three-budget triangle criterion](moc_actual_triangle_failure_integer_20261031.txt)
  and the [same input's full-SOS certificate](moc_future_hit_exact_gram_20261031.txt).
- [Failure of the universal common-five-plane ansatz](moc_joined_positive_plane_ansatz_refuted_20261031.txt),
  distinct from cost-dependent certificates.
- [Failure of singleton-preserving rounding](singleton_rounding_obstruction.md),
  which motivates source-dependent measure changes.
- [Counterexample to Kovačec's stronger polygon conjecture](related_conjecture_polygon.txt)
  and its [independent audit](kovacec_polygon_independent_review.txt).

## Campaign evidence, literature, and formalization

The [seven-lane report](moc_seven_moonshots_20261031.txt) summarizes the major
campaign results. The [extensive analysis](moc_extensive_analysis_20261031.txt)
and [visual atlas](moc_visual_atlas_20261031.txt) organize numerical evidence.
The [literature bridge audit](moc_literature_bridge_audit_20261031.txt) and
[primary generalized-circle check](moc_two_generalized_circle_primary_20261031.txt)
record source verification. For formal scope, use the
[unrestricted Lean status](moc_unrestricted_lean_status.txt) and individual
`*_lean_status*` notes; a compiled scalar lemma does not formalize an entire
analytic or geometric bridge.

Files named `*checkpoint*`, `session_*`, and `moonshots_*` preserve historical
campaign states. Read later corrections before reusing an older candidate.
Notes named `*_independent_review*`, `*_audit*`, `*_oracle*`, and `*_lemmas*`
provide connected audits and derivations, rather than a separate chronology.
Historical `build/` paths identify outputs recorded at the time; generated
artifacts may need reproduction after cleanup.

## Related conjectures and wider document map

The direct investigations of [Chollet](chollet_direct_boundary_attack.md),
[Rota](rota_direct_capacity_attack.md), and [Erdős #1020](erdos_1020_direct_core_attack.md)
have separate hypotheses and unresolved steps.
[Sequence identities and convergence](moc_oeis_convergence.md) collect the
associated exact formulas and numerical audits.

Use the [main mathematical index](../README.md) for curated theorem collections,
[full-text source index](../full_text/README.md) for original PDF extractions,
and [reproduction guide](../reproduction.md) for entrypoints. Legacy paths
quoted inside older notes can be resolved through
[`data/layout.json`](../../data/layout.json). Existing filenames are retained
so historical references remain usable.
