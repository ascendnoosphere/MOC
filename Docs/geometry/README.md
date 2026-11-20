# Order-four support and profile geometry

Start with [MOC4 Verified Results](MOC4_Verified_Results.md), updated 31 October 2026. It states the support theorems, tracks later face closures, and identifies the remaining configurations. The dated notes in this directory preserve the proofs and audits behind individual stages; earlier partial counts should be read alongside that overview.

## Foundations and global reductions

- [Spectral and profile identities](structural_identities_and_audit.md): a quantitative cycle budget, a nearby spectral family, and profile geometry.
- [Standalone contact transfer](closing_high_contact_standalone.txt) and [audit of the two global bridges](full4_bridge_metaproof_audit.txt).
- [Exact 82-ray completeness](cone82_completeness_notes.txt) and the [order-four algebraic model](closing_moc4_notes.txt).
- [Profile geometry audit](profile_geometry_audit.txt) and [contact-complex audit](contact_complex_audit.txt).

## Support certificates by regime

| Regime | Proof notes |
| --- | --- |
| Eleven and ten contacts | [Terminal profile geometry](terminal_profile_geometry_notes.txt), [ten-contact theorem](terminal_ten_notes.txt) |
| Nine contacts | [Initial certificates](terminal_nine_notes.txt), [real-lift exclusion](global_moc4_nine_lift_notes.txt), [weighted propagation](global_moc4_weighted_propagation_notes.txt) |
| Universal weighted-minor inequality | [Analytic proof](global_weighted_minor_notes.txt) |
| Six-contact orbit | [Hessian-row closure](global_six_row_notes.txt) |
| Zero height | [Geometry and census](zero_height_geometry_notes.txt), [type 1](zero_height_type1_notes.txt), [types 3 and 4](zero_height_types34_notes.txt), [type 26](zero_height_type26_notes.txt) |
| Positive height | [Necessary constraints and middle-sector identity](positive_height_terminal_constraints.md) |

The [current overview](MOC4_Verified_Results.md) links the subsequent nine- and eight-contact closures retained under `docs/research/`.

## Local families, cycle budgets, and audits

[Profile cancellation](profile_cancellation_notes.txt), its [five-edge review](profile_family_edges_independent_review.txt), and the [safe-cone audit](profile_safe_cone_audit.txt) treat the local family. [Plücker notes](plucker_moc4_notes.txt) and their [independent audit](plucker_positive_metaproof_audit.txt) treat the quantitative cycle budget. The [algebraic terminal notes](proposal_algebraic_terminal_notes.txt) and [universal-polytope audit](proposal_universal_polytope_audit.txt) record the precise algebraic and convexity obligations. [Selected source sections](source_record_selected_sections.txt) retain the imported tetrahedral material.

These results leave unrestricted MOC4 open. [Geometry code](../../code/geometry/) contains the companion checks; consult the [reproduction guide](../reproduction.md). For the larger theorem collection, see [the theorem index](../theorems/README.md).

[Documentation index](../README.md)
