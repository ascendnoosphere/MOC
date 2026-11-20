# Mathematical document index

Start with the [research guide](research/README.md) for the latest derivation and
its remaining proof step. The subject indexes below lead to supporting proofs,
restricted cases, structural reductions, and independent reviews.

| Subject | Documents | Related code |
| --- | --- | --- |
| Current research; spectral, cofactor, spinor, and stochastic routes | [research guide](research/README.md) | [research code](../code/research/) |
| Order-four geometry, contacts, and weighted minors | [geometry](geometry/README.md) | [geometry code](../code/geometry/) |
| Coverage, exact non-Archimedean ranges, and probability models | [structural](structural/README.md) | [structural checks](../code/structural/) |
| Profile geometry and spectral-model reductions | [profile geometry](theorems/profile_geometry/README.md) | [algebra and geometry code](../code/theorems/profile_geometry/) |
| Finite/continuous geometry, spin, spectral moduli, and cones | [finite and spin geometry](theorems/finite_and_spin_geometry/README.md) | [exact code](../code/theorems/finite_and_spin_geometry/) |
| Restricted support inequalities and explicit certificates | [support certificates](theorems/support_certificates/README.md) | [exact code](../code/theorems/support_certificates/) |
| Number-system variants and exact ranges | [number systems](number_systems/README.md) | [checks](../code/number_systems/) |
| Coupling, tensor, and variational identities | [categorical](categorical/README.md) | [code](../code/categorical/) |
| Contact and cycle reductions | [closing](closing/README.md) | [code](../code/closing/) |
| Earlier structural identities | [early](early/README.md) | [code](../code/early/) |
| Fourier, neighborhood, and positive-law results | [broader](broader/README.md) | [code](../code/broader/) |
| Independent restricted-case derivations | [independent](independent/README.md) | [code](../code/independent/) |
| Standalone volume and reconstruction checks | [volume guide](volume/README.md) | [reconstruction code](../code/theorems/reconstructed_proofs/) |
| Theorem collections | [theorems](theorems/README.md) | [code](../code/theorems/) |

## Literature and original documents

[Complete PDF text](full_text/README.md) indexes all original PDF paths and links
to the retained [PDFs](pdfs/). These originals and their text extractions are
unabridged. [Third-party LaTeX sources](references/) preserve cited arguments;
their original build environments are separate from this project.

## Using historical references

Some notes cite original source filenames. [The layout map](../data/layout.json)
resolves retained legacy paths to their current files; `python3 -B code/run.py
--list` lists mapped runnable entrypoints. Later exploratory scripts may instead
refer to records in the [historical build snapshot](../archive/README.md).
Frozen handoffs and older exports are kept in `archive/`, outside the reading path.

- [Code guide](../code/README.md) and [running checks](reproduction.md)
- [Exact inputs and source mapping](certificates.md)
- [Folder organization and cleanup](cleanup.md)
