# Exact reconstruction of the Cycle 03 and 04 cone tests

The inputs are the Gaussian-integer spectra and direction from the two
agendas. The scripts reconstruct the three generator sets independently;
they do not need the original verifier or the original dual vectors.

Run `python -B reconstruct_cones.py` and `python -B adaptive_squares.py`
here to replay the stored certificates using only Python's standard
library. `--discover` also uses NumPy and SciPy, and replaces the
corresponding certificate. Floating-point LP and eigensolver results
propose certificates only. Exact replay recomputes the contact labels,
all generator columns, the integer objective, and each pairing.

| Finite generator set | Distinct nonzero columns | Minimum dual pairing | Pairing with the agenda gap divided by 112 |
| --- | ---: | ---: | ---: |
| Subset events and the anchored primitive square dictionary | 8,401 | 12 | −13,610,681,254,740 |
| Subset events and all contact-compatible binary phases | 32,847 | 10 | −11,850,472,096,560 |
| Both dictionaries plus the larger Cycle 04 square | 41,056 | 10 | −10,193,549,372,564 |

The last line upgrades the stated **numerical-only** combined-cone
result to an independently replayed exact obstruction. The vectors
have a different integral scaling from the original reports. Padding
the sign-cone vector at the two contacts makes it pass every one of
the 65,536 binary masks, both orientations, and all subset indicators,
while preserving its negative objective.

The combined separator already fails a new admissible rank-one
square: take `x=(0,0,2,1,-2)`, `y=(0,-8,-2,-14,8)`, center at
the common score of the two contacts, and divide the squared score
column by the gcd of its entries. The pairing is −690,123. The
candidate was found by restricting the quadratic form on `y` to the
exact contact hyperplane for a given `x`; the exact checker verifies
the integer spectral score and negative pairing after discovery.

The [Cycle 01 Hall repair](../../agenda-2026-11-25/transport/README.md)
still certifies the same objective by 39 nonnegative event terms and
one nested Hall cut. The [separate replay](cycle01-hall-recheck.txt)
checks that repair. In particular neither a separator for this finite
dictionary nor a negative residual found in an adaptive square test
shows failure after adding the Hall repair. These are tests of
relaxations, not actual unitary counterexamples to MOC.
