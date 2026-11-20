# Literature audit: zero pairing and large scalar shifts

Audit date: 2026-10-16. This is a bounded literature check, not a claim of novelty.

## Four-dimensional zero-pairing theorem

Target statement supplied by the parent team:

For arbitrary normal 4 by 4 matrices A and B, if some eigenvalue pair satisfies
a_i+b_j=0, then MOC holds for every relative unitary U.

Equivalently, the spectra of A and -B intersect. By an opposite scalar shift and
reindexing, the target reduces to a_1=b_1=0, with all remaining six eigenvalues
arbitrary complex numbers. This is different from assuming det(A+UBU*)=0.

I did not locate this statement in the sources below or in targeted searches for
common/shared eigenvalues, overlapping/intersecting spectra, singular normal
pairs, zero sigma-points, and rank-three normal matrices. This absence is not
proof that the result is new.

Sources checked:

1. H. Huang, *A Survey of the Marcus–de Oliveira Conjecture*, Advances in Algebra,
   Springer Proc. Math. Stat. 277 (2019), 169–181, DOI
   10.1007/978-3-030-11521-0_8. The complete author-uploaded text is available at
   https://www.researchgate.net/publication/331388585_A_Survey_of_the_Marcus-de_Oliveira_Conjecture
   . Section 2.1 records the n<=3 theorem, the n-2 repeated-eigenvalue theorem,
   and the n=4 Householder theorem. Section 2.2 enumerates spectral sufficient
   conditions. The zero-pairing condition is not among those enumerated.

2. N. Bebiano and J. P. da Providencia, *Revisiting the Marcus–de Oliveira
   Conjecture*, Mathematics 13 (2025), 711, DOI 10.3390/math13050711.
   Publisher page https://www.mdpi.com/2227-7390/13/5/711 ; publisher-provided
   full text also retrieved at
   https://www.researchgate.net/publication/389331428_Revisiting_the_Marcus-de_Oliveira_Conjecture
   . Its Section 2 does not state the zero-pairing theorem. This survey is
   selective and omits some known conditions, so it cannot establish novelty.

3. Y. N. Shitov, *A further sufficient condition for the determinantal
   conjecture*, Izv. Math. 89:4 (2025), 862–869, DOI 10.4213/im9292e.
   Full primary text: https://www.mathnet.ru/eng/im9292 . The introduction lists
   the repeated-eigenvalue, two-valued-spectrum, line/circle, and mostly-real
   spectral classes; Theorem 1 establishes Hermitian A with at most three
   nonreal eigenvalues of B. Neither statement includes generic complex
   four-dimensional spectra sharing just one opposite eigenvalue.

4. C. K. Li, Y. T. Poon, N. S. Sze, *Ranks and determinants of the sum of matrices
   from unitary orbits*, Linear Multilinear Algebra 56 (2008), 105–130.
   Author PDF: https://cklixx.people.wm.edu/detrank.pdf . Theorem 3.3 and
   Corollary 3.11 concern empty-interior determinant ranges. For normal pairs,
   one relevant sufficient condition is an eigenvalue of A direct-sum -B with
   multiplicity at least n, not merely multiplicity two. The rank results
   discussing common eigenvalues are not MOC results for a generic zero pair.

5. S. W. Drury, *The external vertices conjecture in case n=4*, Electronic
   J. Linear Algebra 11 (2004), 180–191. Official full text:
   https://journals.uwyo.edu/index.php/ela/article/download/263/263/263 .
   Corollary 1.2 assumes zero is outside the convex hull of the permutation
   vertices and proves membership in the radially enlarged hull
   conv{r z_sigma : r>=1}. It does not imply the zero-pairing theorem, for
   which zero is itself a permutation vertex.

6. J. K. Merikoski and A. Virtanen, *Some further notes on the Marcus-de
   Oliveira determinantal conjecture*, Linear Algebra Appl. 187 (1993),
   259–262. Bibliographic record and abstract checked; full text was not
   retrieved. Huang Section 2.2 item 6 and Shitov's introduction attribute the
   two-distinct-eigenvalue theorem to it. Therefore this audit does not claim
   to have excluded an unmentioned observation in its full text.

Critical distinctions:

- Drury–Cload 1992 proves that an actually singular sum has determinant zero in
  the permutation hull. The new target allows the sum to be invertible and
  asks for its nonzero determinant to lie in the hull.
- In n=4, the known n-2 repeated-eigenvalue theorem requires a double
  eigenvalue in one individual spectrum. A common eigenvalue of A and -B
  allows both individual spectra to be simple.
- Opposite scalar shifts do not create a zero pairing unless it was already
  present. Common Mobius maps preserve a common point; they do not create one
  between two disjoint finite spectra.

## Generic large scalar shift / open spectral neighborhoods

Target supplied by the parent team: for fixed generic complex spectra a,b,
there is R(a,b) such that MOC holds for (diag(a)+sI,diag(b)), uniformly in U,
whenever |s|>R(a,b).

No matching theorem was located in searches for large scalar shifts,
translations, asymptotic MOC, near-scalar spectra, perturbations, and open sets
of spectra. The sources above did not state this result. No general theorem
saying every sufficiently small arbitrary complex perturbation of a generic
known pair remains valid was located either.

Important wording trap: Drury's *Essentially Hermitian matrices revisited*,
Electronic J. Linear Algebra 15 (2006), 285–296, Section 6, says the conjecture
is stable under perturbations, but immediately defines this only as closure
under limits of spectra for which MOC already holds. It is not an openness
theorem. Official primary PDF:
https://journals.uwyo.edu/index.php/ela/article/download/403/403/403
.

The same limit-only statement is repeated in K. Homadi's 2017 thesis,
*Progress on the Marcus-de Oliveira Determinantal Conjecture*, p.18:
https://auetd.auburn.edu/bitstream/handle/10415/5587/My%20thesis.pdf?isAllowed=y&sequence=2
.

Matthew Speck's 2024 dissertation *Determinants of Sums of Normal Matrices*
was checked for relevant sections and terms; its main development concerns
spectrum-independent coefficient constructions and unitary factorizations,
not either target spectral perturbation theorem. Full text:
https://etd.auburn.edu/bitstream/handle/10415/9283/Speck%20Dissertation%20Final.pdf?isAllowed=y&sequence=2
.

