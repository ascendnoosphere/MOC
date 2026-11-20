# The Marcus–de Oliveira determinantal conjecture

Annotated literature review through 20 November 2026 · 83 references

## Summary of results

The Marcus–de Oliveira conjecture remains open for general normal matrices. It proposes a bound on the determinant of a matrix sum that uses only the eigenvalues of the two matrices. Pair the eigenvalues in each possible order, add each pair, and multiply the sums. The proposed region is the convex hull of these products in the complex plane. ([2](#ref-2), [3](#ref-3), [25](#ref-25))

Fiedler proved sharp bounds for two Hermitian matrices in every dimension. For arbitrary normal matrices, the inclusion is established through order three. Other proofs cover certain eigenvalue multiplicities, singular sums, spectra on lines or circles, and specific normal dilations. In 2025, Shitov proved the inclusion when one matrix is Hermitian and the other has at most three nonreal eigenvalues, counted with multiplicity. ([1](#ref-1), [6](#ref-6), [11](#ref-11), [12](#ref-12), [21](#ref-21), [23](#ref-23), [24](#ref-24))

Order four exposes the difficulty. Drury showed that one set of nonnegative permutation weights cannot always represent the squared minors of the relative unitary matrix. The original conjecture allows the weights to depend on the eigenvalues. In October 2026, Zheng posted a proof claim for all order-four pairs. No refereed confirmation was located. Counterexamples reported in 2026 refute Kovačec’s proposed smaller polygon and leave the original convex-hull question open. ([9](#ref-9), [61](#ref-61), [62](#ref-62))

## The conjecture in symbols

Let $A$ and $B$ be complex normal matrices of order $n$. Write their eigenvalues as $a_1,\ldots,a_n$ and $b_1,\ldots,b_n$, counted with multiplicity. The conjecture states

$$
\det(A+B)\;\in\;\operatorname{conv}\!\left\{
  \prod_{i=1}^{n}\bigl(a_i+b_{\sigma(i)}\bigr)
  \;\middle|\; \sigma\in S_n
\right\}.
$$

Here $S_n$ is the set of all permutations of $n$ indices, and $\operatorname{conv}$ denotes the convex hull in the complex plane. Diagonal matrices attain every permutation product. Thus, if the conjecture holds, this hull is the smallest convex set that contains every attainable determinant for the two spectra.

## Results by hypothesis

For a fixed pair of spectra, the determinant range consists of all values obtained as the relative unitary eigenbasis varies. A result for a specified pair of matrices can also depend on how their eigenvectors align.

| Hypothesis or topic | Result |
| --- | --- |
| Orders 1 to 3 | Every normal pair satisfies the inclusion. In order two the attainable set is exactly the segment joining the two products. ([2](#ref-2), [6](#ref-6), [27](#ref-27)) |
| Hermitian and circular spectra | For two Hermitian matrices, the extreme permutation products give the exact real interval. More generally each spectrum can lie on its own line or circle. ([1](#ref-1), [21](#ref-21), [22](#ref-22)) |
| Repeated eigenvalues | It suffices that one matrix have at most two distinct eigenvalues, or that one eigenvalue have multiplicity at least n − 2 in one matrix. ([12](#ref-12), [14](#ref-14)) |
| Nonreal eigenvalues | If A is Hermitian, B can have up to three nonreal eigenvalues. The remaining eigenvalues of B are real. ([24](#ref-24)) |
| Singular sums or collinear products | A singular sum puts zero in the hull. If all permutation products are collinear, the inclusion also holds. The 1993 paper corrects the earlier argument for the latter result. ([11](#ref-11), [12](#ref-12)) |
| Specified eigenbases or blocks | The inclusion holds for a Householder change of eigenbasis, and for the paired block dilations constructed by Rodtes. Mulero-Martínez treats additional structured pairs. ([19](#ref-19), [23](#ref-23), [25](#ref-25)) |
| Shape of the range | The range is compact and connected. In order three it is star-shaped. In order twelve it can have a hole, so the proposed convex hull can contain unattainable points. ([28](#ref-28), [29](#ref-29), [51](#ref-51)) |
| Order-four proof claims | The October 24 public preprint uses elliptic curves and a finite case analysis. Kovačec describes an October 16 block Horn manuscript under a different author spelling and DOI. Both records are retained as cited. ([60](#ref-60), [61](#ref-61)) |

## Coverage and sources

The search used both name orders, MOC, OMC, “determinantal conjecture”, “determinantal range”, and the Portuguese title. Reference lists in the 2019 and 2025 surveys, the Auburn theses, and recent papers were checked against journal, DOI, university and preprint records. Related sources are included when they explain a proof, obstruction or direct extension. Private and unindexed material can escape this search.

Research tools include [a formal statement in Lean](<https://github.com/google-deepmind/formal-conjectures/blob/0771383387505c96d1b2f6a3d35088ad00892c5c/FormalConjectures/Wikipedia/DeterminantalConjecture.lean>) and [the OpenTorus numerical search example](<https://github.com/maximilianbehr/OpenTorus/tree/main/examples/marcus-de-oliveira>).

## Annotated bibliography

[Original papers and proved cases](#original-papers-and-proved-cases) · [Geometry](#geometry-of-the-determinant-range) · [Surveys and theses](#surveys-theses-and-historical-sources) · [Preprints and claims](#preprints-and-reported-claims) · [Related inequalities](#related-determinant-inequalities)

### Original papers and proved cases

The original question, proofs under stated hypotheses, and tests of proposed proof methods.

<a id="ref-1"></a>

#### 1. Bounds for the determinant of the sum of hermitian matrices

M. Fiedler · 1971. Proceedings of the American Mathematical Society 30, 27–31

Proves sharp lower and upper bounds for Hermitian summands. The two extreme values are permutation products and are attained.

[DOI 10.1090/S0002-9939-1971-0286814-1](<https://doi.org/10.1090/S0002-9939-1971-0286814-1>)

<a id="ref-2"></a>

#### 2. Derivations, Plücker relations, and the numerical range

M. Marcus · 1973. Indiana University Mathematics Journal 22(12), 1137–1149. Technical report AD767506, 1972

Poses the convex-hull question and verifies order two. A 1972 technical report preceded the 1973 journal article, which explains the two dates used in later citations.

[DOI 10.1512/iumj.1973.22.22094](<https://doi.org/10.1512/iumj.1973.22.22094>) · [1972 technical report](<https://ntrl.ntis.gov/NTRL/dashboard/searchResults/titleDetail/AD767506.xhtml>)

<a id="ref-3"></a>

#### 3. Normal matrices (Research problem)

G. N. de Oliveira · 1982. Linear and Multilinear Algebra 12(2), 153–154

Independently poses the normal-matrix conjecture. Records the case of a summand of rank at most one and the related trace-of-a-product inclusion.

[DOI 10.1080/03081087.1982.11882087](<https://doi.org/10.1080/03081087.1982.11882087>)

<a id="ref-4"></a>

#### 4. The determinant of the sum of two normal matrices with prescribed eigenvalues

N. Bebiano and J. F. Queiró · 1985. Linear Algebra and its Applications 71, 23–28

Proves the case in which all but one eigenvalue of either matrix coincide. Establishes that every nonzero corner of the determinantal range is a permutation product.

[DOI 10.1016/0024-3795(85)90231-9](<https://doi.org/10.1016/0024-3795(85)90231-9>)

<a id="ref-5"></a>

#### 5. Matrices satisfying a conjecture of G. N. de Oliveira on determinants

J. da Providência and N. Bebiano · 1986. Linear Algebra and its Applications 78, 187–198

Proves the conjecture when one summand is positive definite Hermitian and the other is skew-Hermitian. Also gives a transformation using shifted inverses that preserves cases of the conjecture.

[DOI 10.1016/0024-3795(86)90023-6](<https://doi.org/10.1016/0024-3795(86)90023-6>)

<a id="ref-6"></a>

#### 6. On a conjecture of G. N. de Oliveira on determinants

N. Bebiano, J. K. Merikoski and J. da Providência · 1987. Linear and Multilinear Algebra 20(2), 167–170

Proves the unrestricted conjecture in dimension three. The squared moduli of the entries of a unitary matrix give a doubly stochastic matrix, to which Birkhoff’s theorem applies.

[DOI 10.1080/03081088708817750](<https://doi.org/10.1080/03081088708817750>)

<a id="ref-7"></a>

#### 7. Some remarks on a conjecture of de Oliveira

N. Bebiano and J. da Providência · 1988. Linear Algebra and its Applications 102, 241–246

Proves the common-modulus case. When the eigenvalues of both matrices all have the same modulus, the determinants lie on a single line through the origin.

[DOI 10.1016/0024-3795(88)90327-8](<https://doi.org/10.1016/0024-3795(88)90327-8>)

<a id="ref-8"></a>

#### 8. Some notes on de Oliveira’s determinantal conjecture

J. K. Merikoski and A. Virtanen · 1989. Linear Algebra and its Applications 121, 345–352

Studies collinear permutation products and asks whether all squared minors of a unitary matrix can share a permutation decomposition. The authors corrected the proof of the collinear case in 1993.

[DOI 10.1016/0024-3795(89)90709-X](<https://doi.org/10.1016/0024-3795(89)90709-X>)

<a id="ref-9"></a>

#### 9. A counterexample to a question of Merikoski and Virtanen on the compounds of unitary matrices

S. W. Drury · 1992. Linear Algebra and its Applications 168, 251–257

Refutes the proposed common convex decomposition of squared minors in dimension four. That stronger assertion would have yielded the original conjecture.

[DOI 10.1016/0024-3795(92)90296-M](<https://doi.org/10.1016/0024-3795(92)90296-M>)

<a id="ref-10"></a>

#### 10. On symmetric functions of the eigenvalues of the sum of two Hermitian matrices

S. W. Drury · 1992. Linear Algebra and its Applications 176, 211–222

Proves a convex-hull inclusion for the entire characteristic polynomial of a Hermitian sum. A single set of nonnegative permutation weights works for all coefficients.

[DOI 10.1016/0024-3795(92)90219-Z](<https://doi.org/10.1016/0024-3795(92)90219-Z>)

<a id="ref-11"></a>

#### 11. On the determinantal conjecture of Marcus and de Oliveira

S. W. Drury and B. Cload · 1992. Linear Algebra and its Applications 177, 105–109

Proves that if the sum is singular, zero belongs to the convex hull of the permutation products in every dimension.

[DOI 10.1016/0024-3795(92)90319-6](<https://doi.org/10.1016/0024-3795(92)90319-6>)

<a id="ref-12"></a>

#### 12. Some further notes on the Marcus–de Oliveira determinantal conjecture

J. K. Merikoski and A. Virtanen · 1993. Linear Algebra and its Applications 187, 259–262

Identifies a gap in the 1989 proof of a real-part bound and shows that the unrestricted bound is equivalent to the conjecture. Supplies a valid proof for collinear permutation products and proves the case of at most two distinct eigenvalues in one summand.

[DOI 10.1016/0024-3795(93)90140-J](<https://doi.org/10.1016/0024-3795(93)90140-J>)

<a id="ref-13"></a>

#### 13. Interdependence of some problems arising in generalizing the Marcus–de Oliveira determinantal conjecture

J. K. Merikoski, A. Virtanen, N. Bebiano and J. da Providência · 1993. Portugaliae Mathematica 50(2), 227–236

Compares the implications among proposed extensions using elementary symmetric functions and compound matrices.

[University record](<https://researchportal.tuni.fi/en/publications/interdependence-of-some-problems-arising-in-generalizing-the-marc>)

<a id="ref-14"></a>

#### 14. On a conjecture of Marcus and de Oliveira

A. Kovačec · 1994. Linear Algebra and its Applications 201, 91–97

Proves the conjecture when at least n−2 eigenvalues of one summand have the same value. Equivalently, a scalar shift of that summand has rank at most two.

[DOI 10.1016/0024-3795(94)90107-4](<https://doi.org/10.1016/0024-3795(94)90107-4>)

<a id="ref-15"></a>

#### 15. The validity of the Marcus–de Oliveira conjecture for essentially Hermitian matrices

N. Bebiano, A. Kovačec and J. da Providência · 1994. Linear Algebra and its Applications 197–198, 411–427

Proves cases with spectra on parallel lines and with one spectrum positive real and the other on a line through zero. The authors use the geometry of supporting lines.

[DOI 10.1016/0024-3795(94)90498-7](<https://doi.org/10.1016/0024-3795(94)90498-7>)

<a id="ref-16"></a>

#### 16. The determinantal conjecture and Hadamard type inequalities

S. W. Drury · 1996. Linear Algebra and its Applications 246, 279–297

Uses Hadamard-type inequalities to reduce the dimension-four conjecture to a geometrical problem about the permutation products.

[DOI 10.1016/0024-3795(94)00361-0](<https://doi.org/10.1016/0024-3795(94)00361-0>)

<a id="ref-17"></a>

#### 17. The Marcus-de Oliveira conjecture, bilinear forms, and cones

A. Kovačec · 1999. Linear Algebra and its Applications 289, 243–259

Uses a cone of bilinear forms to treat a particular order-four change of eigenbasis. A proposed extension allowing two complex arguments fails. Shitov also cites this paper for the one-nonreal-eigenvalue case.

[DOI 10.1016/S0024-3795(97)10004-0](<https://doi.org/10.1016/S0024-3795(97)10004-0>)

<a id="ref-18"></a>

#### 18. The role of representation theory in the Oliveira-Marcus conjecture

A. Kovačec · 1999. Matrices and Group Representations (Coimbra, 1998), Textos de Matemática, Série B 19, University of Coimbra, from p. 111

Examines how group representation theory applies to the determinant conjecture.

[Coimbra record](<https://www.mat.uc.pt/publicacoes/B19.html>)

<a id="ref-19"></a>

#### 19. OMC for Householder reflections

S. W. Drury · 1999. Linear Algebra and its Applications 298, 159–169

Proves the conjecture when the change of eigenbasis is a Householder reflection. A stronger conjecture about minors of such reflections fails in dimension five.

[DOI 10.1016/S0024-3795(99)00173-1](<https://doi.org/10.1016/S0024-3795(99)00173-1>)

<a id="ref-20"></a>

#### 20. The external vertices conjecture in case n = 4

S. W. Drury · 2004. Electronic Journal of Linear Algebra 11, 180–191

Proves that if the permutation hull for order four excludes zero, the determinant belongs to the convex hull of all rays from each permutation product directed away from zero. This is a weaker enclosure than the original hull.

[DOI 10.13001/1081-3810.1131](<https://doi.org/10.13001/1081-3810.1131>) · [Full text](<https://www.kurims.kyoto-u.ac.jp/EMIS/journals/ELA/ela-articles/articles/vol11_pp180-191.pdf>)

<a id="ref-21"></a>

#### 21. Essentially Hermitian matrices revisited

S. W. Drury · 2006. Electronic Journal of Linear Algebra 15, 285–296

Proves the result for a Hermitian matrix and a non-real scalar multiple of a Hermitian matrix. Corollary 1.3 covers a pair of spectra that each lie on a circle, including different circles.

[DOI 10.13001/1081-3810.1239](<https://doi.org/10.13001/1081-3810.1239>) · [Full text](<https://www2.math.ethz.ch/EMIS/journals/ELA/ela-articles/articles/vol15_pp285-296.pdf>)

<a id="ref-22"></a>

#### 22. OMC for scalar multiples of unitaries

S. W. Drury · 2007. Linear Algebra and its Applications 422, 318–325

Proves the conjecture for independent scalar multiples of two unitary matrices. The two factors can have different absolute values.

[DOI 10.1016/j.laa.2006.10.022](<https://doi.org/10.1016/j.laa.2006.10.022>)

<a id="ref-23"></a>

#### 23. A class of normal dilation matrices affirming the Marcus–de Oliveira conjecture

Kijti Rodtes · 2021. Operators and Matrices 15(1), 127–130. Preprint 2020

Constructs paired normal dilations of arbitrary complex square matrices and proves the inclusion for their sum by a common block decomposition. Also proves closure of the pairwise inclusion under simultaneous direct sums.

[DOI 10.7153/oam-2021-15-09](<https://doi.org/10.7153/oam-2021-15-09>) · [arXiv 2006.14846](<https://arxiv.org/abs/2006.14846>) · [DOI 10.48550/arXiv.2006.14846](<https://doi.org/10.48550/arXiv.2006.14846>)

<a id="ref-24"></a>

#### 24. A further sufficient condition for the determinantal conjecture

Yaroslav N. Shitov · 2025. Izvestiya: Mathematics 89(4), 862–869. Russian edition 89(4), 219–226

Proves the conjecture when A is Hermitian and B is normal with at most three nonreal eigenvalues, counted with multiplicity. Uses Cauchy interlacing and Möbius transformations to extend the 1999 result with one exception.

[English DOI 10.4213/im9292e](<https://doi.org/10.4213/im9292e>) · [Russian DOI 10.4213/im9292](<https://doi.org/10.4213/im9292>)

<a id="ref-25"></a>

#### 25. A variational framework for determinantal inequalities of normal matrices: Successes and obstructions

Juan Ignacio Mulero-Martínez · 2026. Linear Algebra and its Applications 740, 19–38

Derives bounds by optimizing on the unitary group. Treats collinear spectra, circulant/skew-circulant Toeplitz pairs and tridiagonal pairs with a common reduction to essentially Hermitian blocks. Exhibits a support-functional maximizer that is not monomial.

[DOI 10.1016/j.laa.2026.03.019](<https://doi.org/10.1016/j.laa.2026.03.019>)

### Geometry of the determinant range

Results about the shape of the attainable set, its corners, and its relation to other matrix ranges.

<a id="ref-26"></a>

#### 26. Über den Wertevorrat einer Matrix

R. Kippenhahn · 1951. Mathematische Nachrichten 6, 193–228

Describes the ordinary numerical range by an algebraic curve. This gives historical context for the later study of corners and convexity of determinantal ranges.

[DOI 10.1002/mana.19510060306](<https://doi.org/10.1002/mana.19510060306>) · [English translation DOI 10.1080/03081080701553768](<https://doi.org/10.1080/03081080701553768>)

<a id="ref-27"></a>

#### 27. Some variations on the concept of the c-numerical range

N. Bebiano · 1985/86. Portugaliae Mathematica 43(1), 189–200

Studies the determinantal range as a variation of the numerical range. For normal matrices of order two the range is the segment between the two permutation products.

[Author bibliography](<https://www.mat.uc.pt/~bebiano/Publications.html>) · [Survey bibliography · reference 1](<https://doi.org/10.1007/978-3-030-11521-0_8>)

<a id="ref-28"></a>

#### 28. Some analogies between the c-numerical range and a certain variation on this concept

N. Bebiano · 1986. Linear Algebra and its Applications 81, 47–54

Gives an order-12 example in which the determinantal range has a hole. This distinguishes containment in the proposed polygon from equality with that polygon.

[DOI 10.1016/0024-3795(86)90248-X](<https://doi.org/10.1016/0024-3795(86)90248-X>)

<a id="ref-29"></a>

#### 29. On C-det spectral and C-det-convex matrices

N. Bebiano, Y.-T. Poon and J. da Providência · 1988. Linear and Multilinear Algebra 23(4), 343–351

Shows that the determinantal range of a normal pair in dimension three is star-shaped. Gives criteria for convexity in that dimension.

[DOI 10.1080/03081088808817887](<https://doi.org/10.1080/03081088808817887>)

<a id="ref-30"></a>

#### 30. On the C-determinantal range

N. Bebiano, M. E. Miranda, G. N. de Oliveira and J. da Providência · 1989. Linear Algebra and its Applications 121, 554–560, in the report of the 1987 Valencia conference

Presents the range obtained by varying the relative unitary eigenbasis in a determinant. The first link identifies the full conference report that contains this contribution.

[Conference report DOI 10.1016/0024-3795(89)90721-0](<https://doi.org/10.1016/0024-3795(89)90721-0>) · [Author bibliography](<https://www.mat.uc.pt/~bebiano/Publications.html>)

<a id="ref-31"></a>

#### 31. Some convexity theorems for the generalized numerical ranges

C.-K. Li · 1996. Linear and Multilinear Algebra 40(3), 235–240

Proves convexity for q-numerical ranges and the elliptical disk description of the C-numerical range in order two. These results support the order-two analysis of the determinantal range.

[DOI 10.1080/03081089608818441](<https://doi.org/10.1080/03081089608818441>)

<a id="ref-32"></a>

#### 32. Convex Hull Calculations: a Matlab Implementation and Correctness Proofs for the lrs-Algorithm

A. Kovačec and B. Ribeiro · 2003. Coimbra Pré-Publicações de Matemática 03-26. Posted on arXiv in 2016

Reports 82 facets of the 13-dimensional polytope with 24 vertices arising from the order-four compound-matrix approach. Section 1 gives the split into three facet classes.

[arXiv 1604.06112](<https://arxiv.org/abs/1604.06112>) · [DOI 10.48550/arXiv.1604.06112](<https://doi.org/10.48550/arXiv.1604.06112>)

<a id="ref-33"></a>

#### 33. Three observations on the determinantal range

N. Bebiano and G. Soares · 2005. Linear Algebra and its Applications 401, 211–220

Proves that the range for two arbitrary 2 × 2 matrices is an elliptical disk, possibly degenerate. Gives the line-segment criterion for normal matrices with distinct eigenvalues and characterizes linear maps that preserve the range.

[DOI 10.1016/j.laa.2004.06.006](<https://doi.org/10.1016/j.laa.2004.06.006>) · [Full text](<https://www.mat.uc.pt/preprints/ps/p0425.pdf>)

<a id="ref-34"></a>

#### 34. On the corners of certain determinantal ranges

A. Kovačec, N. Bebiano and J. da Providência · 2007. Linear Algebra and its Applications 426, 96–108

For a related range generated by real special orthogonal matrices and entrywise products, describes the local cone at a permutation product under a uniqueness condition. Transpositions determine the opening angle.

[DOI 10.1016/j.laa.2007.04.010](<https://doi.org/10.1016/j.laa.2007.04.010>) · [Full text](<https://www.mat.uc.pt/preprints/ps/p0511.pdf>)

<a id="ref-35"></a>

#### 35. Eigenvalues of the Sum of Matrices from Unitary Similarity Orbits

C.-K. Li, Y.-T. Poon and N.-S. Sze · 2008. SIAM Journal on Matrix Analysis and Applications 30, 560–581

Characterizes the eigenvalues attainable by sums over two unitary similarity orbits. Testing for the eigenvalue zero determines whether the determinant can vanish.

[DOI 10.1137/070699123](<https://doi.org/10.1137/070699123>)

<a id="ref-36"></a>

#### 36. Ranks and determinants of the sum of matrices from unitary orbits

C.-K. Li, Y.-T. Poon and N.-S. Sze · 2008. Linear and Multilinear Algebra 56, 105–130

Characterizes ranges with empty interior and the corners of the range. When A ⊕ (−B) has an eigenvalue of multiplicity at least n, the inclusion follows from the resulting rank restriction.

[DOI 10.1080/03081080701369306](<https://doi.org/10.1080/03081080701369306>) · [Full text](<https://faculty.sites.iastate.edu/ytpoon/files/inline-files/08_rank_det.pdf>)

<a id="ref-37"></a>

#### 37. Extremal case in Marcus–Oliveira conjecture and beyond

A. Guterman, R. Lemos and G. Soares · 2013. Linear and Multilinear Algebra 61, 1206–1222

Studies when the determinant range equals the entire permutation hull. Applies the results to the maximum modulus of points in the range and to maps that preserve the range or its radius.

[DOI 10.1080/03081087.2012.746327](<https://doi.org/10.1080/03081087.2012.746327>)

<a id="ref-38"></a>

#### 38. On the C-determinantal range for special classes of matrices

A. Guterman, R. Lemos and G. Soares · 2016. Applied Mathematics and Computation 275, 86–94

For Hermitian C, refines the conditions for the C-determinantal range to lie on a straight line. Also gives new results for the corresponding trace range.

[DOI 10.1016/j.amc.2015.11.042](<https://doi.org/10.1016/j.amc.2015.11.042>) · [University record](<https://hdl.handle.net/10348/7170>)

<a id="ref-39"></a>

#### 39. On the determinantal range of matrix products

A. Guterman and G. Soares · 2017/18. Zapiski Nauchnykh Seminarov POMI 463 (2017), 94–111. English translation, Journal of Mathematical Sciences 232 (2018), 805–815

Determines conditions under which interchanging two factors in a product preserves its C-determinantal range.

[DOI 10.1007/s10958-018-3910-1](<https://doi.org/10.1007/s10958-018-3910-1>) · [mathnet.ru](<https://www.mathnet.ru/eng/znsl6509>)

### Surveys, theses and historical sources

Sources for the history of the question, earlier bibliographies, and extended arguments.

<a id="ref-40"></a>

#### 40. On a conjecture concerning the determinant of the sum of two normal matrices

N. Bebiano and G. N. de Oliveira · 1985. Symposium of Operator Theory, Athens. Conference presentation

Merikoski and Virtanen identify this presentation in reference 2 and report that the proceedings omitted it. The link identifies the talk through their published paper.

[Citing paper · reference 2](<https://doi.org/10.1016/0024-3795(89)90709-X>)

<a id="ref-41"></a>

#### 41. A conjectura de Marcus-Oliveira

J. F. Queiró · 1992. Estudos de Matemática em homenagem ao Prof. Doutor Renato Pereira Coelho, Universidade de Coimbra, 101–113

Portuguese account of the conjecture and early approaches by one of the authors of the 1985 study of the determinant range.

[Full text](<https://www.mat.uc.pt/~jfqueiro/A%20conjectura%20de%20Marcus-Oliveira.pdf>) · [Coimbra record](<https://www.mat.uc.pt/~jfqueiro/publ.html>)

<a id="ref-42"></a>

#### 42. New developments on the Marcus–Oliveira conjecture

N. Bebiano · 1994. Linear Algebra and its Applications 197–198, 793–803, in the report of the Second International Linear Algebra Society Conference, Lisbon (1992)

Surveys the conjecture and partial results known at the 1992 Lisbon meeting. The links identify the meeting and the pages of the published synopsis.

[Conference account](<https://ilasic.org/wp-content/uploads/IMAGE/image10.pdf>) · [Published synopsis citation](<https://www.ams.org/books/gsm/147/gsm147-endmatter.pdf>)

<a id="ref-43"></a>

#### 43. Spectral Variation of Normal Matrices

R. Bhatia · 1997. Matrix Analysis, Graduate Texts in Mathematics 169, Springer, pp. 152–193, §VI.7

Presents Fiedler’s determinant bounds for Hermitian matrices and states the proposed extension to normal matrices on page 184.

[DOI 10.1007/978-1-4612-0653-8_6](<https://doi.org/10.1007/978-1-4612-0653-8_6>)

<a id="ref-44"></a>

#### 44. Open problems in matrix theory

X. Zhan · 2008. Proceedings of the Fourth International Congress of Chinese Mathematicians (Hangzhou, 2007), vol. I, 367–382

Section 4, Conjecture 8, reviews the Hermitian, common-modulus and singular-sum results.

[researchgate.net](<https://www.researchgate.net/publication/228687529_Open_problems_in_matrix_theory>) · [yumpu.com](<https://www.yumpu.com/en/document/view/5357583/some-open-problems-in-matrix-theory>)

<a id="ref-45"></a>

#### 45. A new series of conjectures and open questions in optimization and matrix analysis

J.-B. Hiriart-Urruty · 2009. ESAIM: Control, Optimisation and Calculus of Variations 15, 454–470

Problem 9, pp. 468–469, reviews the conjecture in difference form. It explains why commuting normal matrices give a permutation product and Hermitian matrices give a real interval.

[DOI 10.1051/cocv:2008040](<https://doi.org/10.1051/cocv:2008040>) · [Full text](<https://www.numdam.org/article/COCV_2009__15_2_454_0.pdf>)

<a id="ref-46"></a>

#### 46. The determinant of the sum of normal matrices

Denis Serre, with an answer by Suvrit · 2010. MathOverflow, question 42902, October

Serre states the problem alongside the analogous trace bound. The exchange identifies the earlier conjecture and links the known essentially Hermitian case.

[Original discussion](<https://mathoverflow.net/questions/42902/the-determinant-of-the-sum-of-normal-matrices>)

<a id="ref-47"></a>

#### 47. Linear Algebra research in Portugal

J. F. Queiró · 2011. IMAGE, Bulletin of the International Linear Algebra Society 46, 9–11

Documents the independent formulations by Marcus and de Oliveira and the research on the conjecture by Natália Bebiano at Coimbra.

[mat.uc.pt](<https://www.mat.uc.pt/~jfqueiro/IMAGE46.html>)

<a id="ref-48"></a>

#### 48. The de Oliveira Marcus Conjecture and related Investigations

A. Kovačec · 2013. The Natália Bebiano Anniversary Volume, Textos de Matemática 44, University of Coimbra, §3, from p. 7

Reviews Bebiano’s work on the conjecture, including her result with Queiró that every nonzero corner of the determinant range equals a permutation product.

[mat.uc.pt](<https://mat.uc.pt/~textos/v44/files/basic-html/page17.html>) · [mat.uc.pt](<https://www.mat.uc.pt/~textos/v44/index.html>)

<a id="ref-49"></a>

#### 49. Progress on the Marcus-de Oliveira Determinantal Conjecture

Khadejah Homadi · 2017. Master’s thesis, Auburn University, 12 April

Collects proofs by dimension and spectral restrictions. Examines equivalent formulations, related conjectures and what they imply for the determinant.

[University record](<https://hdl.handle.net/10415/5587>)

<a id="ref-50"></a>

#### 50. An interview with Graciano de Oliveira

Ana Paula Santana · 2019. CIM Bulletin 41, December, article beginning on p. 11

De Oliveira recalls how Fiedler’s theorem suggested the conjecture to him and how he later learned of Marcus’s earlier formulation.

[Full text](<https://www.cim.pt/magazines/bulletin/40/article/288/pdf>) · [cim.pt](<https://www.cim.pt/magazines/bulletin/40/280>)

<a id="ref-51"></a>

#### 51. A Survey of the Marcus–de Oliveira Conjecture

Huajun Huang · 2019. Advances in Algebra (SRAC 2017), Springer Proceedings in Mathematics & Statistics 277, 169–181

Classifies results by dimension and spectral conditions. Reviews the geometry of the range, including its boundary, corners and the conditions known to imply convexity.

[DOI 10.1007/978-3-030-11521-0_8](<https://doi.org/10.1007/978-3-030-11521-0_8>)

<a id="ref-52"></a>

#### 52. Determinants of Sums of Normal Matrices

Matthew Speck · 2024. Doctoral dissertation, Auburn University, 6 May

Uses representation theory and combinatorics to construct and modify coefficients in a linear system. Treats small orders and develops a statistical approach to the remaining problem.

[Dissertation](<https://etd.auburn.edu/handle/10415/9283>) · [2024 seminar abstracts](<https://webhome.auburn.edu/~mkb0096/Spring2024Seminar.html>)

<a id="ref-53"></a>

#### 53. Revisiting the Marcus–de Oliveira Conjecture

Natália Bebiano, João P. da Providência · 2025. Mathematics 13(5), article 711

Reviews the Hermitian, order-three, spectral-line, unitary and normal-dilation results. Explains how a 12 × 12 determinant range can have a hole and compares eigenvalue, singular-value and indefinite-inner-product questions.

[DOI 10.3390/math13050711](<https://doi.org/10.3390/math13050711>)

### Preprints and reported claims

Public manuscripts, seminar claims, and reports of privately circulated work. The two Coimbra versions have distinct entries because the main claim changed.

<a id="ref-54"></a>

#### 54. Boundary Matrices and the Marcus-de Oliveira Determinantal Conjecture

Ameet Sharma · 2018. viXra:1805.0355. First posted 20 May 2018. Final revision 18 June 2019, 12 pp.

At a regular, nonzero boundary point with a nonzero derivative matrix, the manuscript derives its Hermitian form up to phase and determines the tangent direction.

[vixra.org](<https://vixra.org/abs/1805.0355>) · [Full text](<https://vixra.org/pdf/1805.0355vG.pdf>)

<a id="ref-55"></a>

#### 55. Determinants of Sums of Normal Matrices

Luke Oeding and Matthew Speck · 2023. Seminar announcements, Auburn University, 24 January, and Georgia Institute of Technology, 30 January

The abstracts announce a general proof via a geometric description of the determinantal range. Speck’s January 2024 seminar reports an order-three proof and describes higher orders as future work. No publication establishing the 2023 general claim was located.

[Georgia Tech abstract](<https://math.gatech.edu/node/32834520>) · [Auburn 2023 abstract](<https://webhome.auburn.edu/~mkb0096/Spring2023Seminar.html>) · [Auburn 2024 follow-up](<https://webhome.auburn.edu/~mkb0096/Spring2024Seminar.html>)

<a id="ref-56"></a>

#### 56. A conjecture more precise and stronger than the one by Marcus and de Oliveira

Alexander Kovačec · 2026. DMUC Preprint 26-11, version 1, 7 April. The author replaced this version on 4 November

Conjecture 7 proposed a smaller, computable outer polygon built from transposition segments between permutation products. The author subsequently reported counterexamples in dimensions three and four.

[April catalogue record](<https://cmuc.mat.uc.pt/rdonweb/researchgroups/pppublication.do?publicationId=4888>) · [November replacement](<https://www.mat.uc.pt/preprints/ps/p2611.pdf>)

<a id="ref-57"></a>

#### 57. The strengthened Marcus–de Oliveira conjecture has a three-dimensional counterexample

Wenlin Zhang and Haobo Ma (The Omega Institute) · 2026. Trureturing research dossier and Lean formalization. Communicated to Kovačec in July

Exhibits a rational orthogonal matrix whose determinant escapes Kovačec’s proposed outer polygon. Gives explicit positive weights that place the same determinant inside the original permutation hull.

[Research dossier and proof](<https://www.trureturing.org/research/kovacec-2026-strengthened-marcus-de-oliveira/>) · [Coimbra account · p. 9](<https://www.mat.uc.pt/preprints/ps/p2611.pdf#page=9>)

<a id="ref-58"></a>

#### 58. Counterexamples to Kovačec’s polygon conjecture for the Marcus–de Oliveira region

Dev D. Goyal · 2026. Communicated manuscript, 16 pp., 28 August, recorded in Kovačec, DMUC 26-11 v2, pp. 9–10

Kovačec reports that this manuscript constructs infinitely many counterexamples to his stronger polygon claim in dimensions three and higher, including higher-dimensional examples with pairwise distinct spectra. The link leads to Kovačec’s account.

[Kovačec’s account · p. 9](<https://www.mat.uc.pt/preprints/ps/p2611.pdf#page=9>)

<a id="ref-59"></a>

#### 59. MI-05: A fourteen-term identity and a sharp orthogonal obstruction bound

Sidney Holden · 2026. Research report, OpenProblemsInNLA, 13 September

Gives a signed 14-term identity in order four and sufficient conditions for convex coefficients. One condition covers an operator-norm ball of radius 1/100 about a specified Hadamard matrix.

[Manuscript](<https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/eb7c9d64f91757a82fbe9167e80ab9c1b7f36c22/references/holden-mi05-2026-09-13/report.pdf>) · [Registry record](<https://clopen.solutions/submissions/openproblemsinnla-holden-mi05-2026-09-13-report/v1/>)

<a id="ref-60"></a>

#### 60. The n = 4 Marcus-de Oliveira conjecture via a block Horn certificate

XinFu (Denzel) Zhang · 2026. ResearchGate preprint, 31 pp., 16 October, as cited by Kovačec in DMUC 26-11 v2, pp. 9–10

Kovačec reports a claim based on a 6 × 6 compression and a block Horn certificate. His bibliography supplies the title, author spelling and DOI. No independent copy of this manuscript was located.

[Reported DOI 10.13140/RG.2.2.13229.35046](<https://doi.org/10.13140/RG.2.2.13229.35046>) · [Manuscript citation · p. 10](<https://www.mat.uc.pt/preprints/ps/p2611.pdf#page=10>)

<a id="ref-61"></a>

#### 61. The Marcus–de Oliveira conjecture for n = 4

Dongzhe (Denzel) Zheng · 2026. ResearchGate preprint, uploaded 24 October, 66 pp.

Claims a proof for all order-four normal pairs. The paper reduces squared minors to data from two real orthogonal matrices, then treats a finite list of contact cases. The author cites supplementary exact-arithmetic checks. No refereed version was located.

[DOI 10.13140/RG.2.2.36790.25923](<https://doi.org/10.13140/RG.2.2.36790.25923>) · [Author’s research page](<https://denzelzheng.com/mathematics/>)

<a id="ref-62"></a>

#### 62. A large polygonal region contained in a simply connected Marcus de Oliveira region

Alexander Kovačec · 2026. DMUC Preprint 26-11, replacement version 2, 4 November, 10 pp.

The revised Theorem 7 places a polygon inside the determinant range when its defining Jordan curve exists and the range is two-dimensional and simply connected. Section 4 gives counterexamples to the April outer bound.

[Full text](<https://www.mat.uc.pt/preprints/ps/p2611.pdf>)

### Related determinant inequalities

Selected predecessors and extensions involving singular values, matrix products, other group actions, and indefinite inner products.

<a id="ref-63"></a>

#### 63. On eigenvalues of sums of normal matrices

H. Wielandt · 1955. Pacific Journal of Mathematics 5, 633–638

Characterizes the eigenvalues attainable by sums of normal matrices with fixed spectra using separation by a line or circle. Drury and Cload used this theorem in the singular-sum case.

[DOI 10.2140/pjm.1955.5.633](<https://doi.org/10.2140/pjm.1955.5.633>) · [Full text](<https://msp.org/pjm/1955/5-4/pjm-v5-n4-p14-p.pdf>)

<a id="ref-64"></a>

#### 64. On the trace of the product and the determinant of the sum of complex matrices with prescribed singular values

M. E. F. Miranda · 1984. Linear Algebra and Applications, Vitoria-Gasteiz (1983), Universidad del País Vasco, Bilbao, 326–333

Studies the determinant when the singular values are prescribed. The reference and its bounds are discussed in the linked works.

[Bibliographic reference 6](<https://www.mat.uc.pt/preprints/ps/p1732.pdf>) · [Survey bibliography](<https://doi.org/10.1007/978-3-030-11521-0_8>)

<a id="ref-65"></a>

#### 65. On the determinant of certain strictly dissipative matrices

N. Bebiano and J. da Providência · 1986. Linear Algebra and its Applications 83, 117–128

Studies determinant estimates for matrices whose imaginary Hermitian part is positive definite. This addresses a restricted class of sums of a Hermitian and a skew-Hermitian matrix.

[DOI 10.1016/0024-3795(86)90268-5](<https://doi.org/10.1016/0024-3795(86)90268-5>) · [sciencedirect.com](<https://www.sciencedirect.com/science/article/pii/0024379586902685>) · [Coimbra record](<https://www.mat.uc.pt/~bebiano/Publications.html>)

<a id="ref-66"></a>

#### 66. Determinants of Sums

Marvin Marcus · 1990. The College Mathematics Journal 21(2), 130–135

Explains an expansion of the determinant of a matrix sum in complementary minors. This identity is part of the algebra behind the permutation-weight approach.

[DOI 10.1080/07468342.1990.11973297](<https://doi.org/10.1080/07468342.1990.11973297>) · [Full text](<https://maa.org/wp-content/uploads/2024/10/NTE59.pdf#page=46>)

<a id="ref-67"></a>

#### 67. On elementary symmetric functions of the eigenvalues of the sum and product of normal matrices

J. K. Merikoski and A. Virtanen · 1992. Czechoslovak Mathematical Journal 42(2), 193–198

Formulates convex-hull problems for elementary symmetric functions of sums and products. Proves several low-degree cases, including degrees two and three for sums.

[DOI 10.21136/CMJ.1992.128332](<https://doi.org/10.21136/CMJ.1992.128332>) · [dml.cz](<https://dml.cz/handle/10338.dmlcz/128332>)

<a id="ref-68"></a>

#### 68. A bound for the determinant of the sum of two normal matrices

J. F. Queiró and A. Kovačec · 1992/93. Linear and Multilinear Algebra 33(3–4), 171–173

Applies Hadamard’s inequality to bound the absolute determinant using both spectra. Compares its bound with Miranda’s singular-value estimate.

[DOI 10.1080/03081089308818191](<https://doi.org/10.1080/03081089308818191>)

<a id="ref-69"></a>

#### 69. On a recent determinantal inequality

N. Bebiano and M. E. Miranda · 1994. Linear Algebra and its Applications 201, 99–102

Characterizes equality in the upper bound of Queiró and Kovačec for the modulus of a determinant. This identifies additional cases in which the bound is attained by a permutation product.

[DOI 10.1016/0024-3795(94)90108-2](<https://doi.org/10.1016/0024-3795(94)90108-2>)

<a id="ref-70"></a>

#### 70. A bound for the determinant of certain Hadamard products and for the determinant of the sum of two normal matrices

S. W. Drury · 1994. Linear Algebra and its Applications 199, 329–338

Bounds determinants of entrywise products of a unitary matrix and a complex matrix. Applies the bound to the modulus of the determinant of a normal-matrix sum.

[DOI 10.1016/0024-3795(94)90356-5](<https://doi.org/10.1016/0024-3795(94)90356-5>)

<a id="ref-71"></a>

#### 71. On a theorem of Wielandt and the compounds of unitary matrices

S. W. Drury · 1994. Linear Algebra and its Applications 199, 391–412

Studies which parts of the permutation-decomposition argument survive for compound matrices. Connects this problem to Wielandt’s results on variation of normal-matrix eigenvalues.

[DOI 10.1016/0024-3795(94)90362-X](<https://doi.org/10.1016/0024-3795(94)90362-X>)

<a id="ref-72"></a>

#### 72. The determinant of the sum of two matrices

C.-K. Li and R. Mathias · 1995. Bulletin of the Australian Mathematical Society 52(3), 425–429

Gives upper and lower bounds on the absolute determinant for arbitrary complex matrices with fixed singular values. Extends the method to other scalar functions.

[DOI 10.1017/S0004972700014908](<https://doi.org/10.1017/S0004972700014908>)

<a id="ref-73"></a>

#### 73. A reverse Hadamard inequality

S. Ambikkumar and S. W. Drury · 1996. Linear Algebra and its Applications 247, 83–95

Derives a reverse Hadamard bound for entrywise products involving a special unitary matrix and a real matrix of rank at most two with entries at least one. Provides a route to related vertex inequalities.

[DOI 10.1016/0024-3795(96)89196-8](<https://doi.org/10.1016/0024-3795(96)89196-8>)

<a id="ref-74"></a>

#### 74. On the dual of a result of Miranda and Thompson

N. Bebiano and J. da Providência · 1997. Linear Algebra and its Applications 262, 119–129

Studies determinant values for the sum of real matrices with prescribed singular values when independent proper orthogonal transformations vary on the left and the right.

[DOI 10.1016/S0024-3795(97)80027-4](<https://doi.org/10.1016/S0024-3795(97)80027-4>)

<a id="ref-75"></a>

#### 75. Determinant of the Sum of a Symmetric and a Skew-Symmetric Matrix

N. Bebiano, C.-K. Li and J. da Providência · 1997. SIAM Journal on Matrix Analysis and Applications 18, 74–82

Determines the possible determinants from the singular values of the symmetric and skew-symmetric parts. This gives an exact containment region for a different prescribed-data problem.

[DOI 10.1137/S0895479895293429](<https://doi.org/10.1137/S0895479895293429>)

<a id="ref-76"></a>

#### 76. Extremal matrices in certain determinantal inequalities

N. Bebiano and C. Perdigão · 1998. Linear and Multilinear Algebra 44, 261–276

Studies equality in determinant bounds. Under independent left and right unitary factors it determines the extreme absolute values of the determinant of a sum with prescribed singular values.

[DOI 10.1080/03081089808818562](<https://doi.org/10.1080/03081089808818562>)

<a id="ref-77"></a>

#### 77. On Generalized Numerical Ranges of Operators on an Indefinite Inner Product Space

N. Bebiano, R. Lemos, J. da Providência and G. Soares · 2004. Linear and Multilinear Algebra 52, 203–233

Studies a related determinantal range for an indefinite inner product. In dimension two the authors describe its boundary using a possibly degenerate hyperbola.

[DOI 10.1080/0308108031000134981](<https://doi.org/10.1080/0308108031000134981>) · [University record](<https://hdl.handle.net/10316/11439>)

<a id="ref-78"></a>

#### 78. An extension of Birkhoff’s theorem with an application to determinants

N. Bebiano, J. da Providência and A. Kovačec · 2007. Linear Algebra and its Applications 427, 130–137

Extends Birkhoff’s theorem to J-doubly stochastic matrices and applies it to determinants for an indefinite inner product.

[DOI 10.1016/j.laa.2007.06.025](<https://doi.org/10.1016/j.laa.2007.06.025>)

<a id="ref-79"></a>

#### 79. Determinant and Pfaffian of sum of skew symmetric matrices

T.-Y. Tam and M. C. Thompson · 2010. Linear Algebra and its Applications 433, 412–423

Determines the determinant range for real skew-symmetric pairs under orthogonal and special orthogonal similarity. Also treats Pfaffians and complex matrices.

[DOI 10.1016/j.laa.2010.03.007](<https://doi.org/10.1016/j.laa.2010.03.007>) · [Full text](<https://webhome.auburn.edu/~tamtiny/Pfaffian21.pdf>)

<a id="ref-80"></a>

#### 80. Determinants of sum of orbits under compact Lie group

T.-Y. Tam and M. C. Thompson · 2012. Linear Algebra and its Applications 436, 1644–1650

Extends the Hermitian orbit problem to Lie algebras of compact connected subgroups of the unitary group. Gives the determinant extrema for the symplectic group.

[DOI 10.1016/j.laa.2011.06.020](<https://doi.org/10.1016/j.laa.2011.06.020>) · [Full text](<https://webhome.auburn.edu/~tamtiny/Det12.pdf>)

<a id="ref-81"></a>

#### 81. Determinants of sums of two real matrices and their extensions

T.-Y. Tam and M. C. Thompson · 2012. Linear and Multilinear Algebra 60, 1409–1431

Determines the extreme determinants for two real matrices under independent special orthogonal left and right actions. Extends these results to real classical simple Lie algebras.

[DOI 10.1080/03081087.2012.728215](<https://doi.org/10.1080/03081087.2012.728215>)

<a id="ref-82"></a>

#### 82. A Fiedler-type theorem for the determinant of J-positive matrices

N. Bebiano and J. da Providência · 2016. Mathematical Inequalities & Applications 19, 663–669

Determines the values attained by the determinant of the sum of two J-positive matrices with prescribed spectra under a compatibility condition in an indefinite inner product space.

[DOI 10.7153/mia-19-47](<https://doi.org/10.7153/mia-19-47>) · [Full text](<https://files.ele-math.com/articles/mia-19-47.pdf>)

<a id="ref-83"></a>

#### 83. Determinantal inequalities for J-accretive dissipative matrices

Natália Bebiano, João da Providência · 2017. Studia Universitatis Babeș-Bolyai Mathematica 62(1), 119–125

Gives bounds for the determinant of a sum with prescribed spectra in the indefinite-inner-product setting of J-accretive dissipative matrices.

[DOI 10.24193/subbmath.2017.0009](<https://doi.org/10.24193/subbmath.2017.0009>) · [Full text](<https://www.mat.uc.pt/preprints/ps/p1620.pdf>)
