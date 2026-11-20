# Two freely varying eigenvalues and a finite support test

Fix two triples of real numbers \(a_1,a_2,a_3\) and \(b_1,b_2,b_3\).
Adjoin independent complex fourth entries \(x,y\). Each permutation
product has the form \(c_0+c_1x+c_2y+c_3xy\) with real coefficient
vector \(c_\pi\). Write \(d\) for the corresponding coefficient vector
of the determinant with a fixed unitary eigenbasis. This vector is real
because the determinant is real for real \(x,y\).

**Proposition.** MOC holds for all complex \(x,y\) at those fixed data
if and only if \(d\in\operatorname{conv}_{\mathbb R}\{c_\pi\}\).
In particular, when feasible a single probability law works for both
free complex eigenvalues simultaneously.

A convex representation of the coefficients gives one for every
evaluation. Conversely a support test with phase \(\eta\) tests the
four coefficients with a real functional of the form
\(\Re(\eta,\eta x,\eta y,\eta xy)\).
Every functional proportional by a positive factor to \((1,u,v,w)\)
arises this way: put \(\eta=1,\ x=u+i,\ y=v+i(uv-w)\). Taking
\(\eta=-1\) gives all functionals with negative first component after
rescaling. Functionals with zero first component follow by continuity.
Separation proves the claim. This gives a four-real-dimensional hull test
for the six-real-point subfamily of the spectral problem, including
cases with both fourth entries off the real line.

## A computation for all relative eigenbases

For fixed real triples the 24 vertices can be computed exactly by
evaluating each permutation product at \((x,y)=(0,0),(1,0),(0,1),(1,1)\)
and taking differences. A facet functional \(h=(h_0,h_1,h_2,h_3)\)
with \(h_0h_3=h_1h_2\) is a real rank-one test and follows from the
one-sided real spectrum theorem. Indeed such functionals are real
multiples or limits of \((1,x,y,xy)\) with real \(x,y\).

For a higher-rank facet, let \(f(\pi)\) be its nonnegative slack on
each permutation. For \(t\in\{-3,-2,-1,0,1,2,3,4,5,6\}\) put
\(b(t)=(0,1,2,t)\). Use the linear space of functions on permutations
spanned by all singleton indicators and
\(b(t)_{\pi(i)}b(t)_{\pi(j)}\) for \(i<j\). Include its transpose
version obtained by replacing \(\pi\) with \(\pi^{-1}\).
A nonnegative function in any one such space has nonnegative physical
evaluation for arbitrary unitary eigenbasis by the one-sided coefficient
theorem, which supplies a law matching those singleton and weighted pair
moments. More explicitly the physical evaluation is given by the signed
determinant expansion
\(\sum_\pi (\operatorname{sgn}(\pi)\prod_i W_{i,\pi(i)}/\det W) f(\pi)\).
It matches the squared-minor marginals by the determinant cofactor identities.
This same linear evaluation applies to all the spaces, so a positive
decomposition of \(f\) into such functions would certify its facet.
[One-sided theorem](../MOC_progress.tex)

The exploratory linear program sought such decompositions for each
higher-rank facet. Qhull supplied candidate facets, with candidate
hyperplanes recomputed by rational nullspace calculations. HiGHS
tested feasibility in floating point. The recorded outcomes were:

| Fixed triples | Higher-rank facets where the solver failed to return a decomposition |
| --- | ---: |
| \((0,1,2),(1,2,3)\) | 0 |
| \((0,1,2),(2,4,7)\) | 0 |
| \((-1,0,1),(2,3,4)\) | 0 |
| \((-1,0,1),(3,6,7)\) | 1 |

The first template had 36 candidate facets including 17 rank-one
normals. The last template left the supporting slack with coefficients
\((-4,3,-3,0)\) and constant zero uncertified. Reproduction requires
NumPy, SciPy and SymPy. No rational feasibility certificates or exact
facet-completeness proof were obtained for these templates. Thus even
the first three all-eigenbasis inclusions remain candidate applications.
Failure of the restricted decomposition for a facet does not supply a
relative unitary violating MOC.
[Experiment](../../Code/probe_two_free_hull.py)
