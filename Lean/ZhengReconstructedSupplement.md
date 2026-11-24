# Reconstructed supplementary contact certificates

Independent reconstruction of seven exceptional contact cases in Denzel
Zheng, *The Marcus–de Oliveira conjecture for n = 4* (2026), Proposition
4.3 and Appendix E. This is not the author's missing supplement.

**Status:** complete mathematical arguments for T1, T18, T19, T20,
T21, T22, T23, with exact, independently executable certificate checks.
The remaining 83 exceptional cases are NOT certified here. No new Lean
axiom or unchecked declaration is introduced.

Run from the repository root:

    python Lean/research/zheng_contact_audit.py
    python Lean/research/zheng_algebra_audit.py
    python Lean/research/zheng_reconstructed_cases.py

The first two programs verify the common facet classification and
matching-cubic algebra. The last program reconstructs the specific
contact certificates independently, using four CPU worker processes.
Its checks use only integer/rational arithmetic; SymPy is required.
Do not use Python's -O flag, which disables assertions.

## 1. Setting and common inputs

Use the author's permutation and facet indices (Appendices D and E),
and the 14-dimensional matching-coordinate space with its injective
linear map \(P\) to the 24 permutation values. Write \(p_\sigma =
\eta\prod_i(a_i+b_{\sigma(i)})\), with the arbitrary support multiplier
\(\eta\ne0\) absorbed by common spectral scaling if desired. Use the
minimum-support convention:
\[
h=\min_\sigma\Re p_\sigma,\qquad g_\sigma=\Re p_\sigma-h\ge0.
\]
A contact is a permutation label with \(g_\sigma=0\).
Write \(x\) for the matching coordinate vector of the scaled spectra,
\(\kappa\) for the constant-profile direction, and \(c=\Re x-h\kappa\).
Thus \(Pc=g\).

Let \(f_0,\ldots,f_{81}\) be the facets in Appendix D, with nonnegative
permutation values. The 34 minor facets give nonnegative evaluations
at every relative unitary: their evaluations are squared moduli of
minors. The other 48 are the mixed facets. The exact facet audit
establishes completeness of this list. The standard normal-cone
decomposition gives
\[
c=\sum_{j\in A(T)}t_j f_j,\qquad
A(T)=\{j:(Pf_j)_\sigma=0\ \text{for all }\sigma\in T\},\qquad t_j\ge0.
\tag{1}
\]
A representation with only minor facets proves the support inequality
for every complex unitary, by the signed subset-minor law. Thus these
seven proofs do not require the orthogonal realification theorem.

The repeated-spectrum and opposite-eigenvalue-pair cases are already
proved in the project, in MOC/TwoExceptions.lean and
MOC/FourCoincidence.lean. We can assume the eight marked complex
points \(a_i,-b_j\) are distinct. Every cross-sum is then nonzero.
Two matching products differing by one transposition are distinct,
by the two-factor difference identity.

## 2. Exact contact closure at zero height

Two rules suffice for all seven cases.

### 2.1 Disjoint-swap rectangles

Let \(z_{00},z_{01},z_{10},z_{11}\) be matching products obtained
from a base permutation by two disjoint transpositions. They factor
as \(x_i y_j\), up to the common support multiplier. Hence
\(z_{00}z_{11}=z_{01}z_{10}\).

If all four are contacts at height \(h\ne0\), write
\(z_{ij}=h+i v_{ij}\). The imaginary and real parts of the product
identity imply that the two opposite pairs of real numbers \(v_{ij}\)
have the same sum and the same product, respectively. Consequently
the two unordered pairs are equal, and at least one pair of
transposition-adjacent matching products is equal. This contradicts
the regularity assumption. A full rectangle of contacts therefore
forces \(h=0\).

If \(h=0\), any three contacts in a rectangle force the fourth:
the known products are nonzero purely imaginary numbers, and the
multiplicative identity expresses the fourth as a quotient of a
product of two such numbers by a third. The result is purely imaginary.

### 2.2 Three-label permutation fibers

Fix one assignment of a row to a column. The remaining six
permutations form a three-label fiber, divided into three even and
three odd permutations. Their complex matching products have equal
sums on the two parity classes, by the vanishing three-by-three
minor of the additive kernel, and equal products, because each
of the nine remaining kernel entries occurs once on each side.

If all six are contacts at a nonzero height, write each as \(h+i v\).
Equality of the sums and products implies equality of the three
elementary symmetric functions of the imaginary parts: the sum
comes from the sum identity, the pair sum from the real part of
the product divided by \(h\ne0\), and the triple product from the
imaginary part of the product. The two multisets are equal. But
every even and odd permutation in a three-label fiber differ by
a transposition, so their matching products cannot agree.
Thus a full fiber of contacts forces \(h=0\).

At zero height, two even and two odd contacts force the remaining
two. Write the known values as \(i a,i b\) and \(i d,i e\); write
the unknown even and odd values as \(z,w\).
The sum identity gives \(\Re z=\Re w=r\), and the product identity
gives \(ab z=de w\). If \(r\ne0\), then \(ab=de\), hence \(z=w\)
because all products are nonzero. This contradicts the
transposition difference identity. Thus \(r=0\).

The program enumerates all 18 rectangles and 16 fibers. Each input
contact set contains either a full rectangle or a full fiber, so
the height is zero. Iterating the two zero-height rules terminates
after finitely many additional contacts. The result is denoted by
\(T^+\).

## 3. The real matching cubic vanishes

Let \(C\) be the cubic in the author's (A.2). The independently
checked polynomial identities in research/zheng_algebra_audit.py
give \(\nabla C(x)=0\) for every complex matching point \(x\).
Write \(x=u+iv\) with real \(u,v\). Since \(C\) is a real homogeneous
cubic, separating real and imaginary parts gives
\[
\nabla C(u)=\nabla C(v),\qquad H_C(u)v=0.
\]
Symmetry of the polarized cubic gives
\(u^T\nabla C(v)=\tfrac12v^T H_C(u)v\).
Euler's homogeneous identity therefore gives
\[
3C(u)=u^T\nabla C(u)=u^T\nabla C(v)=0.
\]
At zero height \(c=u\), so \(C(c)=0\).
This necessary spectral condition is the only nonlinear identity
needed for the seven reconstructed cases.

## 4. Uniform nonminor elimination certificate

For each \(T^+\), take a representation (1) minimizing the total
mixed coefficient
\[
M=\sum_{j\text{ mixed}}t_j.
\]
Such a minimum exists: all 82 profiles are nonnegative, each has
at least one positive permutation coordinate, and the sum of
the 24 coordinates of the fixed gap profile bounds the sum of
the nonnegative coefficients. The feasible set is closed and
bounded in finite dimension.

A replacement identity
\[
f_i+f_j=\sum_{k\in R_{ij}}f_k
\tag{2}
\]
with a mixed facet on the left and only minor facets on the right
implies that \(t_i,t_j\) cannot both be positive in a minimizing
representation. Otherwise subtract \(\min(t_i,t_j)>0\) times
the left side and add that amount of the right side. This leaves
the vector and all coefficients valid but strictly reduces \(M\).

For a given case, the exact list of replacements (2) is encoded
in the dictionary R of research/zheng_reconstructed_cases.py.
They are verified by summing the 24 integer permutation profiles;
injectivity of P makes these genuine coordinate-vector identities.
Repetition in a right side denotes multiplicity.

The remaining possible supports of a mixed-positive minimum are
subsets of the maximal subsets of \(A(T^+)\) avoiding every forbidden
pair (2). The program enumerates them exhaustively by bit masks.
For each maximal subset \(S\) containing a mixed facet it verifies
that a sign \(e\in\{1,-1\}\) exists with:

* all coefficients of \(e C(\sum_{j\in S}t_j f_j)\) nonnegative;
* the coefficient of \(t_j^3\) strictly positive for every mixed
  facet \(j\in S\).

The verification needs no symbolic inequality solver. For a cubic,
the integer polarization
\[
\begin{aligned}
\mathcal B(a,b,c)={}&C(a+b+c)-C(a+b)-C(a+c)-C(b+c)\\
                  &+C(a)+C(b)+C(c)
\end{aligned}
\]
is six times its symmetric trilinear form. The signs of these
values on all triples of generators, including repetitions,
give exactly the signs of the coefficients in the displayed
cubic, up to positive multiplicities. The pure coefficients are
checked directly as \(C(f_j)\).

If the minimum representation contained a positive mixed
coefficient, its support would be contained in a verified maximal
set \(S\), and \(eC(c)>0\) would follow from the nonnegative
coefficient check and the strictly positive pure term.
This contradicts Section 3. Thus \(M=0\), and the gap admits a
minor decomposition, establishing its nonnegativity for all
relative unitaries. QED.

## 5. Reconstructed cases

| Case | Contact closure \(T^+\) | Active facets | Maximal mixed supports checked |
| --- | --- | ---: | ---: |
| T1 | 0,1,2,3,4,5,6,7 | 9 | 0 |
| T18 | 0,1,3,6,7,8 | 12 | 2 |
| T19 | 0,1,4,6,7,8 | 12 | 2 |
| T20 | 0,1,5,6,7,8 | 11 | 2 |
| T21 | 0,3,5,9,11,12 | 10 | 1 |
| T22 | 2,3,4,8,10,12,13 | 10 | 2 |
| T23 | 2,3,5,9,11,12,13 | 10 | 2 |

T1 is minor-only after closure. The other six use the uniform
nonminor-elimination argument.

For illustration, T21 has mixed facet 40 only. The two replacement
identities
\[
f_1+f_{40}=f_0+f_7+f_{39},\qquad
f_9+f_{40}=f_2+f_7+f_{41}
\]
leave the only mixed-positive maximal support
\(\{0,2,7,12,29,39,40,41\}\). With coefficient names
\(q,a,b,c,e,f,d,h'\) in that order, substitution gives
\[
C=(f+d+h')[(b+d)(q+a+d)+c(a+d)]
+e[(q+a+c+d)(f+d)+ac].
\]
Every term is nonnegative and the first includes \(d^3\).
Hence \(d>0\) is impossible. This agrees with the previously
formalized restricted cubic identity in MOC/FourContactCertificate.lean.

The new certificate also proves T22 and T23 without using any
of the unavailable supplementary arguments. The exact Python
checker prints all active and maximal support lists. All seven
checks were executed successfully using parallel CPU workers.

## 6. Exact obstruction to a tempting simplification of the curve cases

A natural attempt to extend the single-coincidence pole bound in
Zheng's Corollary B.3 is to ask for one probability law that
works on two disjoint coincidence hypersurfaces. This is false
in order four.

Let \(z_0,\ldots,z_7\) be the eight marked points (first spectrum
and negated second spectrum) in the zero-based convention.
Consider the two disjoint conditions \(z_0=z_1\) and \(z_2=z_4\).
They mean respectively an equality within the first spectrum
and an opposite eigenvalue pair. Suppose one nonnegative
probability law on permutations represented the determinant
for every spectral pair satisfying either condition.

In the matching-coordinate space the span \(W\) of these two
families is the span of the coefficient vectors of the fourteen
basis polynomials restricted to either equality. This follows
because a linear functional vanishes on all evaluations of a
polynomial map if and only if all of its polynomial coefficients
vanish. The exact checker computes
\[
\dim W=12,\qquad f_{76}\in W.
\]
For an explicit certificate, the annihilator of \(W\) is spanned
by the two linear forms \(m_0+m_2\), \(m_1+m_3\);
the mixed facet \(f_{76}=h_{1234,-}\) has coordinates
\[
(0,1,0,-1,1,-1,0,0,1,1,0,-1,0,0).
\]
These facts are verified by rational row reduction of the
restricted polynomials in the checker.

Use the real orthogonal matrix
\[
O_*=\frac17\begin{pmatrix}
1&4&4&4\\-4&1&4&-4\\-4&-4&1&4\\-4&4&-4&1
\end{pmatrix}.
\]
Its signed weights give
\(\Phi_{f_{76}}(O_*)=-158/2401<0\), while every permutation
value of \(f_{76}\) is nonnegative. Both statements are checked
exactly by the program.

If one probability law worked on the union of the two coincidence
families, linearity would make its functional agree with the
determinant functional on their linear span \(W\), in particular
on \(f_{76}\). That would give a nonnegative value there,
contradicting the displayed negative value. Thus no such law
exists for this \(O_*\). The example does not refute MOC for any
specific pair of spectra: it refutes only the stronger uniform
law across the two families.

Consequently a divisibility argument which assumes one law
valid separately at both factors of a vanishing denominator
cannot be used as a general proof of the remaining curve cases.
The single-factor bound remains valid. Further analysis of
higher-order simultaneous collisions, or another boundedness
argument, is needed.

## 7. Limits and next proof dependency

The seven cases above are independent replacements for their
missing supplementary proofs. The ordinary 124 minor-only
classes were already covered by the independently audited
facet/normal-cone argument. That yields 131 of the 214
six-contact symmetry classes through these two methods.
The 83 other exceptional cases remain to be proved or
independently certified; T85 is present in the main PDF but uses
unverified predecessor cases.

The parallel scan across all 90 cases tested additional
coefficient-sign certificates. It established no additional
six-contact case by this specific method. A failure of a
certificate search is not a counterexample to the theorem.
Neither the missing proofs nor the full order-four theorem
have been declared verified. The existing order-five contact
reduction continues to be independent of this status.
