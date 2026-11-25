# Two rich pivot fibres sharing a row or column

**Status.** Paper proof, not Lean-checked. This closes a subclass of the
dense stationary route, not all profiles with seven contacts. In fact no
stationarity is needed here. The only imported result not identified as
Lean-checked is the one-generalized-circle theorem in [Zheng, Theorem
C.1, preprint DOI 10.13140/RG.2.2.36790.25923](https://doi.org/10.13140/RG.2.2.36790.25923).

## Statement and conventions

For order four, suppose that in a common support direction there are two
distinct cells in the same row or column such that each of their
permutation fibres contains exactly four contacts. Then the determinant
support inequality holds for every unitary mixer. On the real stationary
route, at least four contacts suffice in this pair of fibres, since a
full fibre excludes a strict stationary violation directly.

Use signed spectral marks \(a_r,c_s=-b_s\), matching products
\(P_\sigma=\prod_r(a_r-c_{\sigma(r)})\), height
\(H=\max_\sigma \Re(\eta P_\sigma)\) and gaps
\(G_\sigma=H-\Re(\eta P_\sigma)\). Contacts are permutations with gap zero.
The fibre of \((i,j)\) consists of the six permutations with
\(\sigma(i)=j\). We can suppose \(\eta\ne0\) and all eight signed marks
are distinct: a within-spectrum repetition or a zero cross factor is
covered by the checked order-four results in
[TwoExceptions.lean](MOC/TwoExceptions.lean) and
[FourCoincidence.lean](MOC/FourCoincidence.lean).
It suffices to treat two cells in the same row, since swapping the spectra
and inverting permutations gives the column case and changes the mixer
to its adjoint.

The subset-image indicator \(1_{\sigma(I)=J}\) evaluates on a mixer to
the squared modulus of its \((I,J)\) minor, in the row-to-column assignment
convention. Thus any gap that is a nonnegative sum of these indicators
satisfies the determinant bound, by the [Merikoski–Virtanen identity,
DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X)
(the relevant evaluation is checked in
[TwoValues.lean](MOC/TwoValues.lean)).
The full gap function belongs to the real linear span of those indicators:
expand each matching product by deciding at each row which spectral
summand to take.

Common projective changes of chart preserve the gap function after
rescaling the direction. In homogeneous coordinates, every bracket
changes by the determinant of the common projective map and by two
nonzero mark normalizations. A matching uses every mark exactly once,
so the resulting factor is the same for every matching. A column at
infinity can be represented by the bracket \(1\) in all of its factors,
absorbing its common sign into the direction. All minor evaluations are
linear in the gap profile, so a certificate in this chart applies to
the original finite spectra. See the finite chart transport in
[ProjectiveTransport.lean](MOC/ProjectiveTransport.lean).

## One rich fibre forces a two-circle configuration

In a fixed fibre the product for the remaining three rows expands in the
span of constant and singleton assignment indicators. Consequently the
sum of the three gaps on even residual permutations equals the odd
sum: each residual singleton occurs once in each parity. If at least
five gaps are zero, all six are zero. Such a fibre closes at a stationary
point by (4) of
[StationaryPivotReduction.md](StationaryPivotReduction.md);
for the present statement **assume exactly four contacts in each
of the selected fibres**. The proof below does not claim the unrestricted
all-unitary statement with one or both selected fibres full.

The two positive gaps in an exactly four-contact fibre have equal value
and opposite parity. Their relative permutation is therefore a
transposition in \(S_3\), and they share a single residual edge,
called the secondary edge \((r_*,s_*)\). The gap on this fibre is a
positive constant times its indicator.

An exactly four-contact fibre cannot have \(H=0\). The products of the
three matching products in each parity are equal, since each factor
appears once in each parity. The four active rotated products
\(\eta P_\sigma\) are nonzero and purely imaginary. Thus the ratio of
the two inactive products is real. They have the same nonzero real
part by equality of gaps, so they are equal. But their transposition
difference is nonzero for distinct marks and nonzero pair factors.

For fixed pivot \((i,j)\), the three residual \(a\)'s and three
residual \(c\)'s satisfy these two circle statements:
* the residual \(a\)'s and \(c_{s_*}\) lie on a generalized circle
  \(C_A\);
* the residual \(c\)'s and \(a_{r_*}\) lie on a generalized circle
  \(C_B\).

To see the second, fix the two residual rows \(r,t\) other than
\(r_*\). For any two different residual columns \(s,v\), match
\(r,t\) to \(s,v\) in either order and leave \(r_*\) assigned to
the third column \(w\). Swapping \(r,t\) leaves the corresponding
secondary-edge indicator unchanged. The score difference therefore
vanishes, giving
\[
 \Re\bigl(\eta(a_i-c_j)(a_r-a_t)(c_s-c_v)(a_{r_*}-c_w)\bigr)=0
\]
up to an irrelevant sign. Divide out the common product
\(\prod_{s\ne j}(a_{r_*}-c_s)\) inside the nonzero prefactor and
rewrite \((c_s-c_v)/((a_{r_*}-c_s)(a_{r_*}-c_v))\) as the difference
of the two reciprocals. All differences of the three reciprocals
therefore lie on a single real line in \(\mathbb C\). Inverting gives
\(C_B\), including \(a_{r_*}\) as the preimage of infinity. The other
circle statement follows by transposition. The two circles cannot
coincide: putting their common circle on the real axis makes all core
products real, and comparing two distinct active products differing
by a transposition forces the real part of the common prefactor to be
zero, hence \(H=0\).

## Two rich fibres in one row

For two pivots \((i,j_1),(i,j_2)\), their circles \(C_A\) coincide
because they contain the same three residual row marks. If their
secondary columns \(s_1,s_2\) are distinct, either
\(s_1=j_2,\ s_2=j_1\), or one of the two residual column triples
contains both \(c_{s_1},c_{s_2}\). In the latter case its \(C_B\) and
the common \(C_A\) meet at those two column marks and its secondary
row mark, forcing coincidence. Thus only the following cases remain.

### Reciprocal secondary columns

Map the common \(C_A\) to the real line with \(c_{j_1}=\infty\) and
\(c_{j_2}=0\). Write \(z,w\) for the other columns, \(\xi=a_i\), and
let \(t_1\ne0\) be the secondary row mark for pivot \(j_1\).
The two remaining row marks \(A,B\) are also real and distinct.
In the fibre at \(j_1\), assign \(t_1\) to \(z\), and swap the
assignments of \(A,B\) to \(0,w\). Both permutations are contacts,
so their difference gives \(\Re[\eta(t_1-z)w]=0\). Assigning \(t_1\)
to \(w\) instead gives \(\Re[\eta(t_1-w)z]=0\).
Subtracting and dividing by \(t_1\) gives \(\Re[\eta(w-z)]=0\).

In the fibre at \(j_2\) the two contacts differing by an analogous
swap after assigning its secondary row to \(z\), and the two after
assigning it to \(w\), give
\(\Re[\eta\xi(t_2-z)]=\Re[\eta\xi(t_2-w)]=0\):
the other two rows are swapped between infinity and the remaining
finite column. Subtracting gives \(\Re[\eta\xi(w-z)]=0\).
Since \(\eta(w-z)\) is nonzero purely imaginary, \(\xi\) is real. The
entire row spectrum is circular; apply the cited one-circle theorem.

### Common secondary column

Map the common secondary column to infinity and \(C_A\) to the real
line. Label the other columns \(1,2,3\) with marks \(c_j\), taking the
two rich pivots as 1 and 2. Let \(y_j=\Im c_j\), \(\xi=a_i\) and
\(T_j=\eta(\xi-c_j)\). For cyclic triples \((j,k,l)\) of \((1,2,3)\)
put \(d_j=c_l-c_k\). For \(j=1,2\), the line \(c_k c_l\) meets
the real line at the secondary row mark \(t_j\); none of the three
\(y_j\) can vanish, since a real \(c_k\) on this line would force
coincidence with \(C_A\) or the distinct mark \(t_j\). These two
lines cannot be horizontal.

For \(j=1,2\), comparing the contacts in which the secondary row
takes \(c_k\) or \(c_l\) gives \(\Re(T_jd_j)=0\) as above. Write
\(T_jd_j=i b_j\). The intersection parameter is
\(t_j=c_k+\rho_j d_j\), with \(\rho_j=-y_k/(y_l-y_k)\).
Thus the active score is
\[
 H=\Re[T_j(t_j-c_k)(t_j-c_l)]
   =-b_j\,y_k y_l/(y_l-y_k),
 \qquad b_j=-H(1/y_k-1/y_l).
\]
The active score equals this expression because changing any real
row mark other than \(t_j\) to \(t_j\) changes only a term with
zero real projection. Since \(\sum_j T_j d_j=0\) by direct cyclic
cancellation, both identities for \(T_j d_j\) propagate to \(j=3\).
If \(y_1=y_2\), this gives \(T_3 d_3=0\), impossible by distinct
marks. Hence the third line also meets the real axis at a real
point \(t_3\), and the same expression there has score \(H\).
For all three \(j\), if a residual row \(k\) takes the infinity
column, expanding the other two products around \(t_j\) gives
the exact fibre gap
\[
 g_{jk}=-\Re(T_j)\prod_{r\ne i,k}(a_r-t_j)\ge0 .
\]
Here \(k\) denotes a row, not the cyclic column label above. This
uses that both \(T_j(t_j-c_l)\) and \(T_j(t_j-c_k)\) have zero real part.

If \(t_1=t_2\), the two lines coincide because they share \(c_3\)
and the real intersection. All columns are then on a generalized
circle, so the one-circle theorem applies. Otherwise let \(k_1,k_2\)
be the distinct residual rows with marks \(t_1,t_2\). Then the only
positive coefficient of \(g_{j,-}\) for \(j=1,2\) is \(g_{j,k_j}\).

It remains to combine all fibres. Write \(J_0\) for the infinity
column and use the subset-image markers
\[
 E_{jk}=1_{\sigma(\{i,k\})=\{j,J_0\}},\qquad
 R=G-\sum_{j=1}^3\sum_{k\ne i}g_{jk}E_{jk}.
\]
By the fibre formula, \(R\) vanishes off \(\sigma(i)=J_0\), and it
belongs to the span of subset-image markers. Any such function is
constant on this fibre. Indeed \(\operatorname{sgn}(\sigma)
1_{\sigma(q)=r}\) is orthogonal to each subset-image marker in the
unweighted sum on the symmetric group: compose on the right with
a transposition fixing \(q\) and swapping two labels either both in
or both outside the marker's source set. Such a transposition exists
in order four, since deleting \(q\) leaves three labels in two parts.
For any second edge \((q,r)\) with \(q\ne i,r\ne J_0\), this
orthogonality for \(R\) equates its two values in the intersection
fibre (the two permutations have opposite signs). These intersections
connect the \(S_3\) fibre by transpositions. Write the constant as \(\tau\).

Put \(m=\min_{k\ne i} g_{3k}\) and choose a row \(k\) attaining it.
In the fibre at \(J_0\), assign \(k\) to \(3\) and assign the two
remaining rows to \(1,2\), avoiding \(k_1\to1\) and \(k_2\to2\).
This is possible: the forbidden rows are distinct, so if both are
present, send the first to column 2 and the second to column 1; otherwise
avoid the sole forbidden assignment.
The resulting gap is \(\tau+m\), therefore \(\tau+m\ge0\).
Subtract \(m\) from each of the three \(g_{3k}\) and use
\[
 \sum_{k\ne i} E_{3k}=1_{\sigma(i)=3}+1_{\sigma(i)=J_0}.
\]
The resulting gap is a nonnegative sum of subset-image markers,
with the last two singleton coefficients \(m,\tau+m\). This proves
the desired all-unitary comparison for the exactly-four pair.

For a stationary strict witness, a full fibre is already impossible
by (4). Thus all cases of two fibres sharing a row or column with at
least four contacts are excluded on the stationary route. In contrast,
seven supporting labels do not by counting alone yield a rich fibre;
the general dense stationary route remains open.
