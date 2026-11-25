# T1 without a facet list

The six labels of $T_1$ are $0,1,2,3,6,7$ in the row-to-column
convention of [Zheng, Appendix E](https://doi.org/10.13140/RG.2.2.36790.25923).
This note proves the support inequality for the entire $T_1$ pattern
without any cone classification, facet checks, or tests on mixers.
The method also covers arbitrary real spectators at zero height,
without sign assumptions.

## The common circle

Use signed spectra $a_i,c_j=-b_j$, with matching products
$P_\sigma=\prod_i(a_i-c_{\sigma(i)})$. We may assume the spectra are
simple and disjoint: a repeated eigenvalue or a vanishing cross factor
has an existing order-four common-law certificate
([repeated eigenvalue](MOC/TwoExceptions.lean),
[coincident cross pair](MOC/FourCoincidence.lean)).
Projection means $\operatorname{Re}(\eta P)$ for a fixed direction $\eta\ne0$.

The contacts $0,1,6,7$ are a disjoint-swap rectangle and
$P_0P_7=P_1P_6$. Write $\eta P_i=H+i y_i$ at the four contacts.
If $H\ne0$, the imaginary part gives $y_0+y_7=y_1+y_6$ and the real
part gives $y_0 y_7=y_1 y_6$. Hence the two unordered pairs of $y$
values coincide. But both $P_1-P_0$ and $P_6-P_0$ are nonzero:
a single-swap difference has two nonzero eigenvalue differences
and two nonzero spectator factors. Thus $H=0$.

Since all contact differences lie on one complex line through zero,
the following two ratios are real. Each factorization follows by
expanding the two swapped factors, with the unchanged factors
cancelled:
$$
\begin{aligned}
\frac{P_3-P_2}{P_1-P_0}
 &=\frac{(c_1-c_3)(a_1-c_2)}{(c_2-c_3)(a_1-c_1)},\\
\frac{P_2-P_0}{P_1-P_0}
 &=\frac{(a_1-a_2)(c_1-c_2)(a_3-c_3)}
 {(a_2-a_3)(c_2-c_3)(a_1-c_1)} .
\end{aligned}
$$
All denominators are nonzero. The first ratio is a cross ratio,
so $a_1,c_1,c_2,c_3$ lie on one generalized circle. Use a common
fractional-linear map to send that circle to the real line, with
pole away from both spectra. Its effect is a single nonzero multiplier
on all matching products and on the determinant, and the inverse
multiplier changes the support direction accordingly
([checked projective transport](MOC/ProjectiveTransport.lean)).
The second ratio is now a nonzero real multiple of the cross ratio
$(a_1-a_2)(a_3-c_3)/[(a_2-a_3)(a_1-c_3)]$. It places
$a_1,a_2,a_3,c_3$ on another generalized circle. Finally,
$P_1/P_0$ is real because the contacts have height zero and
$P_0\ne0$. After cancellation it is a cross ratio of
$a_2,a_3,c_2,c_3$. The two latter circles share the three distinct
points $a_2,a_3,c_3$, so they coincide. The resulting circle shares
$a_1,c_2,c_3$ with the first and hence is the first. All six
spectators are therefore real in the chosen chart.

In this chart $P_0=(a_0-c_0)\prod_{i=1}^3(a_i-c_i)$,
and the final product is nonzero real. Consequently
$\operatorname{Re}(\eta(a_0-c_0))=0$. This gives all six
permutations fixing label 0 as contacts, but the comparison below
does not require any counting of contact types.

## Three anchored profiles use one positive law

Switch back to the sum convention $a_i+b_j$ and write $u=a_0$,
$v=b_0$. The condition on the outliers is
$\operatorname{Re}(\eta(u+v))=0$. Put
$$
A=\operatorname{Re}\eta,\qquad B=\operatorname{Re}(\eta u v),
\qquad C=\operatorname{Re}(\eta u)=-\operatorname{Re}(\eta v).
$$
If a permutation matches the two outliers together, its projected
value is zero. Otherwise write $x$ for the real first-spectrum
value matched to $v$ and $y$ for the real second-spectrum value
matched to $u$. If $Q$ is the real product of the other spectator
sums, the projected value is
$$Q\,[Axy+C(x-y)+B].$$
For real $d$, form the anchored spectra with both marked values zero,
subtract $d$ from every first-spectrum spectator, and add $d$ to
every second-spectrum spectator. Let $F_d$ be their matching
profile. It vanishes when the outliers match and is otherwise
$Q(x-d)(y+d)$. Therefore the whole projected profile equals
$$
         (A+B)\,F_0+\frac{C-B}{2}F_1-\frac{C+B}{2}F_{-1}.             \tag{1}
$$
This identity holds with either permutation indexing convention
after inverting the labels.

For each unitary $U$, the
[checked zero-pair theorem](MOC/FourCoincidence.lean),
from [Zheng, Appendix B.1](https://doi.org/10.13140/RG.2.2.36790.25923),
supplies one nonnegative law simultaneously for the three
profiles in (1). The real signed weight law of
[Merikoski and Virtanen](https://doi.org/10.1016/0024-3795(89)90709-X)
reproduces the determinant for all spectra. The two laws agree
on every $F_d$ and hence on (1). Every term in the resulting
nonnegative-weight average is a projected matching value at most
zero, so the projected determinant is at most zero.

Lean checks (1) for every finite index type as
**marked_real_profile_of_zero_pair**, and checks the order-four
support conclusion for real spectators as
**four_real_spectators_zero_height_support** in
[ZhengStabilizerSupport.lean](MOC/ZhengStabilizerSupport.lean).
[ZhengT1Circle.lean](MOC/ZhengT1Circle.lean) checks the pole-free
normalization and consequent real cross ratios, then invokes this
comparison. Its theorem **MOC.ZhengT1.support** proves the whole T1
case, including repeated spectra, coincident cross pairs, and the
zero direction.
