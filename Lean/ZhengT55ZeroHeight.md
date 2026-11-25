# The zero-height T55 case

This is a direct proof for the six-label $T_{55}$ of
[Zheng, Appendix E](https://doi.org/10.13140/RG.2.2.36790.25923).
Use the paper's lexicographic assignment labels, with zero-based
one-line entries. Thus $\sigma$ sends a first-spectrum index (a row)
to a second-spectrum index (a column), and
$P_\sigma=\prod_i(a_i+b_{\sigma(i)})$.
The Lean matching convention uses the inverse assignment. Let
$G_\sigma=H-\operatorname{Re}(\eta P_\sigma)$, where
$H=\max_\sigma\operatorname{Re}(\eta P_\sigma)$.
Assume $H=0$ and labels 1, 2, 3, 6, 11, 12 are contacts.
Suppose all matching products are nonzero. If not, some $a_i+b_j=0$,
and the already checked order-four opposite-entries theorem applies
([Zheng, Appendix B](https://doi.org/10.13140/RG.2.2.36790.25923);
holds_four_of_opposite_entries in [FourCoincidence.lean](MOC/FourCoincidence.lean)).

## The two additional contacts

Right multiplication swaps positions in a one-line assignment. At
label $2=(0,2,1,3)$, the two disjoint position swaps $(2\,3)$ and
$(0\,1)$ give labels 3 and 12, and doing both gives 13. At
$6=(1,0,2,3)$, the swaps $(1\,3)$ and $(0\,2)$ give 11 and 12,
and doing both gives 17. The product on a disjoint-swap rectangle
factorizes separately over the two pairs. Hence
$$
P_2P_{13}=P_3P_{12},\qquad P_6P_{17}=P_{11}P_{12}.
$$
These identities hold for the rotated products as well.
The rectangle equations and the forced additional contacts are checked in [ZhengT55Identities.lean](MOC/ZhengT55Identities.lean).
If $\eta=0$ there is nothing to prove. Otherwise the active rotated products
are nonzero and purely imaginary. The quotient of the product of two
purely imaginary numbers by a nonzero purely imaginary number is purely
imaginary. Therefore 13 and 17 are also contacts.

## A six-minor certificate

For equal-cardinality subsets $I,J$ of the four indices, write
$e_{I,J}(\sigma)=\mathbf1_{\sigma(I)=J}$. Let $W$ be the real vector
space spanned by these functions. Expanding $P_\sigma$ by the
positions at which the second summand is selected gives a linear
combination of the $e_{I,J}$ with complex coefficients. Since $W$
also contains constants, $G$ belongs to $W$.

The sum and difference of the two events for a pair and its complement
are
$$
\begin{aligned}
e_{I,J}+e_{I,J^c}
  &=\mathbf1_{\sigma\{I,I^c\}=\{J,J^c\}},\\
e_{I,J}-e_{I,J^c}
  &=|\sigma(I)\cap J|-1 .
\end{aligned}
$$
The second line is a sum of singleton markers minus a constant. The
first is a matrix entry marker of the permutation action on the three
pair partitions. Singletons and triples give the same span by
complementation. The $k\times k$ matrix of assignment entry markers
has each row and column summing to one, so its linear span has dimension
at most $1+(k-1)^2$: keep the constant and the entries in the first
$k-1$ rows and columns. Thus $W$ is the sum of a space of dimension
at most 10 and a space of dimension at most 5. Both contain constants,
so $\dim W\le14$.

The eight evaluations 1, 2, 3, 6, 11, 12, 13, 17 are independent on
$W$. In the next table $ij\to kl$ denotes the two-subset marker with
source $\{i,j\}$ and target $\{k,l\}$; with one index on each side
it denotes a singleton. Each displayed function evaluates to one at
the indicated contact and zero at the other seven.

| Contact | One-line assignment | Isolating function |
|---:|---|---|
| 1 | 0132 | $1\to1$ |
| 2 | 0213 | $02\to01$ |
| 3 | 0231 | $1\to2-(02\to01)$ |
| 6 | 1023 | $03\to13$ |
| 11 | 1320 | $01\to13$ |
| 12 | 2013 | $03\to23$ |
| 13 | 2031 | $02\to23$ |
| 17 | 2310 | $01\to23$ |

Consequently the subspace of $W$ vanishing at all eight contacts has
dimension at most six. The six markers below vanish at each contact.
Each is isolated from the other five by the indicated assignment,
so they are independent and form a basis of that subspace.

| Marker | Isolating label | One-line assignment |
|---|---:|---|
| $0\to3$ | 21 | 3120 |
| $2\to0$ | 10 | 1302 |
| $01\to03$ | 4 | 0312 |
| $01\to12$ | 15 | 2130 |
| $02\to02$ | 0 | 0123 |
| $02\to13$ | 7 | 1032 |

The coefficients of $G$ in this basis are exactly
$(G_{21},G_{10},G_4,G_{15},G_0,G_7)$. They are all nonnegative.
The signed Leibniz evaluation of each term is that coefficient times
the squared minor of the mixer with row and column sets $I,J$.
This is the subset-image identity of
[Merikoski and Virtanen](https://doi.org/10.1016/0024-3795(89)90709-X),
checked in [Weights.lean](MOC/Weights.lean) and
[TwoValues.lean](MOC/TwoValues.lean). It proves
$\operatorname{Re}(\eta\det(D_a+UD_bU^*))\le H$ for every unitary $U$.

The six-minor certificate also applies whenever all eight specified
labels are contacts, independently of the initial height. For simple
spectra with no zero factors, either completed rectangle forces that
height to be zero. This proof does not assert the positive-height
T55 support inequality.
