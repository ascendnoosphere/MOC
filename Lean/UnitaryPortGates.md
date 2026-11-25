# One-port unitary gate factorization

The permutations here map columns to rows. Use the normalized signed
determinant weights and subset-image moments of Merikoski and Virtanen
([DOI 10.1016/0024-3795(89)90709-X](https://doi.org/10.1016/0024-3795(89)90709-X)),
as in [Weights.lean](MOC/Weights.lean) and [TwoValues.lean](MOC/TwoValues.lean).

## Exact law

Partition the coordinate set $I=\bigsqcup_{r\in K} B_r$ into nonempty
blocks. Let $U=\bigoplus_r U_r$ be unitary, choose one port $p_r\in B_r$
from each block, and put $P=\{p_r:r\in K\}$. Let $G$ be unitary on $K$.
Extend $G$ by the identity on $I\setminus P$, obtaining $\widetilde G$,
and set $W=\widetilde G U$. If $j\in B_r$, then

$$
W_{ij}=\begin{cases}
U_{ij},&i\notin P,\\
G_{s,r}\,U_{p_r,j},&i=p_s.
\end{cases}
$$

Write $w_X(\sigma)=\operatorname{sgn}(\sigma)\prod_j X_{\sigma(j),j}/\det X$.
If $\sigma$ assigns a wrong-block column to a nonport row, its
product for $W$ is zero. Otherwise the $|B_r|-1$ nonport rows in
block $r$ are assigned distinct columns in $B_r$, leaving one column
$j_r$. The images of the $j_r$ are exactly the ports, without repetition.
Define $\pi$ by $\sigma(j_r)=p_{\pi(r)}$, and define the
block-preserving permutation $\tau$ by $\tau(j_r)=p_r$ and
$\tau(j)=\sigma(j)$ at the other columns. Then
$\sigma=\widetilde\pi\tau$, where $\widetilde\pi$ fixes the nonports.
Conversely every pair $(\pi,\tau)$ with $\tau$ block-preserving
gives a permutation with no wrong-block nonport assignment.
These two constructions are inverses.

Reindexing gives $\det\widetilde G=\det G$ and
$\operatorname{sgn}(\widetilde\pi)=\operatorname{sgn}(\pi)$, since the
operators on the nonports are identities. The entry formula
factors each permutation product, so sign multiplicativity and
$\det W=(\det G)(\det U)$ give

$$
w_W(\widetilde\pi\tau)=w_G(\pi)w_U(\tau).
$$

This is an identity of signed weights, not a positivity claim.
To obtain the hull bound, fix the first spectrum $a$. Suppose one
probability law $\lambda$ on the port permutations gives the correct
determinant of $G$ at the fixed first port spectrum $(a_{p_r})_r$ and
**every** partner spectrum. This is the property
[HasCommonWeights](MOC/CommonWeights.lean); an all-minor law is not
required. By [signed_determinant](MOC/Weights.lean), in the sum
for the actual determinant of $W$ we can first sum over $\pi$.
For each $\tau$, the nonport factors are independent of $\pi$ and
the remaining factors are exactly

$$
\prod_{r\in K}(a_{p_{\pi(r)}}+b_{j_r}).
$$

Thus the inner signed sum over $\pi$ can be replaced by the same
$\lambda$, independently of $\tau$. Interchanging the two sums
and applying the signed formula again gives

$$
D_W(a,b)=\sum_\pi \lambda(\pi)D_U(a\circ\widetilde\pi,b).
$$

Each determinant on the right is covered if each child block
satisfies MOC for the spectra allocated to it by every $\pi$, using
[holds_directSum](MOC/Small.lean). In particular it suffices that the
fixed child mixers satisfy MOC for arbitrary spectra. All matching
hulls on the right equal the original hull, by permutation composition.

## Consequences and limits

- If $|K|\le3$, every unitary gate has a spectral-independent law.
  The checked Birkhoff singleton marginals
  ([exists_singleton_weights](MOC/Weights.lean)) give the whole law by
  complementary minors
  ([indexed_minor_law_of_small](MOC/FiniteMinorLaw.lean)).
- If the fixed first port spectrum takes at most two distinct
  values, the subset of columns assigned one of the values
  determines the entire matching product. Its probabilities are the
  squared subset minors, independent of the second spectrum, by the
  argument of [holds_two_values](MOC/TwoValues.lean) and
  [sum_subsetMinorSq](MOC/TwoValues.lean). This gate may have any size.
- A tree with at most three coordinates in each leaf and at most
  three ports at each gate satisfies MOC for arbitrary spectra and
  arbitrary finite size. In fact, independently sample each block
  and gate law and compose the permutations. This one law gives the
  correct determinant for all spectra, by the interpolation above,
  and the [subset marker specialization](MOC/TwoValues.lean) then
  identifies all its squared-minor marginals.
- Join two dense unitary blocks of order three, for example
  normalized Fourier matrices, with a two-port gate whose two
  coefficients are nonzero. Every row and column has at least three
  nonzero entries. Thus no row and column reindexing can make the
  matrix upper Hessenberg, whose first column has at most two
  nonzero entries. The combined row-column graph is connected,
  excluding a paired-block decomposition. The interpolation proves
  the full hull inclusion for this mixer nevertheless.
- With two ports in one child block, a joined entry can contain
  several contributing terms, so the pointwise factorization above
  no longer follows.

The unrestricted gate proof above is a symbolic paper proof. For
two ports the repository checks the pointwise signed interpolation,
unitarity, and actual hull inequality in [OneBridge.lean](MOC/OneBridge.lean).

## Recovering the gate from a row separator

There is also a converse structural statement. Suppose deleting
$|K|$ port rows from a unitary leaves row groups $N_r$ supported in
disjoint column blocks $C_r$ that partition the columns, with
$|N_r|=|C_r|-1$ for every $r\in K$. Restrict the rows in $N_r$ to
$C_r$. They are orthonormal and their orthogonal complement in
$\mathbb C^{C_r}$ is one-dimensional. Choose a unit row $u_r$
spanning it. Every removed row was orthogonal to every row in $N_r$,
so its restriction to $C_r$ is a scalar multiple $G_{s,r}u_r$.
Because the port rows were orthonormal, $GG^*=I$. The matrix $G$ is
square, hence unitary.

Pair the port rows arbitrarily with the column blocks and reindex
the coordinates by these paired blocks. Completing the rows in
$N_r$ by $u_r$ gives a unitary block. The original matrix is
$\widetilde G U$ for the direct sum $U$ of the completed blocks.
Thus the gate theorem applies to a mixer recognized by a
one-deficit row separator of its support, not only to a mixer
originally presented as a gate circuit. Unitary blocks of higher
defect give higher-dimensional ports, for which the signed
factorization has not been proved.
