# A common matching law for every pair of two-row coisometries with three columns on one side

## Statement

Let X=[x_1,x_2,x_3] in C^{2 x 3} and
Y=[y_1,...,y_n] in C^{2 x n} satisfy XX*=YY*=I_2. There exists a
probability distribution, independent of all complex spectral values,
on size-two matchings between the three X labels and the n Y labels
such that its selected left-pair law, selected right-pair law, and
expected edge-incidence matrix are respectively

\[
q^X_{ik}=|\det[x_i,x_k]|^2,\qquad
q^Y_{jl}=|\det[y_j,y_l]|^2,\qquad
F_{ij}=|\det[x_i,y_j]|^2.
\]

Consequently, for every a in C^3 and b in C^n,

\[
\boxed{
\det(X\operatorname{diag}(a)X^*
    +Y\operatorname{diag}(b)Y^*)
\in\operatorname{conv}
\{(a_i+b_j)(a_k+b_l):i\ne k,\ j\ne l\},
}
\]

and one distribution works simultaneously for all a,b.

The proof is analytic and works for every finite n. It does not depend
on the earlier computer-assisted (3,4), (3,5), or (3,6) facet enumerations.
Its key is a general colored-edge allocation theorem.

## 1. Colored-edge allocation with an arbitrary number of colors

Let q_{jl}>=0, j<l, be edge weights on n vertices, with
sum_{j<l}q_{jl}=1. Put

\[
d_j=\sum_{l\ne j}q_{jl}.
\]

For a subset S of vertices, write

\[
q(S)=\sum_{\{j,l\}\subseteq S}q_{jl},\qquad
\operatorname{inc}_q(S)
=\sum_{\{j,l\}:\{j,l\}\cap S\ne\varnothing}q_{jl}.
\]

Thus inc_q(S)=sum_{j in S}d_j-q(S).

Given m>=2 colors, let F_ij>=0 satisfy sum_iF_ij=d_j.
The allocation problem asks to distribute every edge {j,l}'s mass
q_jl among pairs of different endpoint colors i,k, so that color i
appears at vertex j with total mass F_ij.

Equivalently, there should exist nonnegative weights w_{ik;jl},
i != k, j<l, satisfying

\[
\sum_{i\ne k}w_{ik;jl}=q_{jl}
\]

and the prescribed color-incidence marginals F.

### Allocation theorem

Such weights exist if and only if

\[
\boxed{
F_i(S):=\sum_{j\in S}F_{ij}
\le\operatorname{inc}_q(S)
\quad\text{for every color }i\text{ and subset }S.
}
\tag{A}
\]

Necessity is immediate: an edge can receive color i at most once,
and can contribute to F_i(S) only when incident to S.

The sufficiency proof below applies to every number of colors. The
three-color restriction enters only when recovering the other
endpoint-pair marginal.

## 2. The exact support-function dual

For each right edge {j,l}, its possible normalized color-incidence
vectors form the convex hull of

\[
e_{ij}+e_{kl},\qquad i\ne k.
\]

The set of feasible F is the Minkowski sum of these polytopes weighted
by q_jl. It is nonempty, compact, and convex. Real separation says that
F belongs to it exactly when, for every real cost matrix c,

\[
\boxed{
\sum_{ij}c_{ij}F_{ij}
\ge
\sum_{j<l}q_{jl}\min_{i\ne k}(c_{ij}+c_{kl}).
}
\tag{B}
\]

This is also the finite linear-programming dual of the nonnegative
allocation variables. No integrality assertion is required.

## 3. Column minima turn every dual cost into subset cuts

Subtract the minimum cost from each column:

\[
\mu_j=\min_i c_{ij},\qquad c'_{ij}=c_{ij}-\mu_j.
\]

Because sum_i F_ij=d_j, this subtracts sum_j mu_j d_j from the left
side of (B). The right side changes by the same amount, since every
edge contributes mu_j+mu_l.

Choose a minimizing color g_j in each column. Let delta_j be the
second-smallest entry in that normalized column, counting
multiplicity. Then delta_j>=0, and delta_j=0 whenever the minimum is
tied. For i !=g_j,

\[
c'_{ij}\ge\delta_j.
\]

The optimal two-endpoint edge cost has an exact elementary formula:

\[
\min_{i\ne k}(c'_{ij}+c'_{kl})
=
\begin{cases}
0,&g_j\ne g_l,\\
\min(\delta_j,\delta_l),&g_j=g_l.
\end{cases}
\tag{C}
\]

If the chosen minima differ, use them both. If they coincide, at least
one endpoint must leave that minimizing color; choosing the cheaper
second-best alternative attains min(delta_j,delta_l). If a column has
tied minima, its zero second-best cost makes the same formula valid.

Define the threshold sets

\[
S_i(t)=\{j:g_j=i,\ \delta_j>t\},\qquad t\ge0.
\]

The layer-cake identity min(delta_j,delta_l)
=integral_0^infinity 1_{t<delta_j}1_{t<delta_l} dt gives

\[
\sum_{j<l}q_{jl}\min_{r\ne s}(c'_{rj}+c'_{sl})
=\int_0^\infty\sum_iq(S_i(t))\,dt.
\tag{D}
\]

Meanwhile the full left cost has the exact decomposition

\[
\begin{aligned}
\sum_{ij}c'_{ij}F_{ij}
={}&
\sum_j\sum_{i\ne g_j}(c'_{ij}-\delta_j)F_{ij}\\
&+\int_0^\infty
\sum_i\left(\sum_{j\in S_i(t)}d_j-F_i(S_i(t))\right)\,dt.
\end{aligned}
\tag{E}
\]

Subtracting (D) from (E) yields the exact dual certificate

\[
\boxed{
\begin{aligned}
\sum_{ij}c_{ij}F_{ij}
-\sum_{j<l}q_{jl}\min_{r\ne s}(c_{rj}+c_{sl})
={}&
\sum_j\sum_{i\ne g_j}(c'_{ij}-\delta_j)F_{ij}\\
&+\int_0^\infty\sum_i
\bigl(\operatorname{inc}_q(S_i(t))-F_i(S_i(t))\bigr)\,dt.
\end{aligned}
}
\tag{F}
\]

Every term is nonnegative under F>=0 and (A). The integral is a finite
sum because the threshold sets change only at the finitely many
numbers delta_j. Thus all dual inequalities (B) hold, proving the
allocation theorem.

## 4. Every two-row coisometry pair satisfies the allocation cuts

Now allow X in C^{2 x m} and Y in C^{2 x n} to be arbitrary
coisometries, temporarily without restricting m=3. Define q=q^Y and F
by their determinant formulas in the statement.

Cauchy–Binet gives sum q^Y=det(YY*)=1. The identity

\[
|\det[x,y]|^2=\|x\|^2\|y\|^2-|x^*y|^2
\]

and XX*=I give sum_iF_ij=||y_j||²=d_j.

For any subset S put

\[
K=\sum_{j\in S}y_jy_j^*,\qquad 0\preceq K\preceq I.
\]

Then q^Y(S)=det K and

\[
\operatorname{inc}_{q^Y}(S)=\operatorname{tr}K-\det K.
\]

Write x_i=sqrt(lambda)e_1 in an orthonormal basis, with
0<=lambda=||x_i||²<=1, and

\[
K=\begin{pmatrix}a&z\\\bar z&b\end{pmatrix}.
\]

The mixed marginal is F_i(S)=lambda b. Therefore

\[
\boxed{
\operatorname{inc}_{q^Y}(S)-F_i(S)
=a(1-b)+(1-\lambda)b+|z|^2\ge0.
}
\tag{G}
\]

All quantities are actual scalar matrix entries of a positive
contraction. Thus all allocation cuts hold.

We have proved a useful all-parent intermediate theorem:

> For arbitrary two-row coisometries X,Y, there is a size-two matching
> law reproducing the full mixed matrix F and the full right-pair law
> q^Y.

This law is not asserted to reproduce q^X when X has four or more
columns.

## 5. Three left parents make the remaining pair law automatic

Return to m=3. A matching selects exactly two of the three left
labels. If r is the omitted left label and {i,k} is its complement,
then its probability is

\[
\mathbb P(\text{selected pair}=\{i,k\})
=1-\sum_jF_{rj}
=1-\|x_r\|^2.
\]

The two-row, three-column coisometry identity gives

\[
|\det[x_i,x_k]|^2=1-\|x_r\|^2.
\]

For example, complete X by a unit row z to a three-by-three unitary;
complementary minors give the left side |z_r|², and column norms give
|z_r|²=1-||x_r||². Hence the allocation law also reproduces q^X.
This proves the common matching law in the statement.

## 6. Recover the determinant and the Bell consequence

Cauchy–Binet expands

\[
\det(XD_aX^*+YD_bY^*)
=
\sum_{i<k}q^X_{ik}a_i a_k+
\sum_{j<l}q^Y_{jl}b_jb_l+
\sum_{ij}F_{ij}a_i b_j.
\]

Assign matching {(i,j),(k,l)} the product

\[
(a_i+b_l)(a_k+b_j).
\]

Its two pure terms use the selected endpoint pairs and its mixed
terms correspond to the matching edges. Averaging with the common
law reproduces the determinant for every complex a,b.

As proved independently in geometry Round 021, the same matching law
is exactly a local hidden-variable model for the singlet when both
parties choose between the same two rank-one qubit POVMs
{x_ix_i*} and {y_jy_j*}. Therefore a three-outcome rank-one qubit POVM
paired with any finite-outcome rank-one qubit POVM in this
identical-setting experiment is Bell local.

## Scope and remaining obstruction

This proves the stronger common-law form of CMC(2;3,n) for every finite
n, and by symmetry CMC(2;n,3). It also proves an all-color allocation
theorem and a one-pair-marginal matching theorem for arbitrary parent
sizes.

When both frames have at least four columns, their pair marginals
are no longer determined by the mixed degrees. The left-pair law
produced by the allocation can differ from q^X. Applying the same
construction in the opposite direction gives a second law, not a
proof that the two laws have a common refinement.
The rank-three scalar compression problem equivalent to MOC4 is likewise not settled by this theorem. No spectrum-independent common-minor law is asserted for that problem.

The root researcher independently checked the dual and layer-cake
argument while this note was written. No historical-priority claim
is made; the proof and its application are recorded here in full.
