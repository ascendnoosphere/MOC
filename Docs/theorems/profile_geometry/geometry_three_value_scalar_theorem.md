# Scalar rank-two compression with at most three spectral values on one side

## Theorem

Let X in C^{2×m} and Y in C^{2×n} be coisometries. If the complex parent
spectrum a has at most three distinct values, then

\[
 \det(XD_aX^*+YD_bY^*)\in
 \operatorname{conv}\{(a_i+b_j)(a_k+b_l):i\ne k,\ j\ne l\}
\]

for every complex b. Parent multiplicities on either side are arbitrary.
The same conclusion holds with the two sides exchanged.

The proof uses the analytically proved colored-edge allocation theorem
in `geometry_three_color_theorem.md`. It allows a coarse spectral class
to be selected twice, with its exact determinant probability.

## 1. Group the equal spectral values

Let the distinct a values be α_1,...,α_g, with g≤3, and put

\[
 E_i=\sum_{r:a_r=\alpha_i}x_rx_r^*.
\]

Then E_i≥0, Σ_i E_i=I_2, and A=Σ_iα_iE_i. Add zero effects if needed
to make three groups. Put

\[
 d_i=\det E_i,\quad D=\sum_i d_i,\quad
 q_{ik}=\operatorname{tr}(\operatorname{adj}E_i E_k)\ (i<k).
\]

The polarization identity in dimension two gives

\[
 1=\det I=\sum_i d_i+\sum_{i<k}q_{ik},
\]

\[
 \det A=\sum_i d_i\alpha_i^2+
             \sum_{i<k}q_{ik}\alpha_i\alpha_k.
\]

All d_i and q_ik are nonnegative. For the right frame write
q^Y_{jl}=|det[y_j,y_l]|² and d^Y_j=||y_j||². The desired mixed
incidence is

\[
 F_{ij}=\operatorname{tr}(\operatorname{adj}E_i\,y_jy_j^*).
\]

## 2. Reserve all double-group probabilities exactly

For each i, reserve the event that both left selections are in group i
with total probability d_i, and give this event right-pair law d_i q^Y.
It contributes d_i d^Y_j to F_ij at each right vertex j.

The residual right law is c q^Y, where c=1−D. Its mixed incidence
matrices are represented by

\[
 H_i=\operatorname{adj}E_i-d_iI:
 \quad F'_{ij}=\operatorname{tr}(H_i y_jy_j^*).
\]

If e_1,e_2∈[0,1] are the eigenvalues of E_i, the eigenvalues of H_i
are e_2(1−e_1),e_1(1−e_2). Hence H_i≥0. Since the two-dimensional
adjugate is linear,

\[
 \sum_iH_i=(1-D)I=cI.
\]

Each H_i also has trace at most c. Indeed, positivity of the mixed
determinants among the other effects implies

\[
 \det(I-E_i)=\det\Bigl(\sum_{k\ne i}E_k\Bigr)
 \ge\sum_{k\ne i}\det E_k.
\]

Expanding det(I−E_i)=1−tr E_i+d_i gives

\[
 \operatorname{tr}H_i=\operatorname{tr}E_i-2d_i\le1-D=c.
\]

These statements actually hold for any number of coarse groups.

## 3. Every residual colored-edge cut holds

For S⊆[n] put K=Σ_{j∈S}y_jy_j*, so 0≤K≤I. The residual incident
right-edge mass is c(tr K−det K). Since
λ_max(K)≤tr K−det K for a two-dimensional positive contraction,

\[
 \sum_{j\in S}F'_{ij}=\operatorname{tr}(H_iK)
 \le\operatorname{tr}(H_i)\lambda_{\max}(K)
 \le c(\operatorname{tr}K-\det K).
\]

The residual column degrees agree because ΣH_i=cI. The colored-edge
allocation theorem therefore supplies an allocation with different
endpoint colors. If c=0 there is no residual allocation to construct.

## 4. Three residual colors determine all cross-group pair probabilities

The residual degree of color i is

\[
 r'_i=\operatorname{tr}H_i=\operatorname{tr}E_i-2d_i.
\]

For three colors, their three unordered pair probabilities are uniquely
determined by these degrees. The desired q_ik have exactly those degrees,
because

\[
 \sum_{k\ne i}q_{ik}
 =\operatorname{tr}(\operatorname{adj}E_i(I-E_i))
 =\operatorname{tr}E_i-2\det E_i=r'_i.
\]

Thus the complete coarse law reproduces every double-group probability
d_i, every cross-group probability q_ik, the full right-pair law q^Y,
and every mixed F_ij.

## 5. Recover the determinant and the original labels

A coarse matching with colors i,k at right vertices j,l represents
(α_i+b_l)(α_k+b_j), including i=k for a reserved double event. Its
average is exactly det(A+YD_bY*) by the displayed coefficient formulas.

For i≠k choose any original label from each selected group. If i=k,
the event has positive probability only when det E_i>0; a single
rank-one original column would have determinant zero, so that group
contains at least two distinct original labels. Choose two of them.
Because the spectral values agree throughout a group, these choices
leave the scalar product unchanged and produce a valid size-two
matching on the original distinct labels.

This proves the theorem. It is a scalar conclusion for the original
fine labels; no fine-label mixed incidence law is asserted after
arbitrary choices of children within a spectral class.

## Additional probabilistic consequence

The same construction proves a complete coarse common law for three
arbitrary positive two-dimensional POVM effects, with diagonal pair
probabilities det E_i. Spectrally refining an arbitrary second POVM
into rank-one effects, applying the construction, and recombining
its labels gives a local hidden-variable model for the singlet when
both parties choose between the same two POVMs and one POVM has at
most three outcomes. The diagonal same-setting events are retained;
they are not discarded by assuming rank-one effects.

## Limits

With four coarse colors, fixing the diagonal pair masses and every
degree still leaves two independent off-diagonal pair coordinates.
The residual allocation theorem alone does not force those coordinates.
The result therefore does not yet prove scalar CMC for four distinct
values on each side, nor the rank-three compression version of MOC4.
