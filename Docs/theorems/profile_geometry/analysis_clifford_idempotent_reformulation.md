# An exact all-dimensional rank-one-idempotent / Clifford reformulation of MOC

This is a reformulation, not a proof of MOC. It works in every matrix dimension n. The Clifford matrices are two-by-two complex matrices; their Pauli vectors and Gram matrices are complex bilinear objects, not Hermitian positive-semidefinite objects.

## 1. Normalize a nonzero permutation product

Let a,b be complex spectra and z_pi=product_i(a_i+b_pi(i)). If at least one z_pi is nonzero, relabel b by such a permutation. Then

\[
m_i=a_i+b_i\ne0,\qquad z_{id}=\prod_i m_i\ne0.
\]

If every permutation product vanishes, MOC is immediate: for every unitary U,

\[
\det((a_i+b_j)U_{ij})=\sum_\pi\operatorname{sgn}(\pi)
\prod_i U_{i\pi(i)}z_\pi=0.
\]

Since this determinant is det(A+UBU*) det U and det U is nonzero, the target determinant also vanishes. Thus the nonzero normalization covers every nontrivial instance, without a genericity assumption.

Define the rank-at-most-two matrix

\[
C_{ij}=\frac{a_i+b_j}{a_i+b_i}.
\]

It has diagonal one. Put

\[
u_i=\binom{b_i}{1},\qquad
w_i^T=\frac{(1,a_i)}{m_i},\qquad
P_i=u_iw_i^T=\frac1{m_i}\begin{pmatrix}b_i&a_ib_i\\1&a_i\end{pmatrix}.
\]

Then w_i^T u_i=1, so P_i²=P_i and tr P_i=1. Each P_i has rank one. These are complex idempotents; generally P_i is not Hermitian.

## 2. Permutation products become cycle traces

For a cycle c=(i1 i2 ... ik), rank-one multiplication gives

\[
\operatorname{tr}(P_{i_1}\cdots P_{i_k})
=(w_{i_1}^Tu_{i_2})\cdots(w_{i_k}^Tu_{i_1})
=\prod_{r=1}^k C_{i_r,i_{r+1}},
\]

where i_(k+1)=i1. Therefore, for every permutation,

\[
\boxed{\frac{z_\pi}{z_{id}}
=\prod_{c\text{ a cycle of }\pi}
\operatorname{tr}\Bigl(\prod_{i\in c}^{\text{cyclic order}}P_i\Bigr).}
\tag{1}
\]

A fixed point contributes tr P_i=1. The formula includes permutations with several disjoint cycles.

For any unitary U, multiplication on the right by U gives

\[
(A+UBU^*)U=AU+UB=((a_i+b_j)U_{ij}).
\]

Hence

\[
\boxed{\frac{\det(A+UBU^*)}{z_{id}}
=\frac{\det(C\circ U)}{\det U}.}
\tag{2}
\]

Equations (1) and (2) preserve convex-hull membership because multiplication by a nonzero complex scalar is an invertible real-linear map.

## 3. Pass to the three Pauli coordinates

Let

\[
Q_i=2P_i-I.
\]

Then tr Q_i=0 and Q_i²=I. With the usual Pauli matrices

\[
\sigma_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\sigma_2=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad
\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\]

write Q_i=nu_i·sigma. The coefficients nu_i lie in C³. The multiplication identity

\[
(x\cdot\sigma)(y\cdot\sigma)
=(x\cdot y)I+i(x\times y)\cdot\sigma
\]

uses the complex-bilinear dot and cross products, without conjugation. Therefore

\[
\nu_i\cdot\nu_i=1.
\]

Explicitly,

\[
\nu_i=\left(
\frac{1+a_ib_i}{m_i},\
\frac{i(a_ib_i-1)}{m_i},\
\frac{b_i-a_i}{m_i}
\right).
\]

Define the complex symmetric Gram matrix

\[
G_{ij}=\nu_i\cdot\nu_j=\tfrac12\operatorname{tr}(Q_iQ_j).
\]

Then

\[
\boxed{G^T=G,\quad G_{ii}=1,\quad\operatorname{rank}G\le3.}
\tag{3}
\]

For n=4, the rank condition is the single complex equation det G=0, together with the possibility of lower rank. This matrix need not be real, Hermitian, or positive semidefinite.

## 4. Pair, triple, and four-cycle formulas

Put s_ij=tr(P_iP_j)=(1+G_ij)/2 and V_ijk=nu_i·(nu_j×nu_k). Then

\[
\operatorname{tr}(P_iP_jP_k)
=\frac12(s_{ij}+s_{jk}+s_{ki}-1)+\frac{i}{4}V_{ijk},
\]

\[
\operatorname{tr}(P_iP_kP_j)
=\frac12(s_{ij}+s_{jk}+s_{ki}-1)-\frac{i}{4}V_{ijk}.
\]

In particular

\[
\boxed{V_{ijk}^2=\det G[\{i,j,k\}],\quad
\left(\operatorname{tr}(P_iP_jP_k)-\operatorname{tr}(P_iP_kP_j)\right)^2
=-\tfrac14\det G[\{i,j,k\}].}
\tag{4}
\]

The signs of the triple volumes are coherent: they come from one collection of vectors nu_i, not independently selected square roots.

For a four-cycle (i j k l), Pauli multiplication gives

\[
\begin{aligned}
\operatorname{tr}(P_iP_jP_kP_l)=\frac18\bigl[
&1+G_{ij}+G_{ik}+G_{il}+G_{jk}+G_{jl}+G_{kl}\\
&+G_{ij}G_{kl}-G_{ik}G_{jl}+G_{il}G_{jk}\\
&+i(V_{ijk}+V_{ijl}+V_{ikl}+V_{jkl})\bigr].
\end{aligned}
\tag{5}
\]

Longer cycles in arbitrary n are obtained by the same two-by-two Clifford multiplication rule.

## 5. Converse: this is the full spectral class

Start with any finite collection of rank-one complex two-by-two idempotents P_i with trace one. Choose one common invertible matrix S such that every lower-left entry of S P_i S^{-1} is nonzero. Such an S exists: for each non-scalar P_i, the condition that this entry vanish is a proper algebraic condition on S, and a finite union of proper algebraic subsets cannot exhaust GL(2,C).

Write a transformed idempotent as

\[
P_i=\begin{pmatrix}p_i&q_i\\r_i&1-p_i\end{pmatrix},\qquad r_i\ne0.
\]

Its rank-one condition gives q_i r_i=p_i(1−p_i). Set

\[
a_i=(1-p_i)/r_i,\qquad b_i=p_i/r_i,\qquad m_i=1/r_i.
\]

Then the matrix is exactly the idempotent constructed in Section 1. Simultaneous conjugation preserves every cycle trace. Thus every finite collection of these complex idempotents arises from actual complex spectra for the purposes of the normalized determinant and permutation products.

Equivalently, start with a complex symmetric matrix G of rank at most three and diagonal one. It admits a complex bilinear Gram factorization G=V^T V with at most three rows. Its column vectors nu_i have nu_i·nu_i=1. The matrices P_i=(I+nu_i·sigma)/2 are rank-one trace-one idempotents, so the preceding construction yields spectra. A coherent orientation of V fixes the triple-volume signs. For rank three, changing the global orientation reverses cycle traces, corresponding to inverting permutation cycles; it must not be replaced by independent sign choices on different triples.

## 6. The abstract conjecture

For rank-one trace-one idempotents P_1,...,P_n, define

\[
Z_\pi(P)=\prod_{c\text{ a cycle of }\pi}\operatorname{tr}\Bigl(\prod_{i\in c}P_i\Bigr).
\]

Choose rank-one factorizations P_i=u_iw_i^T with w_i^T u_i=1, and put C_ij=w_i^T u_j. Rescaling each factor pair changes C by diagonal similarity, which leaves both det(C∘U) and all matching products unchanged. Thus the following statement is well defined:

\[
\boxed{\frac{\det(C\circ U)}{\det U}
\in\operatorname{conv}\{Z_\pi(P):\pi\in S_n\}\quad
\text{for every }U\in U(n).}
\tag{6}
\]

Sections 1–5 prove that (6) is equivalent to the original complex MOC in every dimension. In dimension four, the separate realification theorem permits U to be restricted to O(4), while the P_i and their Gram matrix remain fully complex.

## 7. Where the proof obligation remains

In a support direction, normalized spectral data are described by zeta=eta z_id and the coherent complex Gram matrix G. Transposition gaps are

\[
\delta_{ij}=\tfrac12\operatorname{Re}[\zeta(1-G_{ij})].
\]

The two oriented three-cycle gaps are obtained from (4), and double-transposition values are s_ij s_kl. These formulas give explicit nonlinear constraints coupling the spectral coefficients in the real Cayley quartic. In dimension four, det G=0 is the compact complex constraint whose elimination from real support data is substantially more complicated.

No positivity conclusion follows merely from calling G a Gram matrix: its form is complex bilinear and is generally indefinite on real and imaginary parts. The unresolved step is proving the unitary-weight convex-hull inequality (6), or its equivalent real O4 Cayley quartic inequality. The reformulation identifies the exact spectral class; it does not enlarge it to arbitrary support costs or shrink it to Hermitian projectors.
