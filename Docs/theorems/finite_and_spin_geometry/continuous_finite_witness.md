# Finite witnesses for MOC along a fixed finite-dimensional unitary update

This is an exact reduction, not a proof of unrestricted MOC. All convex combinations and linear spans below are over the real numbers.

## The compression identity

Let a,b be complex n-tuples, m_i=a_i+b_i nonzero, and z_id=product_i m_i. Put

\[
P_i=\frac1{m_i}\begin{pmatrix}a_i&1\\a_ib_i&b_i\end{pmatrix},
\qquad C_{ij}=\frac{a_i+b_j}{m_i}.
\]

Then P_i is a rank-one trace-one idempotent. Factor P_i=u_iw_i^T with u_i=(1,b_i)^T and w_i^T=(a_i,1)/m_i; thus w_i^Tu_j=C_ij.

Let Y be an n by r complex isometry, with row y_i, and let V be an r by r unitary. Define

\[
U=I_n+Y(V-I_r)Y^*,\quad W_i=y_i^*y_i,\quad
N=\sum_iP_i\otimes W_i.
\]

The determinant identity is

\[
\boxed{\frac{\det(D_a+UD_bU^*)}{z_{id}}
=\frac{\det\{I_{2r}+[I_2\otimes(V-I_r)]N\}}{\det V}.}
\tag{1}
\]

Indeed, det(D_a+UD_bU*)=z_id det(C∘U)/det U and det U=det V. The matrix C∘U is I plus a product whose ith row is w_i^T tensor y_i and whose jth column is u_j tensor (V-I)y_j*. Interchanging the factors in det(I+AB) gives (1).

The identity is simultaneous for every V: N contains all of the dependence on the ambient labels and spectra.

## Positive deletion lemma

The real span of trace-one complex two by two matrices has dimension at most seven: the imaginary part of the trace vanishes, leaving seven real coordinates. The real span of Hermitian r by r matrices has dimension r². Thus the atoms P_i tensor W_i lie in a real vector space of dimension at most 7r².

If the frame Y is real, W_i is real symmetric and the bound becomes 7r(r+1)/2.

Suppose there are more nonzero atoms than this bound. Find a nonzero real relation

\[
\sum_i c_i(P_i\otimes W_i)=0.
\]

Taking the partial trace in the two-dimensional factor gives sum_i c_iW_i=0. Taking its ordinary trace shows that the coefficients have both signs, since every nonzero W_i has positive trace. Consequently one can move the positive weights t_i, initially all one, along this relation until one weight vanishes while all remain nonnegative. Iterating leaves a set S and positive t_i such that

\[
\sum_{i\in S}t_iP_i\otimes W_i=N,
\qquad \sum_{i\in S}t_iW_i=I_r,
\]

with |S| at most the stated dimension. Set y_i'=sqrt(t_i)y_i for i in S. These are the rows of an isometry Y'. Its compressed matrix is exactly the original N.

This argument uses only positive reweighting and deletion. It does not invent new spectral labels or duplicate labels.

## Vertex compatibility

Retain only the original a_i,b_i with i in S and form U'=I+Y'(V-I)Y'^*. The normalized determinant in (1) is unchanged.

For a permutation pi of S, extend pi by fixing every label outside S. The corresponding normalized permutation products satisfy

\[
\frac{\prod_{i\in S}(a_i+b_{\pi(i)})}{\prod_{i\in S}m_i}
=\frac{\prod_{i=1}^n(a_i+b_{\widetilde\pi(i)})}{z_{id}}.
\tag{2}
\]

Thus every reduced normalized vertex was an original normalized vertex. The reduced hull can shrink, but cannot grow.

If an original support direction eta strictly separates its determinant from the original hull, put zeta=eta z_id and eta'=zeta/product_{i in S}m_i. Equations (1) and (2) show that the same strict separation holds for the reduced data.

Zeros among the m_i cause no gap in the strict-counterexample assertion: perturb the spectra slightly, preserving the strict violation by continuity, and avoid those finitely many zero hyperplanes before applying the reduction. No permutation normalization is required.

## Finite-witness theorem

If MOC fails for a relative unitary acting nontrivially on an r-dimensional complex subspace, it fails within the same update class in dimension at most 7r². If the active subspace admits a real orthonormal frame, the bound is 7r(r+1)/2.

In particular:

| Update class | Ambient dimension needed for a strict witness |
|---|---:|
| One-dimensional phase update | At most 7 by exact compression; reduced further to 4 for scalar maximization in the companion note |
| Arbitrary unitary on a real two-plane | At most 21 |
| Arbitrary unitary on a complex two-plane | At most 28 |

For a fixed frame and spectra, the reduction preserves the whole function of V, not just one determinant value. It does not preserve arbitrary minor coefficients, and it does not establish that those finite-dimensional cases are true.

## Intrinsic gauge structure

A common conjugation P_i→SP_iS^{-1} conjugates N by S tensor I. A frame change Y→YQ, V→Q*VQ conjugates N by I tensor Q*. Both preserve the determinant in (1) and the trace-cycle description of the vertices. Positive deletion respects these two gauge actions.

One can therefore regard labelled frames with idempotent weights as objects, and positive deletions preserving N as morphisms. The compressed determinant is constant under these morphisms, while the vertex hull is covariant under the inclusion of retained permutations. A strict separating witness descends to a finite object. This categorical statement adds no positivity assumption: the positive part is precisely the frame reweighting, while the idempotents remain complex and non-Hermitian.
