## Round 023 — A whole face of the actual unitary moment hull is determined

**Result: exact convex-hull identification, and extension to arbitrary zero transversals.**

Let M(U) collect the singleton and squared-minor moments. On the face p_11=p_22=p_33=p_44=0, the previous two rounds prove

\[
M(U)\in\operatorname{conv}\{M(P_\pi):\pi\text{ a derangement}}.
\]

Every derangement permutation matrix is itself a zero-diagonal unitary. Thus

\[
\boxed{\operatorname{conv}\{M(U):u_{ii}=0\}
=\operatorname{conv}\{M(P_\pi):\pi\text{ a derangement}}.}
\]

The assertion also identifies the corresponding face of the full convex hull of actual moments. If a convex combination has p_ii=0, every component must have p_ii=0 because all singleton moments are nonnegative. There is no possibility of cancellation across this face.

More generally, if the zero pattern of U contains a perfect matching, independent row and column permutations bring those zeros to the diagonal. Relabeling spectra transports the common-minor law back. This extends the solved class beyond a fixed choice of diagonal and determines every row-column translate of the same moment face.


## Round 034 — Universally normal fixed borders are forced to decouple

**Result: an exact normality obstruction to a common determinant gadget.**

Let

\[
N(D)=\begin{pmatrix}D&X\\Y^*&B\end{pmatrix},
\]

where X,Y,B are fixed and D ranges over all complex diagonal matrices of the indicated size. Assume N(D) is normal for every D. The upper-right block of its normality equation is

\[
DY+XB^*-D^*X-YB=0.
\]

Vary one real diagonal entry of D. Its corresponding row gives Y=X. Vary the imaginary part of the same entry; that row gives Y=-X. Therefore X=Y=0.

Thus a fixed ancilla border that preserves normality for an arbitrary complex diagonal core must be a direct sum. It cannot create the desired Schur-complement subtraction. The familiar block-triangular version is even immediate from equality of the corresponding diagonal blocks of NN* and N*N.

This theorem leaves spectra-dependent couplings and entirely different encodings open. It prevents claiming a universal normal embedding from a formal determinant block identity alone. Direct-sum ancillas merely multiply determinants and preserve existing convex laws; they do not create a uniform additive constant.

## Round 035 — Singular sums are already safe in MOC4, and their stationary geometry is constrained

**Result: a direct use of external positivity and an audited circle lemma.**

Drury's external-vertices theorem implies that every MOC4 instance with det(A+B)=0 satisfies MOC. If zero were outside the permutation hull, a positive separating half-plane could be normalized to Re(eta z_pi)>=1. The theorem would force Re(eta det(A+B))>=1, a contradiction. Thus an actual counterexample must have A+B invertible.

The geometry track's singular stationary lemma is also correct. Let A have distinct diagonal entries, M=A+C have rank n-1, and adj M=kappa r l*. Stationarity of Re(eta det M) on the orbit means W=-eta[A,adj M] is Hermitian. Its off-diagonal entries show supp r=supp l: an index present in only one support would give W_ij nonzero while W_ji=0.

On the common support put w_i=r_i/l_i and t=-eta kappa. Hermiticity gives

\[
t(a_i-a_j)w_i=-\bar t\,\overline{a_i-a_j}\,\bar w_j.
\]

All |w_i| are equal. Taking four pair equations yields R w_k/w_j=conj(R)conj(w_j)/conj(w_k), where R is the usual cross ratio of four a-values. The equal moduli force R real. Thus those spectral values lie on a generalized circle. This is useful geometric structure, although singular determinants themselves cannot violate MOC4 by the first paragraph.

