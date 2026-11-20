# Exact tests of determinant transport against three open-problem targets

**Status.** No proof of unrestricted MOC, Rota's basis conjecture, the Erdős matching conjecture, or Chollet's permanent conjecture is claimed here. The completed results are explicit counterexamples to stronger proposed transfer mechanisms, together with exact identities identifying the remaining global assertions. These are not claims that the target conjectures are false, nor claims of publication priority.

The common input is the wedge/projection-DPP weighted-Hall argument in `../early/proof_notes/metaproof_notes.txt`. Its valid nested couplings do not automatically provide simultaneous, disjoint, or bosonic couplings.

## 1. Rota: the canonical determinant law cannot always be packed

Rota's basis conjecture asks whether n bases in dimension n can be rearranged as n disjoint rainbow bases. A rainbow basis takes one labelled vector from each input basis. Here the inputs are even orthonormal.

For orthonormal bases B_i=(v_i1,...,v_in), define

\[
w(a_1,...,a_n)=|\det(v_{1a_1},...,v_{na_n})|^2,
\qquad q=w/n!.
\]

For a k-vector omega and any orthonormal basis B,

\[
\sum_{v\in B}\|\omega\wedge v\|^2=(n-k)\|\omega\|^2.
\]

Iterating proves sum w=n!, uniform one-vector marginals 1/n, and

\[
\Pr_q(a_1=a,a_2=b)
 =\frac{1-|\langle v_{1a},v_{2b}\rangle|^2}{n(n-1)}.       \tag{1}
\]

This is a genuine determinantal construction: if V contains all n^2 labelled vectors as columns, VV*=nI, so K=V*V/n is a rank-n projection. Conditioning its DPP on rainbow subsets gives q. The conditioning event has probability n!/n^n.

### Explicit obstruction in dimension three

Take

\[
B_1=(e_1,e_2,e_3),\quad x=(1,1,1)^T/\sqrt3,
\quad U=I-2xx^T=\frac13\begin{pmatrix}1&-2&-2\\-2&1&-2\\-2&-2&1\end{pmatrix},
\]

let B_2 be the columns u_1,u_2,u_3 of U, and take

\[
B_3=(x,y,z),\quad y=(1,-1,0)^T/\sqrt2,\quad
z=(1,1,-2)^T/\sqrt6.
\]

Call a rainbow column aligned if it contains e_a and u_a. In a complete disjoint decomposition, two aligned columns force all three aligned: after ordering the first row, a permutation of three points with two fixed points is the identity.

But u_a=e_a-2x/sqrt3, so x belongs to span(e_a,u_a) for every a. If all three columns were aligned, no column could accept x from B_3. Thus every valid decomposition has at most one aligned column.

By (1), the determinant law instead gives

\[
\Pr_q(\text{aligned})=3\frac{1-1/9}{6}=\frac49.
\]

Three columns whose average marginal was q would therefore have expected aligned count 4/3>1. We have proved:

**Theorem.** For these orthonormal inputs, q is not the average column marginal of any probability law on complete rainbow-basis decompositions. In particular, the canonical determinant law cannot be preserved by a disjoint coupling.

### Every marginal-preserving second-row coupling has a dead end

The second-row wedge kernel is

\[
D_{ja}=\frac{1-|U_{ja}|^2}{2}
=\frac1{18}\begin{pmatrix}8&5&5\\5&8&5\\5&5&8\end{pmatrix}.
\]

It is doubly stochastic. Any Birkhoff permutation law with these marginals has expected fixed-point count tr D=4/3. Nonidentity permutations in S_3 have at most one fixed point. If p is the identity's probability, then 4/3<=3p+(1-p), so p>=1/6.

On this unavoidable event, the normalized final-step determinant kernels are

\[
\begin{pmatrix}0&1/4&3/4\\0&1/4&3/4\\0&1&0\end{pmatrix},
\]

with columns indexed by x,y,z. All three rows have only two available neighbors. Ordinary Hall fails. A different Birkhoff decomposition with the same marginals cannot remove this dead end.

### The global polynomial is nevertheless positive here

Let

\[
Z=\sum_{\sigma_1,...,\sigma_n\in S_n}
\prod_{j=1}^n|\det(v_{1,\sigma_1(j)},...,v_{n,\sigma_n(j)})|^2.
\]

For n independent samples T_1,...,T_n from q,

\[
\boxed{Z=(n!)^n\Pr(T_1,...,T_n\text{ are disjoint}).}      \tag{2}
\]

Thus positivity of Z is exactly the desired existence assertion for the orthonormal input, but it does not follow from preserving the local marginals.

For the displayed input, put

\[
A=(0,2/9,2/3),\quad C=(0,8/9,0),\quad
D=(1/3,2/9,0),\quad E=(1/3,1/18,1/6).
\]

The triples of squared determinants against (x,y,z), indexed by (e_j,u_a), are

\[
\begin{pmatrix}A&D&E\\D&A&E\\E&E&C\end{pmatrix}.
\]

After fixing the first row, the six row-two permutations have final-row permanent sums

\[
0,\ 0,\ 4/81,\ 4/81,\ 5/162,\ 5/162.
\]

Therefore

\[
\boxed{Z=6(8/81+10/162)=26/27.}
\]

For example (e_1,u_3,x), (e_2,u_2,y), (e_3,u_1,z) are disjoint rainbow bases, with squared determinants 1/3,2/9,1/6.

The remaining task is a global reweighting or positivity proof for Z for every input. The example refutes the stronger marginal-preserving construction, not Rota.

## 2. Erdős matching: no matching-preserving determinantal envelope

Erdős problem #1020 asks for the largest r-uniform family on n points without k disjoint members. Its proposed extremal size is

\[
\max\left\{\binom{rk-1}{r},\ \binom nr-\binom{n-k+1}{r}\right\}.
\]

A tempting transfer is to enlarge an arbitrary family to the positive support of a determinant measure without increasing its matching number. This is impossible over **every field**, already for seven triples.

Let

\[
\mathcal F=\{123,145,167,246,257,347,356\}.
\]

These are the seven lines of the Fano plane: every pair meets, so the matching number is one.

**Theorem.** Any rank-three matroid whose bases include all members of F has two disjoint bases. Consequently no rank-three determinantal-support envelope of F can preserve its matching number.

**Proof.** Apply basis exchange to bases 123 and 145, removing 2 from 123. The replacement must be 4 or 5. Thus either 134 or 135 is a basis. But 134 is disjoint from the prescribed basis 257, and 135 is disjoint from the prescribed basis 246. In either case there are two disjoint bases. ∎

Positive supports of rank-r projection DPPs are bases of represented matroids: det(V_S*V_S)>0 precisely when the selected r columns are independent. More generally the nonzero maximal-minor supports over any field satisfy the same exchange axiom. Changing fields cannot remove the obstruction above.

This does not disprove the Erdős matching conjecture. It disproves a precise full-strength encoding needed by the naive DPP-envelope attack.

### A historical Erdős problem that the same first-order machinery does prove

Problem #499 is already solved, not a new open-problem closure. For a doubly stochastic matrix P, Birkhoff gives a permutation law with marginals P. Every permutation with positive probability uses only positive entries. Therefore

\[
\max_\pi\log\prod_i P_{i,\pi(i)}
\ge\sum_{i,j}P_{ij}\log P_{ij}
\ge-n\log n.
\]

The last inequality is the rowwise entropy bound, with 0 log 0=0. In fact this gives the explicit strengthening

\[
\boxed{\max_\pi\prod_iP_{i,\pi(i)}
\ge\exp\left(\sum_{i,j}P_{ij}\log P_{ij}\right)\ge n^{-n}.}
\]

This illustrates exactly what Birkhoff controls without silently imposing higher-order compatibility. It is a reproof of a known result, not evidence that #1020 is closed.

## 3. Chollet: the bosonic weighted-Hall replacement is false

Chollet's conjecture states, for Hermitian positive semidefinite A,B,

\[
\operatorname{per}(A\circ B)\le\operatorname{per}(A)\operatorname{per}(B).
\]

By Cauchy–Schwarz on permutation products, it is equivalent to the one-matrix inequality

\[
\boxed{\operatorname{per}(A\circ\bar A)
=\sum_\pi\left|\prod_i A_{i,\pi(i)}\right|^2
\le (\operatorname{per}A)^2.}                            \tag{3}
\]

Necessity uses B=bar A; sufficiency applies (3) separately to A and B. Permanents of PSD matrices are nonnegative, as is also clear from the Gram/Fock representation below.

### The exact symmetric-tensor residual

For Gram vectors u_i in H, use normalized bosonic Fock notation

\[
\Phi=a^\dagger(u_1)\cdots a^\dagger(u_n)|0\rangle
=\sqrt{n!}\,P_{\rm sym}(u_1\otimes\cdots\otimes u_n).
\]

Then ||Phi||^2=per A. Put w_i=u_i tensor bar(u_i) and Omega=Phi_n(w_1,...,w_n). Then ||Omega||^2=per(A circ bar A).

Regrouping factors gives an isometric inclusion

\[
J:\operatorname{Sym}^nH\otimes\operatorname{Sym}^n\bar H
\longrightarrow\operatorname{Sym}^n(H\otimes\bar H).
\]

Separate symmetry implies simultaneous symmetry. Applying the separate symmetrizers to Omega gives

\[
J^*\Omega=\frac1{\sqrt{n!}}\Phi\otimes\bar\Phi.
\]

Hence

\[
\Omega=\frac1{\sqrt{n!}}J(\Phi\otimes\bar\Phi)+E,
\quad E\perp\operatorname{ran}J,
\]

and (3) is equivalent to the still-unproved bound

\[
\boxed{\|E\|^2\le\left(1-\frac1{n!}\right)(\operatorname{per}A)^2.} \tag{4}
\]

The norm decomposition is an identity, not a proof of (4).

### No universal linear reconstruction map

For n>=2 and dim H>=2, there is no complex-linear L on the domain of J satisfying

\[
L(\Phi_n(u_1,...,u_n)\otimes\overline{\Phi_n(u_1,...,u_n)})
=\Phi_n(u_1\otimes\bar u_1,...,u_n\otimes\bar u_n)
\]

for every tuple.

Indeed, setting all u_i equal forces L=J/sqrt(n!) on all vectors u^{tensor n} tensor bar(u)^{tensor n}. These span the domain: a linear functional annihilating them is a polynomial sum c_alpha,beta z^alpha bar(z)^beta vanishing identically, hence has every coefficient zero.

Now set u_1=...=u_{n-1}=e_1 and u_n=e_2 orthonormal. The desired output has squared norm (n-1)!, but the forced map has squared output norm ((n-1)!)^2/n!=(n-1)!/n. Contradiction.

### An explicit Hall deficit of 1/8

Set

\[
u=\tfrac12e_1+\tfrac{\sqrt3}{2}e_2,\qquad
v=\tfrac{\sqrt3}{2}e_1-\tfrac12e_2.
\]

They are orthonormal. The one-particle state x=a^dagger(u)|0> has occupation probabilities

\[
p(10)=1/4,\qquad p(01)=3/4.
\]

Creation in v gives the unit state

\[
y=a^\dagger(v)x=\tfrac{\sqrt6}{4}|20\rangle
+\tfrac12|11\rangle-\tfrac{\sqrt6}{4}|02\rangle,
\]

so q(20)=3/8, q(11)=1/4, q(02)=3/8.

A one-particle-addition coupling must send an occupation alpha only to alpha+e_j. For F={01}, its allowed neighborhood is {11,02}. But

\[
\boxed{p(F)=3/4>5/8=q(N(F)).}
\]

No such nonnegative coupling exists. Appending occupied orthogonal spectator modes preserves this obstruction in every higher degree.

The precise operator defect is visible before coupling. For x_F=(sqrt3/2)|01>,

\[
\|a^\dagger(v)x_F\|^2=\|x_F\|^2+\|a(v)x_F\|^2
=3/4+3/16=15/16>3/4.
\]

Creation is isometric on x because u is orthogonal to v, but not after coordinate restriction. That is the step which the wedge/DPP proof needs and which fails in the symmetric algebra.

This is not a Chollet counterexample: the two Gram vectors are orthonormal, so A=I_2 and Chollet holds with equality. It refutes the proposed bosonic transport proof.

## Sources and scope

- Rota statement: https://en.wikipedia.org/wiki/Rota%27s_basis_conjecture . Recent approximate packing/covering results: https://arxiv.org/abs/2508.05601 .
- Erdős matching statement: https://www.erdosproblems.com/1020 . Frankl–Kupavskii, *The Erdős Matching Conjecture and concentration inequalities*: https://arxiv.org/abs/1806.08855 . A retrieved later preprint https://arxiv.org/abs/2610.16203 claims a large-matching theorem; its abstract is not treated here as an independently checked proof or a full all-parameter closure.
- Erdős #499, explicitly recorded as solved: https://www.erdosproblems.com/499 .
- Kijti Rodtes, *Chollet's permanent conjecture for 4×4 matrices*: https://arxiv.org/abs/2211.02839 . The n=4 case is already established there and is not a new target here.
- *Structural Classes for Chollet's Permanent Conjecture*: https://arxiv.org/abs/2604.24192 . This gives structural classes, not the unrestricted statement.

The three completed mechanism obstructions are: canonical determinant marginal packing fails for orthonormal Rota inputs; matching-preserving matroid envelopes fail for the Fano family over every field; and coordinate-monotone bosonic transport fails even for an orthonormal pair. Any successful transfer must change those exact constructions, not simply rename them in a broader framework.
