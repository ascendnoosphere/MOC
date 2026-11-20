# Exact classification of a saturated Spin slice

This is a root derivation during rounds 011–020, not an assertion about all of SO(6).

Partition R in SO(6) into 2×2 blocks and define m_ij=||R_ij||_F², h_ij=det R_ij.
Suppose, for i=1,2,3,

\[
m_{ii}=1+s_i^2,\qquad h_{ii}=-s_i,\qquad 0<s_i<1.
\]

The singular values of the ith diagonal block are exactly 1 and s_i, because their squared sum and product are specified. Using independent left and right SO(2) transformations in each block, make R_ii=diag(-1,s_i). A real 2×2 matrix of negative determinant has this oriented singular-value form. These transformations preserve every m_ij, h_ij and the determinant of R.

The first row and first column of R_ii already have squared norm one. Orthogonality of the whole R therefore forces the corresponding rows and columns of every off-diagonal block to vanish. After regrouping the first and second coordinates, R is exactly

\[
(-I_3)\oplus Q,\qquad Q\in O(3),\quad\det Q=-1,
\quad Q_{ii}=s_i.
\]

In particular all off-diagonal block determinants vanish. This is a consequence, not an additional hypothesis.

Let S=s_1+s_2+s_3 and A=s_1²+s_2²+s_3². Since -Q is a proper rotation, its quaternion parameters obey

\[
q_0^2=(1-S)/4,\qquad q_i^2=(1+S-2s_i)/4.
\]

Thus S≤1. The squared entries on the two directed off-diagonal cycles have sums D and E satisfying

\[
D+E=3-A,\qquad
D-E=\pm 3\sqrt{(1-S)\prod_i(1+S-2s_i)}.
\]

The second formula follows from the rotation entries 2(q_iq_j±q_0q_k): each directed-pair square difference is ±16q_0q_1q_2q_3, with the same sign on the three edges of a directed cycle. Consequently

\[
\boxed{D=\frac{3-A}{2}\pm\frac32
\sqrt{(1-S)\prod_i(1+S-2s_i)}.}
\]

For equal s_i=s, the smaller directed sum is

\[
D=3a(s)^2,\qquad
a(s)=\frac{(1+s)-\sqrt{(1+s)(1-3s)}}2,
\quad 0\le s\le1/3.
\]

The penalty numerator is F=3(1+s²-6s). Therefore any universal constant C in F+CD≥0 must obey

\[
C\ge \frac{6s-1-s^2}{a(s)^2}
\]

whenever the numerator is positive. At s=1/4 this gives the exact lower bound

\[
\boxed{C\ge \frac{7(3+\sqrt5)}{10}\approx3.665247584.}
\]
