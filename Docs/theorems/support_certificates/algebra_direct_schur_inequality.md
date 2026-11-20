# A direct Schur sum of squares for an actual complex four-label spectrum

## Proved statement

For the explicit complex spectra below, the optimized rank-two energy
inequality

\[
\boxed{g-\frac14\ell^T A^+\ell\ge0}
\tag{1}
\]

holds for **every real rank-two frame in dimension four**. The frame may
carry the full complex `U(2)` motion; the restriction here is that its
two-dimensional subspace has a real orthonormal basis. The inequality is
strict whenever the reflection gap is positive.

This is a direct proof of the energy inequality for one genuinely complex
four-label support direction. It uses an exact sum of squares for the
Schur numerator. It is not a proof of (1) for arbitrary spectra, arbitrary
complex rank-two subspaces, or unrestricted complex MOC.

The direct energy certificate below proves the support inequality for the specified actual spectral direction.

## 1. Actual spectral input and all vertex constraints

Take

\[
a=\left(0,\frac12,1,\frac{15-3i}{26}\right),
\qquad
b=\left(\frac{-2+i}{3},\frac{-11+3i}{26},
          \frac{-14-6i}{29},-\frac23\right),
\tag{2}
\]

and use the supporting scalar

\[
\eta=3276-1404i.
\tag{3}
\]

This is 512 times the supporting scalar in
`polyhedral_enlarged_counter_exact.json`; multiplying the support direction
by a positive scalar has no effect on the assertion.

For `c_pi=Re(eta prod_i(a_i+b_{pi(i)}))`, the 24 values in
lexicographic permutation order are exactly

\[
\begin{split}
(&24,-16,15,20,-33,12,\
&-15,-65,20,-25,16,21,\
&-60,16,-16,20,16,-24,\
&-150,-24,-52,24,-16,-66).
\end{split}
\tag{4}
\]

In particular the identity is a maximizing permutation and `h=24`.
The only other maximizing permutation is `(14)`. The exact verifier
recomputes (4) from the complex rational data (2)–(3), rather than assuming
that an arbitrary cost vector is an actual spectral vector.

The six transposition deficits, in the order
`12,13,14,23,24,34`, are

\[
\delta=(39,40,0,9,12,40).
\tag{5}
\]

For `i<j<k`, put `s_ijk=c_(ijk)-c_(ikj)`. In the order
`123,124,134,234`, these are

\[
s=(80,45,72,53).
\tag{6}
\]

The three four-label coefficients from the exact reflection formula are

\[
(\alpha,\beta,\gamma)=(44,-10,-81).
\tag{7}
\]

The negative entries in (7) matter: a termwise positivity argument for
the four-label correction would not prove this example.

## 2. The exact Schur numerator

Let the two columns of a real matrix `Y` be orthonormal, and let
`p_ij` be its real two-by-two minors. Write

\[
(x,y,z,u,v,w)=(p_{12},p_{13},p_{14},p_{23},p_{24},p_{34}).
\tag{8}
\]

These satisfy

\[
xw-yv+zu=0,\qquad x^2+y^2+z^2+u^2+v^2+w^2=1.
\tag{9}
\]

The first equation is the Plücker relation; the second normalizes the
frame. The polynomial identity below is homogeneous, so its positivity
already holds for every real decomposable vector without normalization.

For the reflection `R=I-2YY^T`, define its spectral support gap

\[
g=24-\Re\{\eta\det(D_a+R D_b R)\}.
\tag{10}
\]

The real-frame splitting of the exact Cayley expansion gives

\[
B=A_{yy}=39x^2+40y^2+9u^2+12v^2+40w^2,
\tag{11}
\]

\[
S=80xyu+45xzv+72yzw+53uvw,\qquad \ell_y=-4S.
\tag{12}
\]

Here the coordinate named `y` in `A_yy` is the imaginary off-diagonal
coordinate of a two-by-two Hermitian Cayley parameter. It is independent
of the Plücker variable `y=p_13` in (8). The subscript is kept only to
match the direct-track notation; below `B` avoids this clash.

The real block of `A` and this imaginary scalar block have no coupling,
and `ell` has only its imaginary component. Consequently, when `B>0`,

\[
\frac14\ell^TA^+\ell=\frac{4S^2}{B}.
\tag{13}
\]

The four-label term is

\[
Q=44x^2w^2-10y^2v^2-115xyvw.
\tag{14}
\]

The exact reflection expansion gives

\[
\begin{split}
G:=\frac g4={}&39(yu+zv)^2+40(-xu+zw)^2
                 +9(xy+vw)^2\\
             &+12(xz-uw)^2+40(yz+uv)^2-4Q.
\end{split}
\tag{15}
\]

For example, the terms in (15) are `delta_ij P_ij^2`, with
`P_ij=sum_k p_ik p_jk`, followed by the genuine four-label correction.
Equations (11)–(15) follow from the exact formulas in
`../moc200/continuous_reflection_quartic_reduction.md`, Sections 3–4,
and `direct_quantitative_contact_rigidity.md`, Section 8. The values of
every coefficient are recomputed from (4).

Define the homogeneous sextic

\[
N=BG-S^2=\frac{gB}{4}-S^2.
\tag{16}
\]

Thus the desired statement is exactly `N>=0`, with the case `B=0`
handled directly. The next identity proves it.

## 3. The positive identity

Define eight vectors of cubic monomials:

\[
\begin{aligned}
m_0&=(xyu,xzv,yzw,uvw)^T,\\
m_1&=(xy^2,xu^2,xw^2,yvw)^T,\\
m_2&=(x^2y,xvw,yu^2,yv^2)^T,\\
m_3&=(x^2u,xzw,y^2u,yzv,uv^2,uw^2)^T,\\
m_4&=(x^2z,xuw,y^2z,yuv,zv^2,zw^2)^T,\\
m_5&=(xyw,y^2v,u^2v,vw^2)^T,\\
m_6&=(x^2w,xyv,u^2w,v^2w)^T,\\
m_7&=(xyz,xuv,yuw,zvw)^T.
\end{aligned}
\tag{17}
\]

There are 36 cubic monomials in all. For the eight positive-definite
integer matrices listed in the appendix,

\[
\boxed{
125\,(BG-S^2)=\sum_{b=0}^{7}m_b^T M_bm_b
\quad\text{whenever }xw-yv+zu=0.
}
\tag{18}
\]

This is an exact polynomial identity modulo the Plücker relation. One
way to check it without any choice of frame is to replace each factor
`zu` by `yv-xw` in both sides and compare all coefficients. Both
normal forms have the same 42 nonzero sextic coefficients.

Every `M_b` is positive definite over the rationals. The companion
certificate supplies an exact `LDL^T` factorization of each matrix, with
all 36 diagonal pivots strictly positive. It also reconstructs the matrix
product and every sextic coefficient exactly. The eight blocks have
orders `4,4,4,6,6,4,4,4`; this is a finite sum-of-squares certificate,
not a numerical nonnegativity check.

For `B>0`, equations (13), (16), and (18) immediately yield the explicit
energy margin

\[
\boxed{
g-\frac14\ell^TA^+\ell
=\frac4{125B}\sum_{b=0}^{7}m_b^T M_bm_b\ge0.
}
\tag{19}
\]

If `B=0`, (11) forces `x=y=u=v=w=0`; only `z` can remain. Then
`S=G=0`, and `ell=0`. The Moore–Penrose energy is zero, so (1) holds
there too. The quadratic form `A` is positive semidefinite because all
transposition deficits in (5) are nonnegative. There is no unhandled
kernel component of `ell`.

The optimized Cayley criterion therefore applies to the full complex
`U(2)` orbit associated with each such real frame.

## 4. Strictness and the exact zero set

Because all eight matrices in (18) are positive definite, `N=0` is
equivalent to the simultaneous vanishing of the 36 monomials in (17).
On the real Plücker quadric the zero set is exactly

\[
\operatorname{span}(x,v)\ \cup\
\operatorname{span}(y,w)\ \cup\
\operatorname{span}(z)\ \cup\
\operatorname{span}(u),
\tag{20}
\]

where each notation indicates the coordinate subspace with all other
variables zero.

To verify this, if `z!=0`, the monomials `x^2z,y^2z,zv^2,zw^2`
force `x=y=v=w=0`, and the Plücker relation then forces `u=0`.
If `z=0` but `u!=0`, the monomials `xu^2,yu^2,u^2v,u^2w`
force those same four variables to vanish. If `z=u=0`, the remaining
monomials force `xy=xw=yv=vw=0`, leaving precisely the first two
coordinate planes in (20).

On every subspace in (20), direct substitution gives `G=S=0`. Hence
equality in (1) can occur only when the reflection gap is zero. Whenever
`g>0`, the inequality in (1) is strict. No claim of a uniform strict
factor less than one is needed for this conclusion.

## 5. Why this identity does not prove the general conjecture

The numerical discovery step solved for the free entries of a Gram
matrix only after the actual complex values (2)–(7) were fixed. The
accepted certificate then rounded those entries to rational numbers and
checked positivity and the identity exactly. The statement proved is
therefore the explicit inequality (19), over an infinite continuum of
real rank-two frames, for this specified actual spectrum.

For arbitrary spectra the coefficients in the Schur sextic change.
Nothing in this certificate asserts that the displayed matrices remain
positive or that an equally positive choice always exists. For genuinely
complex two-dimensional subspaces, the real-frame scalar splitting in
(13) also changes; a corresponding certificate must control the full
matrix Schur expression. Those universal assertions remain unproved.

## Appendix: the eight integer Gram matrices

The matrices below are in precisely the monomial order (17).

\[
M_{0}=\begin{pmatrix}
13946&9773&-29292&2636\\
9773&42040&-62472&10976\\
-29292&-62472&118592&-17896\\
2636&10976&-17896&3976
\end{pmatrix}.
\]

\[
M_{1}=\begin{pmatrix}
45000&-28672&55228&81920\\
-28672&45000&-95058&-133632\\
55228&-95058&224648&314104\\
81920&-133632&314104&443392
\end{pmatrix}.
\]

\[
M_{2}=\begin{pmatrix}
43875&169143&-41984&-7168\\
169143&725952&-177152&-162304\\
-41984&-177152&43875&33265\\
-7168&-162304&33265&299915
\end{pmatrix}.
\]

\[
M_{3}=\begin{pmatrix}
195000&238894&-136192&-229376&3084&49152\\
238894&317464&-123904&-263680&2048&70656\\
-136192&-123904&195000&172668&-1536&-15604\\
-229376&-263680&172668&394264&64512&-112128\\
3084&2048&-1536&64512&60000&-49664\\
49152&70656&-15604&-112128&-49664&60000
\end{pmatrix}.
\]

\[
M_{4}=\begin{pmatrix}
58500&43008&37132&55296&-43520&-31232\\
43008&309248&-161280&-70656&10752&199168\\
37132&-161280&200000&109056&-69632&-183296\\
55296&-70656&109056&271360&-44032&-108544\\
-43520&10752&-69632&-44032&58500&62220\\
-31232&199168&-183296&-108544&62220&200000
\end{pmatrix}.
\]

\[
M_{5}=\begin{pmatrix}
395776&306688&-2560&132096\\
306688&471552&73216&97280\\
-2560&73216&45000&-4608\\
132096&97280&-4608&45000
\end{pmatrix}.
\]

\[
M_{6}=\begin{pmatrix}
226304&313856&-19968&-20480\\
313856&502784&-4608&-51712\\
-19968&-4608&13500&-9216\\
-20480&-51712&-9216&13500
\end{pmatrix}.
\]

\[
M_{7}=\begin{pmatrix}
180736&-33792&-17408&-78848\\
-33792&248832&-22528&30720\\
-17408&-22528&286208&-17408\\
-78848&30720&-17408&130560
\end{pmatrix}.
\]
