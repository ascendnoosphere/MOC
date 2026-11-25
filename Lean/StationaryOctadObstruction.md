# Exact geometric obstruction for dense pivot angles

For the stationary-pivot reduction, the conditions “every pivot has a
negative entry” and “the Householder quartic has no additional real
projective zero” are both geometrically possible. They do not assert
the existence of an exact additive spectral lift at a strict violating
maximum.

Lean also checks an [independent dense family with no admissible pivot](MOC/StationaryPivotTransport.lean). The exact octad calculation below is on paper.

Let
\[
 K=\begin{pmatrix}0&1&1&1\\-1&0&1&-1\\-1&-1&0&1\\-1&1&-1&0\end{pmatrix},
 \qquad U=(rI+K)/\sqrt{r^2+3},\quad 0<r<1 .
\]
This is a skew conference matrix: \(K^2=-3I\), so \(U\) is
orthogonal. Write \(c=r/\sqrt{r^2+3}\), \(s=1/\sqrt{r^2+3}\).
At a diagonal pivot \(i\), choose \(j,k\) distinct from \(i\)
with \(K_{jk}K_{ji}K_{ik}=1\); reversing \(j,k\) flips the sign.
The corresponding corrected entry is \(s^2-s^3/c<0\).
For an off-diagonal pivot \(i,j\), choose \(k\notin\{i,j\}\) with
\(K_{ik}K_{kj}=K_{ij}\). Such \(k\) exists since the two
products add to \((K^2)_{ij}=0\). Its diagonal corrected entry
is \(c^2-cs<0\). Strictness and density persist on a neighborhood.

## The phase directions can be the entire real zero set

Write
\[
 a=\frac{(r-1)^2(r+1)}{r(r^2+3)},\qquad
 b=-\frac{(r+1)^2(r-1)}{r(r^2+3)},\qquad
 \gamma=\frac{3r^2+1}{r(r^2+3)} .
\]
The quadrics
\[
\begin{aligned}
 q_{12}(x)&=x_1x_2+x_0(a x_1+b x_2+\gamma x_3),\\
 q_{13}(x)&=x_1x_3+x_0(b x_1+\gamma x_2+a x_3),\\
 q_{23}(x)&=x_2x_3+x_0(\gamma x_1+a x_2+b x_3)
\end{aligned}
\]
vanish on every coordinate vector and every column of \(rI+K\).
In fact these are all their common projective zeros.
On \(x_0=0\) the three pair products vanish, so there are exactly
the three axes. On \(x_0=1\), let \(w=x_3\). The last two equations
give
\[
 D=\det\begin{pmatrix} w+b&\gamma\\\gamma&w+a\end{pmatrix}.
\]
More explicitly the adjugate applied to \((-aw,-bw)\) gives
\[
 D x_1=w(b\gamma-a(w+a)),\qquad D x_2=w(a\gamma-b(w+b)).
\]
Multiplying \(q_{12}\) by \(D^2\) and using these two exact
relations reduces its numerator to
\[
 \frac{3r^2+1}{r^2(r^2+3)}
 w(w-r)(w-1)(w+1)(rw+1).
\]
Thus the only possibilities are \(w=0,r,1,-1,-1/r\).
The determinant
\[
 D=(w^2-1)+\frac{2(1-r^2)w}{r(r^2+3)}
\]
is nonzero at all five possibilities, by direct substitution and
\(0<r<1\). Each has one of the known projective representatives:
\(e_0\) at \(w=0\), and then the four columns of \(rI+K\) at
\(w=-1/r,1,-1,r\) respectively. This proves the assertion.
In particular \(-q_{12}^2-q_{13}^2-q_{23}^2\) is a nonpositive
quartic whose only real projective zeros are the eight trivial
phase directions. No general zero-set argument using only the
sign and those eight zeros can force additional reflection equality.
