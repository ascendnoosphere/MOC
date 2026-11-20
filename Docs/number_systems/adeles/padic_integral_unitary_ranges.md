# Exact integral-unitary ranges over quadratic local fields

A p-adic unitary problem needs a specified involution. Let \(L/K\) be a quadratic extension of non-Archimedean local fields, with conjugation \(x\mapsto\bar x\), norm \(N(x)=x\bar x\), and integral rings \(\mathcal O_L,\mathcal O_K\). Write \(U^*=\bar U^{,T}\).

Three different hypotheses must be kept distinct: a matrix being normal, a matrix being unitarily diagonalizable, and a unitary matrix having integral entries. Over these fields none of the needed implications should be imported from complex positive-definite inner-product theory.

## An exact order-two range with integral unitary conjugators

Define the coefficient set

\[
T_{L/K}=\{s\in\mathcal O_K:
s=N(b),\quad1-s=N(d)\text{ for some }b,d\in\mathcal O_L\}.
\tag{1}
\]

Let \(A=\operatorname{diag}(a_1,a_2)\), \(B=\operatorname{diag}(b_1,b_2)\) have arbitrary entries in \(L\), and let

\[
z_{\mathrm{id}}=(a_1+b_1)(a_2+b_2),\qquad
z_{\mathrm{sw}}=(a_1+b_2)(a_2+b_1).
\]

Then the exact range is

\[
\boxed{
\{\det(A+UBU^*):U\in U_2(\mathcal O_L)\}
=z_{\mathrm{id}}+(z_{\mathrm{sw}}-z_{\mathrm{id}})T_{L/K}.
}
\tag{2}
\]

The same set is obtained using \(SU_2(\mathcal O_L)\).

To prove this, if \(s=N(U_{12})\), the unitary row and column identities give

\[
N(U_{11})=N(U_{22})=1-s,\qquad N(U_{21})=s.
\]

The order-two determinant expansion therefore gives

\[
\det(A+UBU^*)=(1-s)z_{\mathrm{id}}+s z_{\mathrm{sw}}.
\]

Conversely, if \(s=N(b)\), \(1-s=N(d)\), the explicit matrix

\[
U=\begin{pmatrix}\bar d&b\\-\bar b&d\end{pmatrix}
\tag{3}
\]

satisfies \(U^*U=I\) and \(\det U=N(d)+N(b)=1\), and realizes this value. This proves (2).

The same calculation works over any quadratic field extension with its involution, using the whole field in place of the integral rings. It identifies the coefficient set by the two norm equations, rather than imposing a single notion of convexity across different fields:

| Quadratic extension and permitted entries | Exact coefficient set |
| --- | --- |
| \(\mathbb C/\mathbb R\), all entries | \([0,1]\) |
| \(\mathbb F_{q^2}/\mathbb F_q\), all entries | \(\mathbb F_q\) |
| Unramified quadratic local extension, integral entries | The valuation condition (4) below |

The first row follows from the nonnegative real norm \(z\bar z\); the second follows from surjectivity of the finite-field norm. Thus these are exact versions of the same order-two algebraic formula with genuinely different coefficient sets.

For an unramified quadratic extension, every unit of \(K\) is a norm of a unit of \(L\), and a uniformizer of \(K\) is also a uniformizer of \(L\). Thus, with \(v\) the integer-valued valuation on \(K\),

\[
\boxed{
T_{L/K}=
\{s\in\mathcal O_K:
v(s),v(1-s)\in2\mathbb Z_{\ge0}\cup\{+\infty\}\}.
}
\tag{4}
\]

Indeed \(v(N(x))=2v_L(x)\), and surjectivity on units supplies every value of nonnegative even valuation. The two norm equations in (1) can be solved independently, after which (3) assembles the unitary matrix. The needed unit-norm surjectivity, including its lifting proof from the residue-field norm, is Proposition 4.2.5 in Kiran Kedlaya's *Notes on class field theory*: https://kskedlaya.org/cft/sec_localcomp.html

For \(A=B=\operatorname{diag}(0,1)\), the vertices are \(0,1\), so the exact integral-unitary determinant range is \(T_{L/K}\). A uniformizer \(\varpi\) is excluded by (4), although it lies in the integral general-linear ball. This is a strict restriction even within the fixed-field part \(\mathcal O_K\) of that ball.

### Exact size in Haar measure

Let the residue field of \(K\) have \(q\) elements, and normalize additive Haar measure by \(\mu(\mathcal O_K)=1\). Then

\[
\boxed{\mu(T_{L/K})=\frac{q-1}{q+1}.}
\tag{4a}
\]

There are \(q-2\) residue classes other than 0 and 1; in those classes both valuations are zero, contributing \((q-2)/q\). In the zero class, \(1-s\) is a unit, while \(s\) must have positive even valuation. Its contribution is

\[
\sum_{k\ge1}\frac{q-1}{q^{2k+1}}
=\frac1{q(q+1)}.
\]

The class of 1 contributes the same amount. The two individual points 0 and 1 have Haar measure zero. Adding gives (4a). Thus the allowed set occupies exactly half of \(\mathbb Z_3\) for \(L/K=\mathbb Q_3(i)/\mathbb Q_3\), and one third of the integral ring when \(q=2\).

This is additive Haar measure of the set of attainable coefficients. It is not a claim about the distribution obtained by sampling a unitary matrix with the group's Haar measure.

For the \(3\)-adic case, among the \(3^6=729\) residue classes modulo \(3^6\), exactly 365 have some lift in \(T\). Of these, 363 entire residue classes lie in \(T\); the two classes 0 and 1 modulo \(3^6\) require further digits to decide. The accompanying SVG orders residues by their least-significant-first ternary digits, exposing the nested congruence structure without treating ordinary real numerical distance as \(3\)-adic distance.

