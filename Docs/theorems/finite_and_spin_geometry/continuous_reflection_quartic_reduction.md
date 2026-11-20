# Reflection gaps, optimized flow, and a nonmaximizing base

## 1. Scope

These are exact reductions for the scalar Marcus–de Oliveira support problem. They do not prove the unrestricted complex conjecture. Let

\[
 A=\operatorname{diag}(a_i),\quad B=\operatorname{diag}(b_i),\quad
 z_\pi=\prod_i(a_i+b_{\pi(i)}),\quad
 F(U)=\Re\{\eta\det(A+UBU^*)\}.
\]

Unless a section explicitly says otherwise, the chosen identity pairing itself maximizes permutation support:

\[
 h=F(I)=\max_\pi\Re(\eta z_\pi).
 \tag{1}
\]

For an orthonormal two-frame \(Y\), put \(P=YY^*\), \(R=I-2P\), and

\[
 \delta_{ij}=h-\Re(\eta z_{(ij)}),\qquad
 \mathcal A(T,T)=\sum_{i<j}\delta_{ij}|y_iTy_j^*|^2,\qquad
 g=h-F(R).
\]

The preceding batch proved the exact Cayley identity

\[
 [h-F(U(T))]\det(I_2+T^2)
 =4\mathcal A(T,T)-2\det(T)\ell(T)+g\det(T)^2,
 \tag{2}
\]

where \(U(T)=I+Y[(I+iT)(I-iT)^{-1}-I]Y^*\). Its whole-plane criterion is

\[
 \ell|_{\ker\mathcal A}=0,\qquad
 g\ge \frac14\ell^T\mathcal A^+\ell.
 \tag{3}
\]

Equation (3) is still unproved for all actual spectral inputs satisfying (1). A generic relative rank-two update cannot be rebased at a maximizing permutation while retaining its rank. Section 6 below gives the exact additional terms for a nonmaximizing base.

## 2. Raw frames and an invariant least-energy problem

No square roots are needed to compute the invariants. Start with any full-rank complex \(n\times2\) matrix \(K\), and set

\[
 G=K^*K,\quad \rho=\det G>0,\quad
 Y=KG^{-1/2},\quad T=G^{1/2}SG^{1/2}.
\]

Then

\[
 YTY^*=KSK^*,\quad
 \det T=\rho\det S,\quad
 \operatorname{tr}(T^2)=\operatorname{tr}((GS)^2),\quad
 P=KG^{-1}K^*.
 \tag{4}
\]

Every transformation in (4) is an invertible real change of Hermitian coordinates. Hence positivity, kernel annihilation, and the scalar expression in (3) are invariant. More intrinsically,

\[
 \ell^T\mathcal A^+\ell
 =\sup_T\{2\ell(T)-\mathcal A(T,T)\}
\]

when \(\ell\) kills the kernel. This variational expression proves invariance even though a Moore–Penrose matrix itself need not transform by an ordinary congruence rule.

Let \(\mathcal E\) be the real Hilbert space of complex edge values, omitting edges with \(\delta_{ij}=0\), with inner product

\[
 \langle a,b\rangle_\delta
 =\sum_{i<j}\delta_{ij}\Re(\overline{a_{ij}}b_{ij}).
\]

Let \(L(T)_{ij}=y_iTy_j^*\). Then \(\mathcal A=L^*L\). A flow represents the cubic term exactly when

\[
 L^*a=\ell/4.
\]

If \(T_*=\mathcal A^+\ell/4\), then \(a_{\min}=L(T_*)\) is the unique least-norm representative. Every other representative has the orthogonal decomposition

\[
 a=a_{\min}+k,\qquad L^*k=0,
\]

and therefore

\[
 \boxed{
 C_{\rm flow}=C_{\min}+\|k\|_\delta^2,\qquad
 C_{\min}=\frac1{16}\ell^T\mathcal A^+\ell.}
 \tag{5}
\]

This identifies exactly which flow changes are free and which energy is unavoidable.

A constructive example of the orthogonal decomposition (5), with repaired budget margin 24/121, is proved in `optimized_triangle_flow_example.md`.

## 3. Reflection expansion and spectral interchange

The new reflection formula below does not require (1) for its algebraic identity: there one may use \(h=F(I)\) even if it is not maximal. Maximality is needed when the resulting deficits are treated as nonnegative budgets.

Write \(C_{ij}=a_i+b_j\) and \(c_i=a_i+b_i\). Because \(R^2=I\),

\[
 \det(A+RBR)=\det(B+RAR).
 \tag{6}
\]

Thus the reflection determinant is unchanged by simultaneously interchanging all \(a_i,b_i\). At permutation vertices this interchange replaces \(z_\pi\) by \(z_{\pi^{-1}}\).

Since \(R\) has two negative eigenvalues, \(\det R=1\). The identity

\[
 \det(A+UBU^*)=\frac{\det(C\circ U)}{\det U}
\]

therefore gives

\[
 \det(A+RBR)
 =\det\bigl(\operatorname{diag}(c_i)-2(C\circ P)\bigr).
\]

Moreover

\[
 C\circ P=[\operatorname{diag}(a)Y,Y]
 \begin{bmatrix}Y^*\\Y^*\operatorname{diag}(b)\end{bmatrix}
\]

has rank at most four. The principal-minor expansion consequently terminates exactly:

\[
 \det(A+RBR)
 =\sum_{|S|\le4}(-2)^{|S|}
 \det((C\circ P)_{S,S})\prod_{j\notin S}c_j.
 \tag{7}
\]

This remains valid when some \(c_i=0\), because it is a polynomial identity and involves no division.

### Four labels and the three Plücker pairings

Fix \(S=\{i<j<k<l\}\), and let \(p_{uv}=\det[y_u;y_v]\). Set

\[
 w_1=p_{ij}p_{kl},\quad
 w_2=p_{ik}p_{jl},\quad
 w_3=p_{il}p_{jk}.
\]

The elementary \(2\times4\) Plücker relation is

\[
 w_1-w_2+w_3=0.
 \tag{8}
\]

Define

\[
 A_a=(a_i-a_k)(a_j-a_l),\quad
 B_a=(a_i-a_j)(a_k-a_l),\quad
 \phi_a(w)=A_aw_1-B_aw_2,
\]

and similarly for \(b\). Expanding the determinant of
\([\operatorname{diag}(a)Y,Y]_{S,:}\) in its first two columns gives

\[
 (a_ia_j+a_ka_l)w_1
 -(a_ia_k+a_ja_l)w_2
 +(a_ia_l+a_ja_k)w_3
 =\phi_a(w).
\]

The second factor in (7) gives \(\phi_b(\overline w)\), so

\[
 \boxed{
 \det((C\circ P)_{S,S})
 =\phi_a(w)\phi_b(\overline w).}
 \tag{9}
\]

There is no complex conjugation on the spectral entries \(b_i\). Treating the second factor as the conjugate of the first would be invalid.

Because of (6), one can average (9) with its \(a,b\) interchange before summing. The averaged factor is

\[
 A_aA_b|w_1|^2+B_aB_b|w_2|^2
 -(A_aB_b+B_aA_b)\Re(w_1\overline w_2).
 \tag{10}
\]

This averaging is essential. An unaveraged four-label term can contain an orientation-sensitive imaginary part which cancels only after the lower-label terms are included.

## 4. Exact reflection gap in permutation deficits

For two disjoint transpositions define

\[
 \delta_{(uv)(rs)}=h-\Re(\eta z_{(uv)(rs)}).
\]

For the ordered four-label set above, put

\[
 \begin{aligned}
 \alpha&=\delta_{ik}+\delta_{jl}-\delta_{(ik)(jl)},\\
 \beta&=\delta_{ij}+\delta_{kl}-\delta_{(ij)(kl)},\\
 \gamma&=\delta_{il}+\delta_{jk}-\delta_{(il)(jk)}.
 \end{aligned}
\]

The four-label contribution to the real support in (10), including the factors outside \(S\), is

\[
 \begin{aligned}
 Q_S
 &=\alpha|w_1|^2+\beta|w_2|^2
   -(\alpha+\beta-\gamma)\Re(w_1\overline w_2)\\
 &=\frac12\left[
  (\alpha-\beta+\gamma)|w_1|^2
 +(\beta-\alpha+\gamma)|w_2|^2
 +(\alpha+\beta-\gamma)|w_3|^2\right].
 \tag{11}
 \end{aligned}
\]

For example, the coefficient \(\alpha\) follows by expanding the two independent swaps:

\[
 \begin{aligned}
 &z_{\mathrm{id}}-z_{(ik)}-z_{(jl)}+z_{(ik)(jl)}\\
 &\qquad=
 (a_i-a_k)(b_i-b_k)(a_j-a_l)(b_j-b_l)
 \prod_{r\notin S}c_r.
 \end{aligned}
\]

The other two coefficients follow identically. Equation (8) proves the second line of (11).

The complete reflection gap is

\[
 \boxed{
 g=4\sum_{i<j}\delta_{ij}|P_{ij}|^2
       -16\sum_{|S|=4}Q_S.}
 \tag{12}
\]

Here is the lower-label cancellation proving (12). A two-label term in (7) is the corresponding \(z_{\mathrm{id}}\det P_{\{i,j\}}\), plus
\((z_{\mathrm{id}}-z_{(ij)})|P_{ij}|^2\). The constant terms from levels zero, one, and two sum to \(z_{\mathrm{id}}\), since
\(\operatorname{tr}P=2\) and \(\sum_{i<j}\det P_{\{i,j\}}=1\).

For a triple \(i,j,k\), use

\[
 z_{(ijk)}+z_{(ikj)}
 =z_{(ij)}+z_{(ik)}+z_{(jk)}-z_{\mathrm{id}}
\]

and \(\det P_{\{i,j,k\}}=0\). After spectral interchange averaging, its determinant term is

\[
 \sum_{\{u,v\}\subset\{i,j,k\}}
 (z_{\mathrm{id}}-z_{(uv)})
 \left(|P_{uv}|^2P_{rr}
       -\Re(P_{ij}P_{jk}P_{ki})\right),
\]

where \(r\) is the remaining label. The coefficient of \(\delta_{ij}\) in the gap contributed by levels two and three is

\[
 -4|P_{ij}|^2
 +8|P_{ij}|^2\sum_{k\ne i,j}P_{kk}
 -8\sum_{k\ne i,j}\Re(P_{ij}P_{jk}P_{ki}).
\]

Now use

\[
 \sum_{k\ne i,j}P_{kk}=2-P_{ii}-P_{jj},\qquad
 \sum_{k\ne i,j}\Re(P_{ij}P_{jk}P_{ki})
 =(1-P_{ii}-P_{jj})|P_{ij}|^2.
\]

The coefficient reduces to \(4|P_{ij}|^2\). The level-four contribution has the sign \(-16Q_S\), completing the proof.

Although (12) was proved using the rank-two spectral matrix \(C\), it also holds for every real common-minor linear cost, with gaps defined by its vertex values. To see this, regard the displayed determinant identity as a polynomial in all \(a_i,b_j\). The coefficient of \(a_{I^c}b_J\) is exactly \(R(U)_{I,J}\). Comparing coefficients and taking real linear combinations gives the assertion. This extension does not identify arbitrary linear common-minor costs with spectral product costs.

In raw-frame coordinates, replace \(p_{ij}\) by \(\det[K_i;K_j]/\sqrt\rho\); each \(|w_m|^2\) consequently has the factor \(\rho^{-2}\). Coefficients in (11) can have either sign; no positive four-label gluing principle is asserted.

## 5. What the reduction still lacks

The all-dimensional maximizing-base problem is now the specific inequality

\[
 4\sum_{i<j}\delta_{ij}|P_{ij}|^2
 -16\sum_{|S|=4}Q_S
 \ \ge\ \frac14\ell^T\mathcal A^+\ell.
 \tag{13}
\]

The three-label budget proves that \(\ell\) kills \(\ker\mathcal A\) and supplies a representing edge flow. The universal optimized inequality (13) for actual spectra remains unproved.

## 6. Exact budget at a nonmaximizing commuting base

Let now \(f_0=F(I)\), \(h\ge\max_\pi\Re(\eta z_\pi)\), and \(c=h-f_0>0\). Define

\[
 \delta^{0}_{ij}=f_0-\Re(\eta z_{(ij)}),\quad
 \mathcal A_0=\sum_{i<j}\delta^0_{ij}|L_{ij}|^2,\quad
 g_h=h-F(R).
\]

The gaps \(\delta^0_{ij}\) can be negative. Let

\[
 W_4=\operatorname{diag}(1,1,2,2),\qquad
 D_4=\begin{pmatrix}
 0&1/2&0&0\\1/2&0&0&0\\0&0&-1&0\\0&0&0&-1
 \end{pmatrix};
\]

these represent \(\operatorname{tr}T^2\) and \(\det T\) in coordinates \(s,t,x,y\). The exact prescribed-height criterion from the preceding batch becomes

\[
 \exists\lambda\in\mathbb R:\quad
 \begin{pmatrix}
 c&0&\lambda/2\\
 0&B_\lambda&-\ell\\
 \lambda/2&-\ell^T&g_h
 \end{pmatrix}\succeq0,\qquad
 B_\lambda=cW_4+4\mathcal A_0-\lambda D_4.
 \tag{14}
\]

Taking the Schur complement of the positive scalar \(c\), then the possibly singular \(B_\lambda\), yields the scalar version

\[
 \boxed{
 \exists\lambda:\quad
 B_\lambda\succeq0,\quad \ell\in\operatorname{range}B_\lambda,\quad
 g_h-\frac{\lambda^2}{4c}\ge
 \ell^TB_\lambda^+\ell.}
 \tag{15}
\]

Both implications include singular \(B_\lambda\); the stated range condition is precisely what the generalized Schur complement requires. At \(c=0\), positivity of (14) forces \(\lambda=0\) and reduces to (3).

One cannot simply replace every \(\delta^0\) by the nonnegative target gap \(\delta^h_{ij}=h-\Re(\eta z_{(ij)})\). With \(\mathcal A_h=\sum\delta^h_{ij}|L_{ij}|^2\), the required correction is

\[
 B_\lambda(T,T)
 =4\mathcal A_h(T,T)
 +c\left(2\sum_i(y_iTy_i^*)^2-\operatorname{tr}(T^2)\right)
 -\lambda\det T.
 \tag{16}
\]

Indeed \(H=YTY^*\) has \(\operatorname{tr}H^2=\operatorname{tr}T^2\), so
\(\sum_{i<j}|H_{ij}|^2=\frac12(\operatorname{tr}T^2-\sum_iH_{ii}^2)\).
Substituting this identity proves (16). The extra diagonal term is a concrete obstruction to treating arbitrary-base and maximizing-base budgets as interchangeable.

## 7. A stable polynomial for every actual two-plane

Every actual two-plane has the real multiaffine polynomial

\[
 p_Y(t)=\det\!\left(\sum_i t_i\,y_i^*y_i\right)
 =\sum_{i<j}|p_{ij}|^2t_it_j.
\]

It is real stable. If all \(\Im t_i>0\), the imaginary part of the matrix inside the determinant is
\(\sum_i(\Im t_i)y_i^*y_i\), which is positive definite because
\(\sum_i y_i^*y_i=I_2\). A matrix with positive definite imaginary part has no kernel, proving nonvanishing.
