# Positive-height constraints, and the exact middle-sector formula

**Status.** These are proved necessary conditions and one exact identity. They do not prove unrestricted \(4\times4\) Marcus–de Oliveira. No priority claim is made.

Notation is as in `MOC4_Verified_Results.md`. For \(\eta\in\mathbb C\setminus\{0\}\),
\[
 h=\max_\pi\operatorname{Re}(\eta z_\pi),\qquad
 g_\pi=h-\operatorname{Re}(\eta z_\pi).
\]
An active label has \(g_\pi=0\).

## 1. Two distinct products on a positive-height line

**Theorem 1.** Suppose \(h>0\) and \(z,z'\) are distinct and satisfy \(\operatorname{Re} z=\operatorname{Re} z'=h\). Then \(z/z'\) is not real. In particular neither product is zero.

**Proof.** Both points lie on the vertical line \(\operatorname{Re}=h>0\). Each open ray from the origin meets that line at most once, so \(z\) and \(z'\) are not real scalar multiples of one another.

**Corollary.** Suppose two active matching products are nonzero and distinct, the support height is positive, and the two permutations differ by a transposition of columns \(c,d\) in rows \(i,j\). Then the four points
\[
 a_i,\ a_j,\ -b_c,\ -b_d
\]
do not lie on a generalized circle.

**Proof.** The ratio of the two products is
\[
 \frac{(a_i+b_c)(a_j+b_d)}{(a_i+b_d)(a_j+b_c)}
 =\frac{(a_i-(-b_c))/(a_i-(-b_d))}{(a_j-(-b_c))/(a_j-(-b_d))}.
\]
Theorem 1 says this ratio is not real. A real cross ratio is equivalent to concyclicity, a line being allowed as a circle.

This is the opposite of the height-zero rule used for Theorem 2 of `MOC4_Verified_Results.md`. There both active products are purely imaginary, so a transposition ratio is real and the four points are concyclic. The circle-merging argument therefore does not transfer to positive height.

## 2. Three corners of a disjoint-swap rectangle

A disjoint-swap rectangle is a set of four permutations obtained by independently swapping two disjoint assignment pairs and leaving the other assignments fixed. Their matching products satisfy \(z_{00}z_{11}=z_{01}z_{10}\).

**Theorem 2.** Suppose \(h>0\) and all matching products under consideration are pairwise distinct. If three corners \(z_{00},z_{01},z_{10}\) are active, write them as \(h+iy_0\), \(h+iy_1\), and \(h+iy_2\) after multiplying by \(\eta\). Then \(y_1-y_0\) and \(y_2-y_0\) are nonzero and of the same sign, the fourth corner is strictly inactive, and its deficit is
\[
 g_{11}=\frac{h(y_0-y_1)(y_0-y_2)}{h^2+y_0^2}>0.
\]

**Proof.** The rectangle identity gives
\[
 z_{11}=\frac{(h+iy_1)(h+iy_2)}{h+iy_0}.
\]
Clearing the denominator \((h-iy_0)/(h^2+y_0^2)\) produces
\begin{align*}
 h-\operatorname{Re} z_{11}
 &=h\cdot\frac{(h^2+y_0^2)-(h^2+y_0 y_1+y_0 y_2-y_1 y_2)}{h^2+y_0^2}\\
 &=\frac{h(y_0-y_1)(y_0-y_2)}{h^2+y_0^2}.
\end{align*}
The denominator is positive. If the numerator is negative, then \(\operatorname{Re} z_{11}>h\), contradicting maximality of \(h\). If the numerator is zero, then \(y_1=y_0\) or \(y_2=y_0\), so two of the three active products coincide. Thus the numerator is positive.

In particular, no four pairwise-distinct products on a positive-height supporting line can occupy a whole disjoint-swap rectangle. That special case was already used in the ten- and eleven-contact arguments; the same-side constraint and the exact positive fourth deficit are the additional content.

## 3. What this does not remove

Contact transfer still supplies, from any strict counterexample, spectra with all \(24\) products nonzero and pairwise distinct and at least six active labels, with the same unitary, the same support direction, and the same positive gap. Drury's \(n=4\) external-vertices theorem covers support height \(h<0\). The zero-height terminal analysis in `MOC4_Verified_Results.md` is unchanged.

At positive height the remaining obstruction is therefore still an actual spectral deficit on one of the rectangle-free mixed faces. The existing enumeration `code/geometry/terminal_profile_faces.py` finds \(83\) symmetry orbits of those six-contact faces. Theorem 2 constrains the \(60\) orbits whose active set contains three corners of a rectangle, but it does not put the deficit in the ordinary squared-minor cone. The \(23\) orbits with no such triple are not touched. Separately, six of the twenty-nine nonzero-height nine-contact types remain open in `global_moc4_weighted_propagation_notes.txt`. Theorems 1 and 2 do not close those types.

## 4. Exact middle-sector formula

The following identity isolates the obstruction to one sufficient certificate. It is not an equivalence with Marcus–de Oliveira: the weights below are not allowed to depend on the spectra.

Let \(U\in U(4)\) and let \(w\) be a probability on \(S_4\). Write
\[
 m_w(K,L)=\sum_{\pi(K)=L}w_\pi
\]
and \(z_\pi=\prod_{i=1}^4(a_i+b_{\pi(i)})\). Expand \(\det(\operatorname{diag}a+U\operatorname{diag}b\,U^*)\) by principal minors and apply Cauchy–Binet to each principal submatrix of \(U\operatorname{diag}b\,U^*\). The same expansion of the weighted average gives, for every complex \(a,b\),
\begin{align*}
 &\det(\operatorname{diag}a+U\operatorname{diag}b\,U^*)-\sum_\pi w_\pi z_\pi\\
 &\qquad=\sum_{|K|=|L|}\bigl(|\det U[K,L]|^2-m_w(K,L)\bigr)
 \Bigl(\prod_{i\notin K}a_i\Bigr)\Bigl(\prod_{j\in L}b_j\Bigr).
\end{align*}

**Theorem 3.** If \(m_w(\{i\},\{j\})=|U_{ij}|^2\) for every \(i,j\), then every term with \(|K|\ne2\) vanishes. Thus
\[
 \det-\sum_\pi w_\pi z_\pi
 =\sum_{|K|=|L|=2}\bigl(|\det U[K,L]|^2-m_w(K,L)\bigr)
 \Bigl(\prod_{i\notin K}a_i\Bigr)\Bigl(\prod_{j\in L}b_j\Bigr).
\]

**Proof.** Both coefficient families vanish when \(|K|\ne|L|\). The empty and full marginals both equal \(1\), as do the corresponding minors. A bijection satisfies \(\pi(K)=L\) if and only if \(\pi(K^c)=L^c\), so \(m_w(K,L)=m_w(K^c,L^c)\). For a unitary matrix the complementary-minor identity gives \(|\det U[K,L]|=|\det U[K^c,L^c]|\). Every three-element index set is the complement of a singleton, and the hypothesis matches those singletons. Only the two-element sum remains.

Consequently, a single spectrum-independent probability that matches both the singleton moduli and the \(2\times2\) squared minors is a Marcus–de Oliveira certificate for that unitary and every spectrum. Producing such a probability is strictly stronger than the conjecture: the weights in the conjecture may depend on \(a\) and \(b\). Failure of this certificate for even one unitary would not be a counterexample to the conjecture. The identity only says that any further spectrum-independent transport proof has to match the two-element sector and nothing else.

## 5. Frontier

Unrestricted \(4\times4\) Marcus–de Oliveira remains open. The first unresolved positive-height obligation is unchanged: an actual spectral support deficit, with all \(24\) products nonzero and pairwise distinct, on a rectangle-free mixed face with six, seven, eight, or nine active labels, must still be shown to lie in the ordinary squared-minor cone or to be impossible.
