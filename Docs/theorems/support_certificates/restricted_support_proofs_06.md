## 1. Identities, base transport, and the exact sufficient region

Let \(g_\pi=h-c_\pi\ge0\), with \(h\) the actual maximum of the
permutation costs. Let \(A\) be the base gap, \(T\) the sum of its
six transposition gaps, \(D\) the sum of its nine derangement gaps, and
\(K\) the signed three-cycle expression in the direct note. Define

\[
 V_4=\{e,(12)(34),(13)(24),(14)(23)\},\qquad
 S=\sum_{v\in V_4}g_v,\qquad t=T-2A.
\]

The four three-label relations and the alternating relation imply

\[
 \sum_{\text{three-cycles}}g_\pi=2t,\qquad
 T=t+2A,\qquad D=t+2S-3A.
 \tag{36.1}
\]

These are identities in the full real common-cost space. I independently
checked them on 20 spanning profile-coordinate columns under every one
of the 24 base translations, giving 480 exact spanning checks. Each of
the four individual triangle relations was included. I also checked
directly on this spanning set that \(S,t,K\) are unchanged within each
\(V_4\) coset. This last invariance is stronger than just the constancy
of \(S\).

There are four signs of each orientation in \(K\), so nonnegative
gaps give

\[
 0\le A\le S,\qquad t\ge0,\qquad |K|\le2t.
 \tag{36.2}
\]

The core identity is

\[
 TD-t^2=t(2S-A)+2A(2S-3A).
 \tag{36.3}
\]

If \(A\le2S/3\), both terms on the right are nonnegative. If
\(t\ge2S\), a useful exact rearrangement is

\[
 TD-t^2=(t-2S)(2S-A)+2(S-A)(2S+3A)\ge0.
 \tag{36.4}
\]

Both conditions therefore imply \(K^2\le4t^2\le4TD\). There is no
division by a potentially zero coefficient in this argument. If \(S=0\),
then \(A=0\), \(T=D=t\), and the result remains valid. If \(t=0\),
then \(K=0\), which is sufficient directly.

For \(S>0\), the exact region in which (36.3) fails, subject to
\(D\ge0\), is correctly normalized as

\[
 \frac23<a=\frac AS\le1,\qquad
 3a-2\le u=\frac tS<\frac{2a(3a-2)}{2-a}.
 \tag{36.5}
\]

The denominator \(2-a\) is positive because \(a\le1\). This is the
potentially unsettled region for the elementary estimate
\(|K|\le2t\), not a necessary region for failure of the actual support
inequality. The actual \(K\) may be far smaller than its elementary
upper bound.

### At least three bases per coset

The four possible base gaps are nonnegative and sum to \(S\). At most
one can exceed \(2S/3\). Thus at least three bases in each of the six
cosets satisfy the budget, giving at least 18 of the 24 bases. This
count is valid even when \(S=0\), when all four bases are safe.

Changing the base changes the translated isoclinic support problem. The
three-of-four result does not transfer the conclusion to the remaining
base or prove the universal budget. The direct note maintains that
distinction.

## 2. Actual spectral determinant and Walsh formulas

With

\[
 P(a)=(a_1-a_2)(a_3-a_4),\qquad
 Q(a)=(a_1-a_3)(a_2-a_4),
\]

I independently expanded the eight actual spectral products with their
orientation signs. The result has 24 nonzero monomials and satisfies

\[
 K=2\operatorname{Re}\{\eta[P(a)Q(b)-Q(a)P(b)]\}.
 \tag{36.6}
\]

This is a complete complex polynomial identity before taking the real
part, so it has no hidden reality assumption on the spectra.

I also independently verified the four Walsh product formulas and their
mean and three linear coefficients. I then reconstructed all 24 actual
products and checked that the six coordinate permutations of the second
Walsh vector, each with the four Klein sign choices, give exactly the
same multiset of 24 polynomials. Thus the six-tetrahedron support formula
covers every permutation, rather than just the original four-element
coset. In these coordinates the orientation identity is indeed

\[
 K=-32\operatorname{Re}\left\{\eta
 \det\begin{pmatrix}
 1&1&1\\X_1^2&X_2^2&X_3^2\\Y_1^2&Y_2^2&Y_3^2
 \end{pmatrix}\right\}.
 \tag{36.7}
\]

These identities retain the original spectral source but do not, by
themselves, give the needed inequality in all of (36.5).

### The stated phase geometry is valid

Write the four coset gaps as \(H-\epsilon\cdot l\), where
\(\epsilon_1\epsilon_2\epsilon_3=1\), so \(S=4H\).
If \(l_1l_2l_3\ge0\), the allowed sign changes make all three
coefficients nonnegative, including zero-coordinate cases. With their
absolute values ordered as \(x\ge y\ge z\ge0\), support maximality
gives \(H\ge x+y+z\). The largest gap is at most
\(H+x+y-z\le2H=S/2\), and every base is safe.

If the product is negative, allowed sign changes make the triple
\((-x,-y,-z)\), with \(x\ge y\ge z>0\). Then support maximality
gives \(H\ge x+y-z\), while a dominated gap \(A>2S/3\) requires
\(H<3(x+y+z)/5\). Together these force \(z>(x+y)/4\), exactly as
stated. These are necessary geometric conditions for an unsettled coset,
not a complete solution of its spectral compatibility constraints.

## 3. Repeated-spectrum theorem and actual sharpness

The two-plus-two repeated-spectrum result is correct for all phases,
all other spectra, and all base permutations.

If \(a=(p,p,q,q)\), right composition by \((12)(34)\) preserves
every complex product. It pairs the four members of every \(V_4\)
coset into equal-cost pairs, so every gap is at most \(S/2\). A
different ordering of the repeated eigenvalues merely changes the
nonidentity double transposition used. If \(b\) is the repeated
spectrum instead, the same reasoning uses left composition; normality of
\(V_4\) ensures that this still pairs members within each coset.
Coincident values and zero support coefficients cause no problem.
Therefore the sufficient region above applies for arbitrary complex
support coefficient \(\eta\). This is a theorem about the stronger
isoclinic budget in that family; no new discovery claim about the
underlying MOC special case is needed.

For the supplied finite actual example

\[
 a=(1,1,-1,-1),\qquad b=(i,-i,-i,i),\qquad\eta=\frac14,
\]

independent rational complex multiplication gives sixteen cost values
\(1\), eight values \(-1\), and \(h=1\). The resulting data are

\[
 (A,T,D,K,S,t)=(0,4,4,-8,0,4).
\]

Hence \(K^2=4TD\), with \(TD>0\), so no coefficient smaller than
four can hold for all actual instances. With the stated convention for
\(J\), the exact isoclinic deficit is

\[
 \frac{4(r+1)^2}{(r^2+3)^2}.
\]

This equality model proves a sharp necessary constant; it does not turn
the still-unproved universal bound into a theorem.

## 4. Entire finite actual two-parameter cost family

The family is genuinely an actual finite spectral source, not just a
point in a projected closure. Set

\[
 q=(1,0,0,\varepsilon),\quad
 a=(1,\tau+i\nu,0,0),\quad
 b_j=-\frac1{1+q_j},\quad
 \eta=2(1+\varepsilon),
\]

where \(0\le\tau,\varepsilon\le1/2\) and \(\nu\in\mathbb R\).
All denominators \(1+q_j\) are strictly positive, so every member is
finite, including every boundary case. The source has a freely variable
imaginary parameter \(\nu\), while the real cost depends only on
\(\tau,\varepsilon\).

To check the entire family rather than selected points, I independently
cleared the four column denominators. Their product is exactly
\(2(1+\varepsilon)=\eta\). Expanding each of the 24 complex products
then yields symbolically

\[
 \eta z_\pi=-q_{\pi(1)}
 [1-(\tau+i\nu)(1+q_{\pi(2)})].
 \tag{36.8}
\]

The real part is nonpositive throughout the specified rectangle, because
\(\tau(1+q_j)\le1\). A permutation placing one of the two zero
\(q_j\)'s in the first position has real part zero. Hence the actual
support height is **exactly zero**, and

\[
 g_\pi=q_{\pi(1)}[1-\tau(1+q_{\pi(2)})].
\]

Independent symbolic sums give

\[
 \begin{aligned}
 A&=1-\tau,& S&=(1+\varepsilon)(1-\tau),\\
 T&=3(1-\tau)+\varepsilon(1-2\tau),&
 D&=\varepsilon(3-4\tau),\\
 K&=2\tau\varepsilon,&
 t&=(1-\tau)+\varepsilon(1-2\tau).
 \end{aligned}
 \tag{36.9}
\]

The uniform inequality follows from three transparent estimates:

\[
 T\ge\frac32,\qquad D\ge\varepsilon,\qquad
 K^2\le\varepsilon^2.
\]

If \(\varepsilon>0\), these imply

\[
 \frac{K^2}{TD}\le\frac{2\varepsilon}{3}\le\frac13.
\]

If \(\varepsilon=0\), both \(K\) and \(D\) vanish and the same
inequality holds directly. Equality is attained at
\(\tau=\varepsilon=1/2\), with \(T=3/2,D=K=1/2\).

### Precise scope of the dominated-region claim

For \(\varepsilon<1/2\), this family satisfies
\(A>2S/3\) and \(t<2S\), so it lies outside the two simple sufficient
regions. The full parameter family is **not** contained in the sharper
unsettled region (36.5): its \(\varepsilon=1/2\) boundary is already
safe, and some interior parameters satisfy the stronger criterion
\(TD\ge t^2\). It does contain actual points strictly inside (36.5).

For example \(\tau=1/2,\varepsilon=1/10\) gives

\[
 A=t=\frac12,\quad S=\frac{11}{20},\quad
 T=\frac32,\quad D=K=\frac1{10},\quad
 TD=\frac3{20}<\frac14=t^2.
\]

Thus the separate \(1/3\) bound settles an actual example that cannot
be settled by \(|K|\le2t\) alone. I reported the introductory wording
distinction to the author; the displayed theorem and example are correct.

The \(1/3\) theorem is for the displayed spectral ordering and specified
real coefficient \(\eta\). It does not claim the same constant for
every base permutation or every support phase of those spectra.

