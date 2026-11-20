## Setup and coordinate conventions

Use the cost coordinates, oriented three-cycle convention, and nonic branches of the retained [A4 spectral-support companion](algebra_a4_spectral_support.md), Sections 1–2. An actual spectral cost means
\[
c_\pi=\operatorname{Re}\!\left(\eta\prod_{i=1}^4(a_i+b_{\pi(i)})\right).
\]
The ambient fourteen coordinates, in the order used for every vector below, are the permutation values
\[
1234,1243,1324,1342,1423,2134,2143,
2314,2341,2413,3124,3142,3412,4123.
\]
Here \(F\) is the normalized M8 cubic, \(\nabla F\) its gradient, \(H_F\) its Hessian, and \(e_0=(1,0,\ldots,0)\) the first coordinate vector. The matching forms and normalization
\(F(z)=\frac16\sum_M\epsilon(M)\ell_M(z)^3\)
are defined in Section 2, equations (5)–(6), of the retained [spectral-moduli source](../finite_and_spin_geometry/categorical_spectral_moduli_final.md); Sections 3–4 give the constant-cost projection and cubic lift. Thus the kernel vectors and numbered coordinates below use that explicit basis, not an unspecified choice. The finite conjugate-realization criterion is given in Section 6 of that source. These conventions do not assert an unrestricted MOC theorem.

## 2. The actual plane y=4x/3

The A4-invariant cost coordinates have class values

\[
c_{\mathrm{id}}=h_0,\quad c_{\mathrm{trans}}=h_0+x,
\quad c_{\mathrm{double}}=h_0+y,
\quad c_{\mathrm{four}}=h_0+x+y/2,
\quad c_{\mathrm{three},\pm}=h_0+3x/2\pm k.
\]

On the branch \(y=4x/3\), away from \((x,k)=(0,0)\), the unique
cubic lift has \(h_0=-3x/2\). At the zero point we choose this same
formula by continuity.
Let \(c_X\) be the lift for \((x,k)=(1,0)\), and let \(c_K\) be the
cost equal to \(+1,-1\) on the two oriented three-cycle classes and zero
on every other class. Exact differentiation gives

\[
\nabla F(c_K)=12\nabla F(c_X),\qquad H_F(c_X)c_K=0.
\tag{1}
\]

Consequently both complex lines

\[
m_\pm=c_X\pm\frac{i}{\sqrt{12}}c_K
\tag{2}
\]

lie on the singular locus of the cubic, and

\[
xc_X+kc_K
=\operatorname{Re}\bigl[(x-i\sqrt{12}k)m_+\bigr].
\tag{3}
\]

There is an explicit finite realization. Let
\(\omega=(-1+i\sqrt3)/2\), and take

\[
\boxed{
a=(0,1/2,-\omega^2,-\omega),\qquad
b=\left(-1,1,\frac{2\omega-1}{7},\frac{2\omega^2-1}{7}\right).
}
\tag{4}
\]

All twenty-four products satisfy exactly

\[
\boxed{
\frac79\prod_i(a_i+b_{\pi(i)})
=(c_X)_\pi+\frac{i}{\sqrt{12}}(c_K)_\pi.
}
\tag{5}
\]

The verifier checks every equality in \(\mathbb Q(\omega)\). A direct
derivation starts from \(C_{ij}=1+u_iv_j\), where
\(u=(0,1,\omega,\omega^2)\),
\(v=(0,2,2\omega^2,2\omega)\), then uses
\(a_i=u_i/(u_i+1)\), \(b_j=1/(v_j-1)\). The product of the row and column
factors is \(-14\), giving the factor \(7/9\) in (5).

Thus the whole real plane is obtained from different support directions
for one fixed pair of finite, noncollinear four-point complex spectra.
Equivalently, for \(c=xc_X+kc_K\), the explicit imaginary cost

\[
d=\sqrt{12}k\,c_X-\frac{x}{\sqrt{12}}c_K
\]

satisfies \(H_F(c)d=0\) and \(\nabla F(d)=\nabla F(c)\).

## 3. A component consisting generically only of border secants

On the branch \(x=0\), with \(yk\ne0\), the unique cubic lift has
\(h_0=0\). In the fourteen-coordinate basis from the prior campaign,
put \(c=yc_Y+kc_K\), with \(c_Y\) the vector for \((x,y,k)=(0,1,0)\).
Its exact Hessian kernel is spanned by

\[
v=(0,0,0,0,0,0,1,0,0,1,0,1,0,0),
\]

\[
w=(0,0,0,0,0,0,1,0,1,0,0,0,-1,1).
\]

The isotypic block determinants prove that this kernel has exactly dimension
two for \(yk\ne0\). On its vectors,

\[
\nabla F(sv+tw)=-(s^2+st+t^2)e_0,
\tag{6}
\]

whereas coordinate 1 of \(\nabla F(c)\) is \(k^2\ne0\). Therefore the
required gradient equality, with either sign, is impossible over the reals
or complexes. These points have no finite two-point secant representation,
including no actual conjugate spectral realization. They lie only in the
projected closure of the secant variety.

This result does not classify the degenerate axes \(yk=0\), nor the
quadratic branch \(4k^2=x(x-y)\).

Scaling the inversion-odd part sends \(k\mapsto sk\). On the generic
quadratic branch, with \(x(3y-4x)k\ne0\), the exact nonic factorization
shows that the scaled cost lies on the spectral closure only at
\(s=\pm1\). This rules out a naive proof that rescales odd parts and
silently preserves spectral realizability. On the actual plane in Section 2,
equation (3) does preserve finite actual realizability under that scaling.


## 5. Two preliminary lemmas for the root's simplex reduction

The root derived a sufficient full-unitary reduction to the following
inequality for probability vectors \(p,q\in\mathbb R_+^4\):

\[
\Phi(p,q):=\sum p_i^2+\sum q_i^2+4\sum p_iq_i-1
-4\sqrt{\prod p_i}-4\sqrt{\prod q_i}\ge0.
\tag{12}
\]

The root owns the unitary-to-simplex derivation. The two arguments below
were the initial partial results. The complete proof of (12), including
the boundary and all interior stationary-point types, is now in
algebra_tetrahedral_simplex_inequality.md.

### 5.1 Complementary marginals

Suppose \(p_i+q_i=1/2\) for every \(i\). Write
\(z_i=2(p_i-q_i)\), so \(|z_i|\le1\), \(\sum z_i=0\), and
\(p_i=(1+z_i)/4\), \(q_i=(1-z_i)/4\). Let \(s=\sum z_i^2\), and denote
the elementary symmetric polynomials by \(e_j\). Then \(e_2=-s/2\), and

\[
\begin{aligned}
\sqrt{\prod(1+z_i)}+\sqrt{\prod(1-z_i)}
&\le2\sqrt{1-s/2+e_4}\\
&\le2\sqrt{(1-s/4)^2}=2-s/2.
\end{aligned}
\tag{13}
\]

The first step is concavity of the square root applied to the two
nonnegative products; the second is \(e_4\le s^2/16\), which follows by
AM--GM on \(z_i^2\). Also \(s\le4\), so the last sign is correct.
Equation (13) is exactly (12) after substitution.

Equality includes the continuum

\[
p=(a,a,b,b),\qquad q=(b,b,a,a),\qquad a+b=1/2.
\tag{14}
\]

### 5.2 One vector supported on at most two coordinates

Assume \(p_3=p_4=0\), and put \(p_1=t,p_2=1-t\).
For fixed \(q\), minimizing its quadratic dependence on \(t\) over the
whole real line only lowers \(\Phi\). Put \(u=q_1q_2\), \(v=q_3q_4\).
The unconstrained minimum is exactly

\[
\Phi(p,q)\ge\frac12+6u-2v-4\sqrt{uv}.
\tag{15}
\]

Since \(q_1+q_2\ge2\sqrt u\),

\[
0\le v\le\frac{(1-2\sqrt u)^2}{4},\qquad 0\le\sqrt u\le1/2.
\]

The right side of (15) decreases with \(v\), so substituting its upper
bound gives

\[
\Phi(p,q)\ge8u\ge0.
\tag{16}
\]

The same statement holds with \(p\) and \(q\) exchanged and under all
coordinate permutations. In particular, every boundary stratum where one
probability vector has support at most two is completely settled.
