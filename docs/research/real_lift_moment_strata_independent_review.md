### 1. Rank-two moment line and congruence

`organized/research/REAL_LIFT_MOMENT_STRATA.md:7–18` is correct:

- \(\dim\operatorname{Sym}_2=3\), so rank \(B=2\) gives a one-dimensional kernel.
- An affine solution line exists **only after** checking \(d\in\operatorname{im}B\).
- With \(K'=KS\), moment coordinates transform by \(M'=S^{-1}MS^{-T}\); the kernel direction transforms by the same congruence. Sylvester’s law preserves inertia. Since a generator can also be negated, the intrinsic classification is definite/indefinite/singular-semidefinite, rather than a preferred positive sign.

The rank-reduction argument in `organized/research/JOINT_CERTIFICATE_RANK.md:169–181` is valid, including semidefinite perturbation directions and zero targets. Consequently, PSD feasibility really is equivalent to rank-at-most-one feasibility here.

### 2. Definite direction and the target-range prerequisite

The whitening proof in `organized/research/REAL_LIFT_MOMENT_STRATA.md:24–31` works for **every compatible target**, not merely the example:
\[
M(t)=W^{1/2}(N+tI)W^{1/2}.
\]
The two extremal eigenvalue shifts give PSD and NSD singular matrices. Coincident eigenvalues force \(M_0\in\mathbb RW\), hence \(d=0\). Otherwise both matrices are nonzero rank one.

The range condition is sharp and cannot be removed: for example,
\[
B(M)=(M_{00}-M_{11},M_{01},0,\ldots,0)
\]
has rank two and definite kernel direction \(I_2\), but a target with nonzero third coordinate has no preimage.

The real and complex critical-point conclusions at `organized/research/REAL_LIFT_MOMENT_STRATA.md:33–41` also follow correctly from cubic polarization.

### 3. Singular and indefinite directions, including degeneracies

The complete singular classification at `organized/research/REAL_LIFT_MOMENT_STRATA.md:76–84` is correct. For
\[
M(t)=\begin{pmatrix}a+t&b\\b&c\end{pmatrix},
\]
the PSD conditions are exactly:

- \(c>0:\ t\ge b^2/c-a\);
- \(c=0,b=0:\ t\ge-a\);
- \(c=0,b\ne0\), or \(c<0:\) infeasible.

The indefinite-direction discussion at `organized/research/REAL_LIFT_MOMENT_STRATA.md:74` correctly requires non-strict inequalities. A repeated determinant root must **not** be discarded: with
\[
M_0=\operatorname{diag}(1,0),\qquad
W=\begin{pmatrix}0&1\\1&0\end{pmatrix},
\]
the determinant is \(-t^2\), and the PSD feasible set is the singleton \(t=0\). Taking \(M_0=0\) gives a feasible zero-matrix singleton; taking \(M_0=\operatorname{diag}(-1,0)\) gives no PSD point despite the same determinant polynomial. These cases agree with the note’s prescribed diagonal tests.

For indefinite \(W\), the determinant polynomial cannot be identically zero because its quadratic coefficient is \(\det W<0\). Identically zero determinants do occur in the singular-direction cases already covered.


### 6. All-phase identity and scope

`organized/research/REAL_LIFT_MOMENT_STRATA.md:65–70` is correct for any real homogeneous cubic. Writing \(Q=\nabla\Phi\), criticality gives \(Q(f)=Q(y)=g\) and \(H_fy=0\), so
\[
Q(rf+sy)=r^2g+s^2g.
\]
The imaginary part of \(Q((r-is)(f+iy))=0\) gives \(H_{f'}y'=0\). This includes \(r=s=0\); fixed-modulus phase changes use \(r^2+s^2=1\), and therefore preserve the gradient exactly.

