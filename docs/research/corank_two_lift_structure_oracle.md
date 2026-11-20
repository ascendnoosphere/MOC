## 1. Original-source ingredients

The necessary additional ingredient is the original theorem that the gradient/duality map sends \(\operatorname{Sec}(M_8)\) dominantly to \(N'_8\).

Its active proof constructs the affine diagram
\[
X\times X\longrightarrow \widehat{N_8},
\qquad
(p,q)\longmapsto p+q\longmapsto G(p+q),
\]
commutative up to a nonzero scalar. The authors prove commutativity using the unique relevant irreducible representation in the degree-two piece. Thus this is an affine polynomial-map statement, not just a heuristic about secant lines:

- `organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:864–867`
- active proof: `organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:919–954`.

The source establishes
\[
\dim\operatorname{Sec}(M_8)=11,\qquad \dim N_8=9,
\]
using the pencil of quadrics through eight general points and the contracted secant line:
`organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:1190–1201`.

Consequently,
\[
\dim S=12,\qquad \dim\overline{G(S)}\le10.
\]

The identification \(X=\{G=0\}\), including affine cones, is the original singular-locus theorem:
`organized/research/external/m8_hmsv/0809.1233v1/8pts-090708.tex:245–255`.

The audited coordinate bridge transports these statements to the **actual Fourier cubic**, rather than another abstract 14-dimensional representation:
`organized/research/HMSV_COMPATIBILITY.md:48–56`.

**The suppressed septic proposition is not used.**

---

## 2. Proof of the universal rank bound

### Step A: every Hessian on the secant cone has rank at most twelve

At a general smooth \(f\in S\), the derivative of \(G|_S\) is
\[
d(G|_S)_f=H_f|_{T_fS}.
\]
Its rank is at most ten because \(G(S)\) has dimension at most ten. Since \(\dim T_fS=12\),
\[
\dim(\ker H_f\cap T_fS)\ge2.
\]
Therefore \(\operatorname{rank}H_f\le12\) generically on \(S\).

All \(13\times13\) minors of \(H_f\) are polynomial functions of \(f\). Since \(S\) is irreducible, their generic vanishing implies
\[
\boxed{\operatorname{rank}H_f\le12\quad\text{for every }f\in S.} \tag{1}
\]

This is stronger than the determinant-square assertion: it gives the vanishing of **all** \(13\times13\) minors on \(S\).

### Step B: differentiate those minors at a rank-twelve point

Fix any \(f\in S\) with \(\operatorname{rank}H_f=12\). Choose an invertible matrix \(P=(U,K)\), where \(K\) spans the kernel, such that
\[
P^TH_fP=
\begin{pmatrix}
C&0\\
0&0
\end{pmatrix},
\qquad \det C\ne0.
\]

For a tangent vector \(h\in T_fS\), write
\[
P^TH_hP=
\begin{pmatrix}
*&*\\
*&L(h)
\end{pmatrix},
\qquad L(h)=K^TH_hK.
\]

For each \(i,j\in\{1,2\}\), take the \(13\times13\) minor consisting of the first twelve rows and row \(12+i\), and the first twelve columns and column \(12+j\). By (1), this minor vanishes identically on \(S\). Its derivative at \(f\) in direction \(h\) is
\[
\det(C)\,L(h)_{ij}.
\]
Hence
\[
\boxed{K^TH_hK=0\qquad(h\in T_fS).} \tag{2}
\]

This argument remains valid when \(f\) is singular on \(S\): use its Zariski tangent space. Since \(\dim T_fS\ge12\),
\[
\operatorname{rank}\bigl(h\mapsto K^TH_hK\bigr)\le14-\dim T_fS\le2. \tag{3}
\]

### Step C: identify this map with the adjoint of \(B_f\)

Write
\[
G(K(u,v))=b_0u^2+b_1uv+b_2v^2,\qquad B_f=(b_0,b_1,b_2).
\]
The constant symmetric third derivative of the cubic gives
\[
K^TH_hK=
\begin{pmatrix}
2\langle b_0,h\rangle&\langle b_1,h\rangle\\
\langle b_1,h\rangle&2\langle b_2,h\rangle
\end{pmatrix}. \tag{4}
\]
Thus the linear map in (3) and \(B_f\) have the same rank. This proves the theorem.

An explicit structural identity obtained along the way is
\[
\boxed{\operatorname{im}B_f\subseteq(T_fS)^\perp.} \tag{5}
\]

### Why this retains the actual-real-lift conditions

For actual spectra, let \(x\in X\) be the Fourier coordinate vector of
\(\eta\,\mathrm{product\text{-}array}(a,b)\). Then
\[
f=\Re x=\frac{x+\bar x}{2}\in S.
\]
Therefore the theorem applies directly.

More generally, if real \(f,y\) satisfy the full lift equations
\[
H_fy=0,\qquad G(y)=G(f),
\]
then \(G(f+iy)=0\), so \(f+iy\in X\) and again \(f\in S\). No actual-real-lift condition was replaced by a fake-secant assumption.

---

## 3. Generic rank, exceptional strata, and an exact normal form

### Generic rank is exactly two

I reconstructed the actual example from its spectra using the current Fourier cubic:
\[
a=(-1-2i,\,2+2i,\,-1+2i,\,0),\qquad
b=(-2-i,\,-2+i,\,1,\,2+2i),\qquad \eta=1.
\]

With the kernel basis in the existing record, the \(B_f\) minor using rows \(0,1\) and columns \(0,1\) is exactly
\[
-\frac{143403915106425600}{3680082049519}\ne0.
\]
The Hessian has rank twelve. Thus rank two occurs on a nonempty Zariski-open subset of the corank-two secant chart.

The existing exact kernel and restriction matrix are at
`organized/research/joint_certificate_rank/exact_real_lift.json:20–150`.
I independently reconstructed and compared both matrices exactly.

### Useful exceptional-stratum consequences

On the corank-two chart, \(g:=G(f)\ne0\). Indeed, if \(G(f)=0\), then \(f\in X\). Since \(G\) vanishes on the six-dimensional affine cone \(X\), \(H_f\) kills \(T_fX\), giving \(\operatorname{rank}H_f\le8\), a contradiction.

Consequently:

- **Rank \(B_f=2\):** equation (5) forces \(\dim T_fS=12\), so \(S\) is smooth at \(f\). Moreover
  \[
  \operatorname{im}B_f=(T_fS)^\perp,
  \]
  and \(g\in\operatorname{im}B_f\), since \(\Phi\) vanishes on \(S\). Thus consistency of the moment equations is automatic here.
- **Rank \(B_f=1\):** lifting requires \(g\in\operatorname{im}B_f\), followed by one quadratic sign test.
- **Rank \(B_f=0\):** no lift is possible on this chart because \(g\ne0\).
- If \(S\) is singular at an **actual** corank-two point, necessarily
  \[
  \operatorname{rank}B_f=1,\qquad \dim T_fS=13.
  \]

I have **not** established whether that last stratum is nonempty, nor excluded rank one at smooth secant points. These are occurrence questions, not gaps in the rank bound or lifting algorithm.

### Computable binary-quadratic normal form

In the rank-two case choose any \(n\in\operatorname{im}B_f\) independent of \(g\). Solving three two-column linear systems gives binary quadratics \(q,r\) such that
\[
\boxed{G(K(u,v))=g\,q(u,v)+n\,r(u,v).} \tag{6}
\]
The entire real-lifting problem becomes
\[
\boxed{q(u,v)=1,\qquad r(u,v)=0.} \tag{7}
\]

This normal form requires no expansion of the septic or nonic.

---

## 4. Exact real-lift algorithm

For real algebraic input \(f\in S\) with Hessian rank twelve:

1. Compute \(g=G(f)\), a real kernel basis \(K\), and \(B_f\).
2. Apply the appropriate branch below.

### Rank two

Construct (6). The nonzero binary quadratic \(r\) has at most two real projective zero directions.

For each real direction \([u:v]\) satisfying \(r=0\):

- if \(q(u,v)\le0\), discard it;
- if \(q(u,v)>0\), return
  \[
  y=\pm\frac{K(u,v)}{\sqrt{q(u,v)}}.
  \]

This finds **all** real lifts. In particular there are at most four.

It handles double roots, roots at infinity, and directions where \(q=0\). For rational \(f\), only quadratic equations and square roots are required; the resulting coordinates have algebraic degree at most four.

### Rank one

First test \(g\in\operatorname{im}B_f\). If not, reject.

Otherwise write
\[
G(K(u,v))=g\,q(u,v).
\]
A lift exists exactly when \(q\) has a positive direction. Choose such a direction and rescale it to \(q=1\).

### Rank zero

Reject on this chart.

Thus rank-one degeneracies are covered, not silently discarded.

---

## 5. Exact normal form for the actual example

These are explicit certificates accompanying the proof, not its evidential basis.

Use the recorded kernel basis with \(u=y_{12}\), \(v=y_{13}\), and choose \(n=B_f[:,0]\).

### Actual spectra above

Exact reconstruction gives
\[
q(u,v)=\frac{v(103345u-422661v)}{460946784},
\]
\[
r(u,v)=\frac{(6u-71v)(311u-1107v)}{1866}.
\]

The two projective directions are
\[
(u,v)=(71/6,1),\qquad (1107/311,1),
\]
and
\[
q(71/6,1)=\frac1{576}>0,\qquad
q(1107/311,1)=-\frac{23}{193442}<0.
\]
Hence the only real lifts are
\[
\boxed{y=\pm K(284,24).}
\]

This recovers the positive moment endpoint already recorded at
`organized/research/joint_certificate_rank/exact_real_lift.json:174–195`.


## 6. Verification of the general PSD rank-reduction observation

The observation is correct with **“rank at most one”**, rather than necessarily nonzero rank one.

**Lemma.** Let
\[
\mathcal B:\operatorname{Sym}_k(\mathbb R)\to W,
\qquad \operatorname{rank}\mathcal B\le2.
\]
Then
\[
\exists M\succeq0:\mathcal B(M)=g
\iff
\exists x\in\mathbb R^k:\mathcal B(xx^T)=g.
\]

**Proof.** Start from a feasible \(M\) of rank \(r\ge2\). Symmetric perturbations supported on \(\operatorname{range}M\) form a space of dimension
\[
r(r+1)/2\ge3.
\]
Therefore a nonzero supported symmetric \(\Delta\) satisfies \(\mathcal B(\Delta)=0\).

On the range of \(M\), write \(M=UDU^T\), \(D\succ0\), and \(\Delta=URU^T\). Set
\[
E=D^{-1/2}RD^{-1/2}\ne0.
\]
Reverse its sign if necessary so that \(\lambda_{\min}(E)<0\), and take
\[
t_*=-1/\lambda_{\min}(E).
\]
Then \(M+t_*\Delta\succeq0\), has smaller rank, and has the same moments. Repeat. After at most \(r-1\) steps the rank is at most one. ∎

Qualifications:

- If \(g\ne0\), the final matrix cannot be zero.
- If \(g=0\), zero may be the **only** feasible matrix; for example, \(\mathcal B(M)=\operatorname{tr}M\).
- Do not add an extra trace normalization and continue invoking the rank-two bound: it can add an independent constraint.

Combined with the theorem, this proves that the PSD moment relaxation is **universally exact on the corank-two secant chart**, including all rank degeneracies of its restriction map.

---

