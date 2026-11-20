## 1. Möbius invariance: exact statement and proof

I read all three requested documents. The wrapped file is an **exact derivative**: deleting its newlines reproduces `/home/dell/Desktop/MOC/metaproof.txt` byte-for-byte.

Write
\[
D_{a,b}(U)=\det(\operatorname{diag}a+U\operatorname{diag}b\,U^*),
\qquad
z_\pi(a,b)=\prod_i(a_i+b_{\pi(i)}).
\]

### Lemma 1 — Pole-free Möbius invariance

Let
\[
f(t)=\frac{\alpha t+\beta}{\gamma t+\delta},
\qquad \Delta=\alpha\delta-\beta\gamma\ne0.
\]
Assume
\[
\gamma a_i+\delta\ne0,\qquad \delta-\gamma b_j\ne0
\]
for every \(i,j\). Set
\[
a'_i=f(a_i),\qquad b'_j=-f(-b_j).
\]
Then, for every \(U\in U(n)\),
\[
D_{a',b'}(U)=\kappa D_{a,b}(U),\qquad
z_\pi(a',b')=\kappa z_\pi(a,b),
\]
where
\[
\kappa=
\frac{\Delta^n}
{\prod_i(\gamma a_i+\delta)\prod_j(\delta-\gamma b_j)}
\ne0.
\]
Consequently determinant-convex-hull membership is equivalent before and after transformation.

**Proof.** Put \(A=\operatorname{diag}a\), \(C=-U\operatorname{diag}b\,U^*\). Direct multiplication gives
\[
(\gamma A+\delta I)\,[f(A)-f(C)]\,(\gamma C+\delta I)
=\Delta(A-C).
\]
Indeed the numerator is
\[
(\alpha A+\beta I)(\gamma C+\delta I)
-(\gamma A+\delta I)(\alpha C+\beta I)
=\Delta(A-C).
\]
Taking determinants proves the matrix identity. The scalar identity
\[
f(x)-f(y)=\frac{\Delta(x-y)}
{(\gamma x+\delta)(\gamma y+\delta)}
\]
proves the vertex identity, with the same multiplier independently of \(\pi\). Multiplication by a nonzero complex number preserves real convex combinations. \(\square\)

This is **not** the assertion that a Möbius map preserves convex hulls. The determinant and every vertex undergo one common complex scaling.

### Lemma 2 — Projective extension, including poles

There is an exact homogeneous formulation valid even at poles.

Represent the points \(a_i\) and \(c_j=-b_j\) by nonzero pairs
\[
a_i=[x_i:y_i],\qquad c_j=[r_j:s_j].
\]
Let \(X,Y,R,S\) be the corresponding diagonal matrices, and define
\[
\mathcal D(U)=\frac{\det(XUS-YUR)}{\det U},
\qquad
\mathcal z_\pi=\prod_i(x_i s_{\pi(i)}-y_i r_{\pi(i)}).
\]
For finite points, using \(y_i=s_j=1\), these are precisely \(D_{a,b}(U)\) and \(z_\pi(a,b)\).

Apply the same invertible matrix
\[
M=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}
\]
to every homogeneous pair. Then
\[
X'US'-Y'UR'=\Delta(XUS-YUR),
\]
so
\[
\mathcal D'(U)=\Delta^n\mathcal D(U),\qquad
\mathcal z'_\pi=\Delta^n\mathcal z_\pi.
\]
Rescaling individual homogeneous representatives likewise multiplies every quantity by one common nonzero factor. Thus homogeneous hull membership is well-defined and Möbius invariant **at infinity as well**. \(\square\)

**Continuity interpretation.** Approximate projective points by finite points and use convergent homogeneous representatives. If membership holds along the approximation, choose convex weights in the compact simplex \(\Delta_{n!-1}\); a convergent subsequence supplies weights proving limiting membership.

One must distinguish this from assigning an ordinary finite determinant to a matrix with an infinite eigenvalue. At a pole, either use the homogeneous statement or take limits back in the original finite spectral coordinates.

---

## 2. What can actually be normalized?

### Lemma 3 — Three-point normalization

If \(a_1,a_2,a_3\) are distinct finite complex numbers, define
\[
r=\frac{a_3-a_2}{a_2-a_1},\qquad
f(t)=\frac{r(t-a_1)}{r(t-a_1)-(t-a_3)}.
\]
Then
\[
f(a_1)=0,\qquad f(a_2)=\tfrac12,\qquad f(a_3)=1.
\]
The map is nondegenerate because the numerator and denominator have no common zero.

Thus any quadruple with at least three distinct values can be projectively normalized to
\[
(0,\tfrac12,1,z),
\]
after relabeling, initially allowing \(z=\infty\).

If four values are distinct and \(z=\infty\), compose with
\[
g(t)=\frac{t-\frac12}{\frac32t-1}.
\]
This permutes \(0,\frac12,1\) and sends \(\infty\) to \(2/3\). After relabeling, all four normalized values are finite. With exactly three distinct values, the fourth image repeats one of the three finite targets.

**Exceptions and scope.**

* Quadruples with fewer than three distinct values cannot have this exact normal form: Möbius maps preserve multiplicities and distinctness.
* A normalizing map may have a pole at some \(-b_j\). The projective lemma handles this formally; for an ordinary finite-spectrum proof, approximation handles it.
* For a dense set of pairs \((a,b)\), a chosen three-point normalization avoids every relevant pole. Therefore a theorem for **all finite \(z\) and all finite \(b'\)** in the normalized form would imply unrestricted MOC4 by continuity. Explicitly, the maximum support gap is continuous in \(a,b,U,\eta\), being a finite maximum minus a determinant expression.

**Important limitation:** normalization does not fix the other spectrum. The transformed \(b'\) is arbitrary subject to the transformation; there is no argument here reducing it to
\[
(i,-i,1+i,-1+2i).
\]
Consequently the 68-ray family, even after exact certification, does not imply unrestricted MOC4.

---


## 5. Finite support fans: what remains finite for arbitrary \(b\)

For fixed arbitrary \(b\) and \(a=(0,\frac12,1,z)\), every vertex has the form
\[
z_\pi(z)=A_\pi(b)z+B_\pi(b).
\]
With \(w=\eta z\), its support value is linear in
\[
\theta=(\Re w,\Im w,\Re\eta,\Im\eta)\in\mathbb R^4.
\]
Therefore the support fan is polyhedral and finite **for each fixed \(b\)**. On a pointed normal cone, raywise PSD certificates combine linearly to certify the whole cone; cones with lineality require additional treatment of both directions of that lineality.

This validates the finite-fan mechanism used for the fixed family in `organized/research/SINKHORN_SOS_CERTIFICATE_ROUTE.md:119–180`.

What it does **not** provide is finitely many fixed certificates covering all \(b\). The coefficient vectors and ray directions vary with \(b\). Their combinatorial changes admit a finite semialgebraic stratification, obtained from rank and determinant-sign conditions on the 24 coefficient vectors. But finite combinatorial types do not produce PSD Grams on those parameter strata.

The missing certificate would have to be parameter-dependent, with polynomial identities and PSD verified throughout each stratum—or follow universally from (PM).

