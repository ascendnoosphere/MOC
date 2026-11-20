## 1. Complete primal–dual argument: valid

**Location:** `organized/research/JOINT_CERTIFICATE_RANK.md:21–65`.

- **Nonempty compact allocation domain:** correctly imported rather than inferred from the seed or finite computations. [actual_fiber_allocation_independent_review.md](actual_fiber_allocation_independent_review.md), “explicitly establish P(z) nonempty,” supplies the actual-supported-input construction. Boundedness follows from \(0\leq\alpha\leq w\).
- **Coercivity:** independence and tracelessness of the eight gauges imply
  \[
  \lambda_{\min}(G(h))\leq-c\|h\|.
  \]
  Writing \(B(\alpha)=F(z)+\sum_e\alpha_eA_e\), compactness gives \(\|B(\alpha)\|_{\rm op}\leq K\), and therefore
  \[
  \lambda_{\min}(B(\alpha)+G(h))\leq K-c\|h\|.
  \]
  This establishes attainment of \(v(z)\) and excludes an infeasible family with unattained value zero.
- **Sion:** the compact set is correctly the density-matrix side. The other side need only be convex, not bounded. The one-compact-set corollary following Theorem 3.4 on printed page 174 applies.
- **Eliminating \(h\):** the supremum over \(h\in\mathbb R^8\) is \(+\infty\) unless every \(\langle Y,G_j\rangle=0\). On that annihilator, the remaining objective is continuous on a nonempty compact set; \(I/19\) establishes nonemptiness.
- **LP signs:** the displayed dual is correct:
  \[
  b=\mu-\nu-C^T\xi,\qquad
  \max_{\alpha\in P}b\cdot\alpha=\min(\mu\cdot w+\xi\cdot r).
  \]
  In particular,
  \[
  L_z-\langle Y,B(\alpha)\rangle
  =\mu\cdot(w-\alpha)+\nu\cdot\alpha+\xi\cdot(r+C\alpha).
  \]

There is **no Slater assumption or weak-infeasibility gap** in this derivation. Degenerate or lower-dimensional \(P\) causes no problem for finite LP duality.

## 2. Rank, parity, and scalar supports: valid

**Locations:** `organized/research/JOINT_CERTIFICATE_RANK.md:73–121`.

The normalization produces a compact product-cone slice. An extreme point of the minimizing face is also extreme in that slice, so the two-sided face perturbation proves
\[
\frac{r_Y(r_Y+1)}2+s\leq15,
\]
and hence \(r_Y\leq5\). This uses only the unconditional upper bound from the cited source, not its generic lower bound.

Parity averaging preserves every equation and the objective. Applying the face argument **within the block cone** gives
\[
\frac{r_+(r_++1)}2+\frac{r_-(r_-+1)}2+s\leq15,
\]
hence total rank at most six. The note correctly treats this as an **alternative** certificate guarantee, not a simultaneous strengthening of the full-cone rank-five guarantee.

The factor-coordinate maximum is **51**, attained at \((r_+,r_-)=(3,3)\). These are factor coordinates modulo orthogonal right action, not a count including scalar variables or imposed equations.

The scalar-support proof handles normalization correctly. More explicitly, for a normalized certificate \(x\), scalar kernel direction \(\delta\), and \(q=N(\delta)\), set
\[
x_\pm=\frac{x\pm\varepsilon\delta}{1\pm\varepsilon q}.
\]
Then
\[
x=\frac{1+\varepsilon q}{2}x_+
 +\frac{1-\varepsilon q}{2}x_-.
\]
The weights are positive for small \(\varepsilon\). Because \(Y\neq0\), these normalized points are distinct. Nonempty \(P\) is exactly what excludes negative certificates with \(Y=0\).

The exact independent-support counts are consistent:
\[
1,15,99,377,900,1344,1088,
\qquad \text{total }3824.
\]
They enumerate candidate independent supports; they do not claim every support admits a negative certificate.

## 3. New constructive rank-two-map lemma: valid in full generality stated

**Location:** `organized/research/JOINT_CERTIFICATE_RANK.md:169–185`.

The proof works for **any** real linear \(B:\operatorname{Sym}_k\to\mathbb R^m\) with \(\operatorname{rank}B\leq2\).

For a feasible rank-\(r\geq2\) factorization \(M=UU^T\), the restricted map has a nonzero symmetric kernel direction \(W\). The stated eigenvalue choices make \(I+tW\) PSD and singular:

- If \(\lambda_{\max}(W)>0\), then \(1-\lambda_i(W)/\lambda_{\max}(W)\geq0\).
- Otherwise \(W\neq0\) implies \(\lambda_{\min}(W)<0\); the other stated choice also gives nonnegative eigenvalues and at least one zero.

This covers positive semidefinite, negative semidefinite, indefinite, and repeated-eigenvalue degeneracies. Full column rank of \(U\) ensures the singularity strictly lowers rank.

Boundary cases are sound:

- \(k=0\): feasibility forces \(d=0\), with the unique empty zero matrix.
- \(k=1\): every PSD feasible matrix already has rank at most one.
- \(d=0\): the zero matrix is available immediately.
- \(d\neq0\): reduction cannot terminate at rank zero.

The stated bound of at most \(\max(k-1,0)\) reductions is correct. No compactness, closed-image assumption, or genericity is needed.

The rank-three-map counterexample is sharp: specifying \((M_{00},M_{01},M_{11})=(1,0,1)\) uniquely forces \(I_2\), excluding rank at most one.

