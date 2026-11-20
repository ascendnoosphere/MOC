# A precise generic target and the forced quadratic-block degeneracies

These are reductions, not a proof of the remaining support inequality. They clarify which singular cases can legitimately be handled by continuity, and which matrix must actually be completed.

## 1. A dense strict-support class is enough for unrestricted MOC4

It is sufficient to prove the original support inequality for all data with:

1. all relevant spectral entries and pair sums away from the poles used in the chosen chart;
2. all 24 complex permutation products \(z_\pi=\prod_i(a_i+b_{\pi(i)})\) distinct;
3. a support direction \(\eta\in S^1\) with a unique maximizing permutation.

After permuting \(b\), the unique maximizer is identity and
\[
 \Delta_\pi=h-\Re(\eta z_\pi)>0\qquad(\pi\ne\mathrm{id}).
\]

**Density proof.** For distinct permutations \(\pi,\sigma\), the polynomial \(z_\pi-z_\sigma\) is not identically zero: choose \(i\) with \(\pi(i)\ne\sigma(i)\) and compare the coefficient of \(a_{[4]\setminus i}b_{\pi(i)}\). Thus the distinct-product condition excludes only finitely many proper polynomial zero sets. Distinct entries, nonzero pair sums and finite normalization denominators are likewise dense open conditions. For a fixed pair with distinct products, ties in real support values occur only at the finitely many directions perpendicular to a product difference. Perturbing the direction avoids them.

For arbitrary data, choose such generic spectra and directions converging to them, with the unitary held fixed. Both
\[
 \Re\bigl(\eta\det(D_a+UD_bU^*)\bigr)
 \quad\text{and}\quad
 \max_\pi\Re(\eta z_\pi)
\]
are continuous (the second is a finite maximum). The inequality passes to the limit. This addresses singular and duplicate-product data **only after** the generic inequality is proved. It does not prove that inequality.

In particular, a universal construction may assume every nonidentity permutation gap is strictly positive. One need not solve singular Gram equations first and mistake them for the principal obstacle.

## 2. Positive definiteness of the forced quadratic block

Use the real \(4\times3\) Hadamard isometry \(Y\) with \(Y^TY=I\), \(Y^Te=0\), where \(e=(1,1,1,1)^T/2\). The already-verified quadratic gap identity is
\[
 t^TAt=4\sum_{i<j}\Delta_{(ij)}|(YTY^T)_{ij}|^2.
\]
If all six transposition gaps are positive, vanishing implies every off-diagonal entry of \(Q=YTY^T\) is zero. But \(Qe=0\), so a diagonal such \(Q\) is zero; multiplying by \(Y^T,Y\) then gives \(T=0\). Hence
\[
 \boxed{A\succ0.}
\]
Also \(g=\tfrac14\sum_{i<j}\Delta_{(ij)}>0\). Thus both invertibility and leading positivity are genuinely available on the dense strict-support class.

## 3. Exact kernel dimension at any nonnegative support data

Let \(H\) be the graph on four vertices whose edges are the pairs with \(\Delta_{(ij)}=0\). Write \(m=|E(H)|\) and let \(c(H)\) count all connected components, including isolated vertices.

The kernel of \(A\) consists of Hermitian \(Q\) with \(Qe=0\) and off-diagonal support contained in \(H\). Assign one real part and one imaginary part to each edge. The real row-sum equations uniquely determine the four real diagonal entries. The imaginary row-sum equations say that the oriented imaginary edge flow has zero divergence; the incidence matrix has rank \(4-c(H)\). Therefore
\[
 \boxed{\dim\ker A=2m-4+c(H),\qquad
 \operatorname{rank}A=13-2m-c(H).}
\]
Possible ranks are \(9,8,7,6,5,4,2,0\), depending on the zero-gap graph. This classification is a quadratic-block fact, not a completion theorem.

