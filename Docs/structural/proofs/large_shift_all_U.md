# A generic large-scalar-shift theorem for MOC

This note derives a theorem with a complete proof below. Two other agents independently audited the variational and compactness steps; this is an informal mathematical audit, not formal verification. No claim of literature priority is made.

Let A=diag(a_1,...,a_n), B=diag(b_1,...,b_n), and let

    s_pi = sum_i a_i b_{pi(i)}.

Assume n>=3, the convex hull H of the s_pi is two-dimensional, each vertex of H comes from exactly one permutation, and each edge of H contains exactly two s_pi. The stronger finite condition that all s_pi are distinct and no three are collinear implies these hypotheses.

THEOREM. There exists R<infinity, depending on a,b, such that for every complex scalar s with |s|>R and every unitary U,

    det(sI+A+UBU*) belongs to conv{ product_i(s+a_i+b_{pi(i)}) : pi in S_n }.

Thus the conclusion is uniform over the entire unitary group and all supporting directions. The spectra a,b may have arbitrary distinct complex values subject to the stated finite genericity test.

Proof.

1. Remove the common Taylor terms.

Write C_U=UBU*. For complex t near zero,

    D_t(U)=det(I+t(A+C_U)).

Its expansion is

    D_t(U)=1+t tr(A+B)
      +(t^2/2)[(tr(A+B))^2-tr(A^2)-tr(B^2)]
      -t^2 tr(AC_U)+O(t^3).

Let c(t) be the first three U-independent terms in this formula and define G_t(U)=(D_t(U)-c(t))/t^2 for t!=0, extended at t=0 by

    G_0(U)=-tr(AC_U).

G_t is a polynomial in t with smooth polynomial coefficients in U and its conjugate. Hence G_t -> G_0 in C^2 on U(n), uniformly for all arguments of complex t. MOC for D_t is equivalent to MOC for G_t because subtraction of c(t) and division by t^2 apply to both the actual determinant and every permutation vertex.

2. Classify all maximizers at t=0.

Fix a supporting direction theta, and put f_{t,theta}(U)=Re(e^{-i theta}G_t(U)). At t=0,

    f_{0,theta}(U) = sum_{ij} c_ij |U_ij|^2,
    c_ij=-Re(e^{-i theta} a_i b_j).

The matrix Q=(|U_ij|^2) is doubly stochastic. Birkhoff's theorem implies its maximum is the maximum of the corresponding permutation assignment costs.

By the polygon hypotheses, the set of maximizing permutations is either a singleton {P}, or exactly two permutations {P,Q}.

If two permutations maximize, their relative permutation is one nontrivial cycle. Indeed, if it had two or more disjoint nontrivial cycles, the cost difference decomposes as a sum of the differences for those cycles. Every partial-cycle permutation has cost no greater than P, while the total difference is zero. Thus every cycle difference is zero, giving at least four maximizing permutations, a contradiction.

Any maximizing doubly stochastic matrix lies in the convex hull of the maximizing permutations, by applying a Birkhoff decomposition and noting that every nonmaximizing permutation has strictly smaller cost.

If the relative cycle has length at least three, no interior point (1-lambda)P+lambda Q with 0<lambda<1 is unistochastic: after relabeling P=I on the cycle, two consecutive rows have supports {j,j+1} and {j+1,j+2}, hence exactly one common nonzero column. They cannot be orthogonal. Therefore the maximizing unitaries are precisely the two permutation tori.

If the relative cycle is a transposition, all maximizing unitaries are precisely the zero-pattern manifold M consisting, after permutation, of one arbitrary 2x2 unitary block and n-2 scalar unitary blocks. In the singleton case, M is one permutation torus.

3. Every leading maximum is strict in directions normal to its maximum manifold.

At a permutation P, the second derivative in a skew-Hermitian off-diagonal direction K is

    2 sum_{i<j}|K_ij|^2 [cost(P_(ij))-cost(P)].

In the singleton case all bracketed quantities are negative. In the two-permutation case with a cycle of length >=3 they are again all negative, since no transposition is maximizing. The Hessian is consequently negative definite normal to each permutation torus.

For a transposition face, let E be the union of the supports of the two optimal permutation matrices, and let delta>0 be the smallest assignment-cost gap among the other finitely many permutations. For any doubly stochastic Q0, a Birkhoff decomposition gives

    h - sum c_ij Q0_ij >= (delta/n) sum_{(i,j) not in E} Q0_ij,

because each nonoptimal permutation has at most n entries outside E, and the optimal ones have none.

At U in M, a tangent vector normal to M is KU with K supported off the blocks. Then KU is supported off E and ||KU||_F=||K||_F. Applying the preceding gap estimate to exp(rK)U gives

    Hess f_{0,theta}(U)[KU,KU] <= -(2delta/n)||K||_F^2.

Thus the Hessian is uniformly negative definite on the normal bundle of the compact manifold M.

4. Exact normal stationarity persists for all t and all directions.

For each manifold above, A and C_U are block diagonal with either only singleton blocks, or one 2x2 block and singleton blocks. For a normal tangent direction KU, the variation [K,C_U] is off the blocks. The adjugate of I+t(A+C_U) is block diagonal, including when the matrix is singular, because the adjugate is a polynomial in that matrix. Therefore

    d/dr D_t(exp(rK)U)|_(r=0)
      =t tr(adj(I+t(A+C_U))[K,C_U])=0.

The same exact normal stationarity holds for f_{t,theta}, for every t and theta.

5. Uniform stability of the maximum set.

Equip U(n) with the bi-invariant Riemannian metric induced by the real Frobenius inner product on skew-Hermitian matrices. Each maximum set above is either one compact block-unitary coset, one compact permutation torus, or a disjoint union of two compact permutation tori. In particular it is a finite disjoint union of smooth compact submanifolds.

The following elementary compact-manifold lemma applies. Suppose a smooth f_0 on a compact Riemannian manifold has maximum set M, a finite disjoint union of compact smooth submanifolds, with negative-definite Hessian on the normal bundle. If a C^2-close function f is exactly critical in all directions normal to M at every point of M, then every global maximum of f lies on M.

To prove the lemma, use compactness to obtain a uniform negative normal-Hessian bound and a tubular neighborhood. Along each short normal geodesic from M, the first derivative at its start is zero and the second derivative stays strictly negative. Thus every point off M in the tube has smaller value than its foot point. On the compact complement of a smaller tube, f_0 is bounded below its maximum by a fixed positive gap. C^0 closeness prevents f from attaining its maximum there.

For each fixed theta_0, apply this lemma to f_{0,theta_0}, using the fixed maximum manifold M classified above. Uniform C^2 closeness holds for (t,theta) near (0,theta_0), and exact normal stationarity on this same M holds for all such parameters. Consequently all global maximizers of f_{t,theta} lie on this M for sufficiently small |t| and |theta-theta_0|.

On a permutation torus, D_t equals its corresponding permutation vertex. On a 2x2 block manifold, the elementary 2x2 determinant identity gives D_t as a convex combination of the two associated permutation vertices. Therefore

    max_U f_{t,theta}(U) <= max_pi f_{t,theta}(P_pi).

Cover the compact circle of theta by finitely many such neighborhoods and choose the smallest permitted |t| radius. This proves all supporting inequalities simultaneously for every U and every sufficiently small nonzero complex t.

Finally put t=1/s and multiply all values by s^n. This proves the stated theorem.

6. Genericity is substantial rather than a special spectral line/circle condition.

The stronger sufficient hypothesis, distinct s_pi with no three collinear, holds on an open dense subset of C^(2n). For distinct permutations P,Q, the difference s_P-s_Q is a nonzero complex bilinear polynomial in a,b. For three distinct permutations, their collinearity condition is a real-algebraic condition. It cannot hold identically: otherwise the ratio (s_R-s_P)/(s_Q-s_P), a holomorphic rational function on its domain, would always be real and hence a real constant. That would force the two permutation-matrix differences to be real proportional. Three distinct vertices of the Birkhoff polytope are not collinear, so this is impossible. A finite union of these proper real-algebraic exceptional sets has empty interior.

Limits of the result.

The proof yields existence of R; no explicit numerical value or asserted computable bound for R is supplied in this note. The theorem changes the spectra by adding a large common scalar to A; it does not imply MOC for the original unshifted pair. No assertion is made about trace-assignment polygons failing the hypotheses, and no assertion of novelty is made until a literature check is complete.

7. An exact four-dimensional example of the finite hypotheses.

Take

    a=(0,1,i,2+3i),
    b=(0,2+i,-1+2i,3-i).

Both spectra have four distinct entries and are neither collinear nor concyclic. In counterclockwise order, the vertices of the trace-assignment polygon are

    -9+3i, -5, 1-2i, 11+8i, 7+11i, 1+13i.

The corresponding unique permutations, written as the list (pi(1),...,pi(4)), are

    (4,1,2,3), (2,4,1,3), (2,4,3,1),
    (3,2,1,4), (1,3,2,4), (1,3,4,2).

For each consecutive oriented edge v->w, the exact cross product

    cross(w-v, s_pi-v)

is zero for precisely the two displayed endpoint permutations and is positive for every other permutation. The six minimum positive cross products are respectively

    5, 10, 10, 5, 10, 10.

There are two coincidences among interior trace points; the theorem does not prohibit them, since it only needs uniqueness on the exposed boundary. These finite assertions are verified entirely with integer arithmetic by verify_large_shift_example.py, with all 24 trace points and the six edge certificates recorded in large_shift_example_certificate.json.

The theorem therefore applies to this pair in dimension four: for every sufficiently large complex s, every unitary U satisfies the MOC enclosure for diag(s,s+1,s+i,s+2+3i) and diag(0,2+i,-1+2i,3-i). No numerical threshold for "sufficiently large" is claimed.
