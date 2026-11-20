# An exact dimension reduction to rectangular compressions

No assertion in this note assumes that a compression of a normal matrix is
normal. That property generally fails. The compressed determinant is kept
as a separate, precisely stated convex-hull problem.

## Rectangular compression conjecture

For coisometries X in C^(r by m), Y in C^(r by n), so that XX*=YY*=I_r,
write CMC(r;m,n) for the assertion

    det(X diag(a) X* + Y diag(b) Y*)

belongs to the real convex hull of

    product_{k=1}^r (a_{i_k} + b_{j_k}),

where the i_k are distinct and the j_k are distinct. The matching between
the two selected index sets is allowed to vary. A common matching law is
the stronger assertion that one probability law, depending only on X,Y,
works simultaneously for all a,b.

## Exact rank reduction theorem

Let A = diag(a_1,...,a_r,c,...,c) have dimension n and suppose temporarily
that every a_i-c and c+b_j is nonzero. Put

    alpha_i = 1/(a_i-c), beta_j = 1/(c+b_j),
    X = U[1:r,:],
    Gamma = product_{i=1}^r(a_i-c) product_{j=1}^n(c+b_j).

Then the exact identity is

    det(A + U diag(b) U*)
       = Gamma det(diag(alpha) + X diag(beta) X*).        (1)

Proof: write D = diag(a_1-c,...,a_r-c,0,...,0) and
E = U diag(c+b) U*. The matrix determinant lemma gives

    det(E+D) = det(E) det(I_r + X diag(beta) X* D_r)
             = det(E) det(D_r)
                        det(D_r^(-1)+X diag(beta) X*),

which is (1). This proof is purely algebraic and makes no normality claim
about the compression.

For every injection j:[r]->[n], the same scalar Gamma gives

    Gamma product_{i=1}^r(alpha_i+beta_{j(i)})
       = product_{i=1}^r(a_i+b_{j(i)})
           product_{k not in image(j)}(c+b_k).             (2)

The right side is exactly the corresponding full matching product. The
remaining equal eigenvalues c make the order of the unused b indices
irrelevant. Multiplication by a fixed complex scalar is a real linear map,
so (1)-(2) transport a convex combination without changing its weights.
All excluded poles and repetitions follow by continuity.

## Equivalence in every dimension

For n>=2,

    MOC(n) is equivalent to CMC(n-1;n-1,n).                (3)

To prove the forward implication, let X be any (n-1) by n coisometry and
complete it to a unitary U. Apply MOC to diag(alpha_1,...,alpha_(n-1),M)
and U diag(beta) U*. Divide the determinant and all matching vertices by
the positive real M and let M tend to infinity. The resulting determinant
is precisely det(diag(alpha)+X diag(beta) X*); compactness of the finite
probability simplex preserves its convex representation. A square
coisometry in the first argument is unitary and may be absorbed by a change
of coordinates, giving the stated CMC formulation.

For the reverse implication, apply (1)-(2) with r=n-1 and c=a_n.

More generally, MOC(n) implies CMC(r;r,n) for every r<=n by the same leading
coefficient limit with n-r large diagonal entries. A theorem for CMC(r;r,n)
therefore proves MOC(n) whenever A has n-r copies of one eigenvalue.

## What the new rank-two result does and does not give

The analytic colored-edge theorem in this campaign proves a common
law for CMC(2;3,n), and by symmetry CMC(2;n,3), for every finite n.
The complete uniform proof is in geometry_three_color_theorem.md.
This allows both compressed summands to be nonnormal and is stronger
than the square first-frame case CMC(2;2,n).

By (3), however, the next decisive scalar problem for MOC(4) is
CMC(3;3,4). A spectrum-independent common law for this problem is already
too strong. In a 4 by 4 unitary completion, the singleton, pair, and triple
minors on three rows determine every remaining singleton and pair minor
by complementary-minor identities. A universal matching law for them would therefore give the full common-minor permutation law for U(4). The scalar compression equivalence does not supply such a law.

Thus a successful rank-two-to-rank-three gluing must use the actual complex
spectra, or preserve only the required scalar determinant. It cannot simply
require all conditional minor marginals to be reproduced simultaneously.

For the coefficient hull used elsewhere in this campaign, the same rank
three determinant is visible directly:

    D_0(U) + t D_1(U)
       = det(diag(0,1,t) + U[124,:] diag(beta) U[124,:]*).

This identifies an exact route from the start of MOC to its reduced end
obligation. The compatibility theorem needed between them remains open.
