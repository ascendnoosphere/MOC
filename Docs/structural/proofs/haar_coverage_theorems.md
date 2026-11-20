# Rigorous Haar coverage criteria for the Marcus–de Oliveira inclusion

These are probabilistic sufficient conditions. They do not prove MOC for every
unitary, and they do not define a percentage of all normal matrix pairs without
specifying a probability law. No novelty claim is made.

Let n>=2, A=diag(a_1,...,a_n), B=diag(b_1,...,b_n), and let U be Haar distributed
on U(n). Write

    d(U)=det(A+UBU*),
    z_pi=product_i (a_i+b_pi(i)),
    K=conv{z_pi: pi in S_n},
    c=(1/n!) sum_pi z_pi,
    V=(1/n!) sum_pi |z_pi-c|^2.

All statements below are unconditional consequences of determinant expansion,
unitary Haar integration, and convex geometry; MOC is not used in their proofs.

## 1. Exact second moment and a universal variance bound

Index matrices by S_n, and let

    G_(pi,sigma)=n^(number of cycles of pi^(-1)sigma),
    S_(pi,pi)=sgn(pi),
    H=S G^(-1) S.

Then

    E d = c,
    E |d|^2 = z* H z,
    E |d-c|^2 <= V/(n+1).                         (1)

Here z* is conjugate transpose. The inverse exists because the matrix size in
the Haar integral and its polynomial degree are both n.

### Derivation of the exact formula

Put

    m_pi(U)=product_i U_(i,pi(i)),
    q_pi(U)=sgn(pi) m_pi(U)/det U.

The determinant identity

    det(A+UBU*)=det(AU+UB)/det U

and Leibniz expansion give d=sum_pi q_pi z_pi and sum_pi q_pi=1.

The unitary Weingarten formula, with all row indices distinct and all column
indices distinct, reduces to

    E[m_pi conjugate(m_sigma)] = (G^(-1))_(pi,sigma).

Since |det U|=1,

    E[q_pi conjugate(q_sigma)] = H_(pi,sigma).

The sign vector is a G-eigenvector with eigenvalue n!. Therefore H has row
sums 1/n!, and

    E q_pi = E[q_pi sum_sigma conjugate(q_sigma)] = 1/n!.

This proves the mean and exact second-moment formulas.

### Proof of the factor 1/(n+1)

The eigenvalues of G on the symmetric-group isotypic summands indexed by
partitions lambda of n are

    C_lambda(n)=product_(i,j in lambda) (n+j-i).

This is the standard character expansion of the unitary Weingarten matrix,
equivalently the hook-content dimension formula combined with Schur–Weyl
duality. For the column partition lambda=(1^n), C_lambda(n)=n!. Every other
partition has

    C_lambda(n) >= C_(2,1^(n-2))(n) = (n+1)n!.    (2)

For an elementary verification of the minimum: if a noncolumn partition is
not (2,1^(n-2)), remove the last box from its bottommost row r of length at
least two, and put that box into a new bottom row. The resulting shape is
still a partition and is still not a column. If the previous number of rows
was ell, its product changes by replacing n+lambda_r-r with n-ell. The
former is strictly larger. Repeat until (2,1^(n-2)).

The sign twist S sends the original column eigenspace to the constant
vectors. Hence, on the orthogonal complement of constants,

    H <= I/((n+1)n!).

Apply this to z-c*1 to obtain (1).

The constant is sharp in general: take rank-one A=diag(alpha,0,...,0) and
choose distinct b_j so the determinant depends nontrivially on the first row
probabilities |U_1j|^2. The Dirichlet(1,...,1) covariance gives equality in
the variance comparison for this first-order permutation representation.

## 2. A stronger, affine-invariant covariance comparison

Identify C with R^2. Let

    x_pi=(Re z_pi, Im z_pi)^T,
    mu=(Re c, Im c)^T,
    Sigma=(1/n!) sum_pi (x_pi-mu)(x_pi-mu)^T.

Then

    Cov_R2(d) <= Sigma/(n+1)                     (3)

in the positive-semidefinite order.

The key point is that real signed coefficients work for every complex
spectrum. The squared-minor determinant expansion is unchanged when U is
replaced by its entrywise conjugate. But q_pi(conjugate U)=conjugate(q_pi(U)).
Consequently

    d(U)=sum_pi q_pi(U)z_pi
        =sum_pi conjugate(q_pi(U))z_pi
        =sum_pi tau_pi(U)z_pi,
    tau_pi=Re q_pi,
    sum_pi tau_pi=1.

These coefficients may be negative; this is not a convex representation.

For any real vector v indexed by permutations,

    Var(sum_pi tau_pi v_pi)
      <= E |sum_pi q_pi(v_pi-mean(v))|^2
      <= sum_pi (v_pi-mean(v))^2 / ((n+1)n!).

Take v_pi=t^T x_pi for any t in R^2. This proves (3).

In fact, for these particular coordinate vectors, the covariance can be
computed exactly with the same n!-dimensional H. If X is the n! by 2 real
matrix whose rows are x_pi-mu, then

    Cov_R2(d) = X^T H X.                         (4)

Indeed, the squared-minor formula gives
d(conjugate a,conjugate b;U)=conjugate(d(a,b;U)), whereas the conjugated
spectra have vertices conjugate(z_pi). Hence

    sum_pi q_pi Re(z_pi) = Re(d),
    sum_pi q_pi Im(z_pi) = Im(d).

Both sums are real. The usual conjugated Weingarten second moment therefore
also computes the real coordinate cross moments, yielding (4).

## 3. Explicit coverage certificates

If r>0 and the disk centered at c of radius r is contained in K, Markov's
inequality and (1) give

    P[d outside K] <= V/((n+1)r^2).              (5)

If Sigma is positive definite, set

    rho = inradius about 0 of Sigma^(-1/2)(K-mu).

Then (3) gives

    P[d outside K] <= 2/((n+1)rho^2).           (6)

In particular, at least half of Haar unitaries satisfy MOC whenever

    rho^2 >= 4/(n+1).                           (7)

For n=4 this is rho^2>=4/5. A strict inequality defines an open set of
spectral data, as long as Sigma remains positive definite. Such a set has
positive Lebesgue measure when nonempty; exact examples are being computed
independently by the team.

No matrix square root is needed for an exact certificate. If the facets of
K-mu are u_f^T x<=h_f, with h_f>0, then

    rho^2=min_f h_f^2/(u_f^T Sigma u_f).          (8)

For Gaussian-rational spectra, all quantities in (8) are rational when
unnormalized rational facet normals are used. Thus (7) is checkable using
only exact rational inequalities.

Using the exact covariance C in (4) gives the sharper bound

    P[d outside K] <= tr(Sigma^(-1) C)/rho^2.   (9)

Even more generally, any positive definite real matrix Q and R>0 satisfying
{x:x^T Q x<=R^2} subset K-mu yields

    P[d outside K] <= tr(Q C)/R^2.

These inequalities are genuine probabilistic lower bounds, not sampling
estimates. A bound larger than one is simply uninformative. When Sigma is
singular, do not apply the whitening formula; handle the line or point
case separately (the classical collinear-vertices theorem gives full MOC).

## 4. Arbitrarily high coverage after a large scalar shift

This result avoids any all-U local-maximizer stability assertion.

Fix a,b and define the assignment-trace vertices and their hull

    v_pi=sum_i a_i b_pi(i),
    T=conv{v_pi},
    c_T=(sum_i a_i)(sum_j b_j)/n.

Assume T has nonempty planar interior, and let r_T>0 be the radius of a disk
centered at c_T contained in T. Put

    M=max_i |a_i| + max_j |b_j|,
    E(s)=sum_(k=3)^n binom(n,k) M^k/|s|^(k-2).

For 0<m<=1/n, if

    2 E(s) <= n m r_T,                          (10)

then MOC holds for (A+sI,B) for every U satisfying

    min_(i,j) |U_ij|^2 >= m.                    (11)

### Proof

Let W(U)=tr(AUBU*)=sum_(i,j) a_i b_j |U_ij|^2. If (11) holds, the doubly
stochastic matrix P=(|U_ij|^2) decomposes as

    P = n m (J/n) + (1-nm) P',

where P' is doubly stochastic (the case nm=1 is immediate). By Birkhoff,

    W(U) in n m c_T + (1-nm) T.

Thus W(U) has supporting-line margin at least n m r_T inside T.

Let e_k denote the elementary symmetric function of the eigenvalues, and
write t=tr A+tr B and C2=e_2(a)+e_2(b)+(tr A)(tr B). Since

    e_2(A+UBU*)=C2-W(U),

the normalized determinant

    D_s(U)=-[det(sI+A+UBU*)-s^n-s^(n-1)t-s^(n-2)C2]/s^(n-2)

satisfies |D_s(U)-W(U)|<=E(s). The same normalization maps every shifted
permutation vertex to within E(s) of its assignment-trace vertex v_pi.
The uniform estimate follows from ||A+UBU*||<=M and therefore
|e_k(A+UBU*)|<=binom(n,k)M^k. The analogous diagonal bound is immediate.

Every supporting function of the normalized permutation hull is at least
the corresponding supporting function of T minus E(s). Meanwhile D_s(U)
lies below that supporting function of T by at least n m r_T-E(s).
Condition (10) therefore places D_s(U) in the normalized permutation hull.
Undoing its affine normalization proves the claimed MOC inclusion.

For Haar U, each |U_ij|^2 has Beta(1,n-1) distribution. Thus

    P[min |U_ij|^2<m]
       <= n^2 [1-(1-m)^(n-1)]
       <= n^2(n-1)m.                           (12)

Given epsilon in (0,1), take m=epsilon/[n^2(n-1)]. Then (10) implies

    P[MOC for (A+sI,B)] >= 1-epsilon.           (13)

One completely explicit sufficient threshold is

    |s| >= max{2nM,
               4 n(n-1) binom(n,3) M^3/(epsilon r_T)}.  (14)

To verify (14), use

    E(s) <= binom(n,3) M^3/|s| (1+M/|s|)^(n-3)
         < 2 binom(n,3) M^3/|s|

when |s|>=2nM. Formula (10) follows. For n=2 the tail is zero and ordinary
MOC already holds for every U.

In particular, for all fixed spectra satisfying the interior hypothesis,

    lim_(|s|->infinity) P[MOC for (A+sI,B)] = 1. (15)

The estimate is uniform in the argument of s. It does not assert a finite
threshold beyond which every unitary works.

### Which fixed spectra satisfy the interior hypothesis?

The assignment hull T has nonempty planar interior exactly when neither
spectrum is constant and at least one of the two spectra is not collinear.

To see this, differences between assignments differing by a transposition
are (a_i-a_j)(b_k-b_l). Every such product occurs. If T is collinear and both
spectra are nonconstant, fix a nonzero difference in one spectrum: all
differences in the other spectrum must lie on one real line. Doing this in
both directions proves both spectra collinear. Conversely, if both spectra
are collinear, all assignment differences lie in the product of their two
directions, a real line. A constant spectrum makes T a singleton.

Thus the hypothesis holds for a full-measure set of a,b in C^n times C^n
when n>=3. The threshold depends on a,b and can diverge near degenerate
trace hulls.

The excluded fixed spectra already satisfy MOC for every relative unitary:
a constant spectrum is trivial, and both spectra individually collinear is
the established essentially-Hermitian case (including arbitrary affine
lines, by the known scalar-shift and Mobius reductions). These properties
persist after shifting A by sI. Thus, combining this known case with (15),
the limit in (15) in fact holds for every fixed pair of complex spectra.
This final extension uses Drury's established essentially-Hermitian results,
not the new probabilistic estimate alone. Official primary text:
https://journals.uwyo.edu/index.php/ela/article/download/403/403/403

## 5. Distributions actually covered

- Fixed spectra with relative eigenbasis Haar distributed: (5), (6), (9),
  and (13) apply as stated.
- Random spectra whose conditional relative eigenbasis is Haar: integrate
  any of these conditional bounds over the spectral law. In particular, a
  spectral law supported on pairs satisfying (7) has at least half coverage.
- Independent unitarily invariant normal matrices have this conditional
  relative-Haar model, including independently Haar-conjugated diagonal
  matrices with arbitrary independent spectral laws.
- The large-shift theorem is uniform over any spectral family having M
  uniformly bounded above and r_T uniformly bounded below by a positive
  constant. Hence it produces whole positive-measure spectral regions with
  any prescribed coverage 1-epsilon, not only individual examples.
- These conclusions do not automatically apply to orthogonal-Haar matrices,
  adversarial relative eigenbases, or an unspecified notion of a random
  normal matrix.

## Primary integration reference

Benoit Collins and Piotr Sniady, *Integration with respect to the Haar measure
on unitary, orthogonal and symplectic group*, Comm. Math. Phys. 264 (2006),
773–795, DOI 10.1007/s00220-006-1554-3.
https://arxiv.org/pdf/math-ph/0402073

Proposition 2.3 gives the inverse/character expansion, and Corollary 2.4
gives the entry-moment formula. The factor C_lambda(n) above follows by the
hook-content evaluation of the Schur polynomial in that expansion. The
variance and convex-geometric deductions here have been derived explicitly;
no literature priority claim is attached to them.
