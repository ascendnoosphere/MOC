# Finite-field and finite-chain-ring determinant ranges

## Setup

Let q be a prime power, k=F_q, and K=F_(q²), with conjugation
bar(x)=x^q. Write Norm(x)=x bar(x) and Trace(x)=x+bar(x) for the norm
and trace from K to k. For matrices, U* is the conjugate transpose.
A finite unitary matrix satisfies U*U=I. In the F4 case below, omega
satisfies omega²+omega+1=0. The unitary theorems concern diagonal spectra
and unitary changes of eigenbasis, not arbitrary normal matrices lacking
such an eigenbasis. The later similarity statements specify their own field
or ring and use U B U^(-1), not an adjoint action.

## 1. The affine analogue holds for unitarily diagonalized pairs, in every characteristic

Let a_i,b_j belong to K and let U*U=I. Put

d=det(diag(a)+U diag(b) U*),
z_pi=product_j(a_pi(j)+b_j).

Then d belongs to the affine hull of the z_pi over k, for every n and q,
including characteristic two.

To construct coefficients, define

c_pi=sgn(pi) product_j U[pi(j),j] / det U.

Laplace expansion followed by Jacobi's complementary-minor identity gives

sum_{pi:pi(J)=I} c_pi = Norm(det U[I,J]) in k.             (1)

Choose eta in K with Trace(eta)=1, and set

p_pi=Trace(eta c_pi) in k.

The trace map is onto. In odd characteristic eta=1/2 works; in characteristic
two any beta outside k has nonzero trace, so eta=beta/Trace(beta) works.
For r in k, Trace(eta r)=r. Applying this to (1) shows that the p_pi reproduce
all squared-norm minors, including the empty-set normalization sum p_pi=1.
Inserting these identities in the determinant expansion yields

d=sum_pi p_pi z_pi,  with p_pi in k and sum p_pi=1.

No ordering or positivity is asserted for the p_pi. The conclusion concerns
diagonal spectra and unitary change of eigenbasis; it does not apply to the
arbitrary normal matrices without a unitary diagonalization.

For n=2 this is an exact image theorem: the determinant values fill the whole
k-affine line between the two pairing vertices. Indeed, for any x in k,
choose a,b in K with Norm(a)=x and Norm(b)=1-x. Then

U=[[a,b],[-conjugate(b),conjugate(a)]]

is unitary with determinant 1, and its determinant mixture is
x z_id+(1-x)z_swap.

## 2. Exact finite-unitary image in dimension three over F4

For diagonal spectra in F4 and U in U(3,2), the image equals the entire
F2-affine hull of the pairing vertices.

If one spectrum has at most two values, express its matrix as a scalar plus
a rank-one update. The determinant is a mixture of three pairing vertices
with coefficients Norm(v_i), where v is a unit vector. Over F2 the possible
coefficient vectors with sum one are the three coordinate vectors and
(1,1,1). All occur: coordinate vectors give permutation matrices, and the
matrix with columns

(1,1,1), (1,omega,omega^2), (1,omega^2,omega)

is unitary over F4. These four combinations are precisely the affine hull of
the three vertices. The rank-one determinant identity is polynomial and valid
even when the diagonal part is singular.

If both spectra have three distinct elements, each omits one element of F4.
Simultaneously translating a by t and b by -t, then scaling both spectra by
a nonzero scalar, reduces to two cases, up to relabeling:

a={1,omega,omega^2}, b={1,omega,omega^2};
a={1,omega,omega^2}, b={0,omega,omega^2}.

The respective vertex sets are {0,1} and all of F4. In either case the
permutation unitaries already supply the entire affine hull. This proves the
claim without relying on exhaustive computation.

## 3. Exact determinant image under unrestricted similarity, over any field

Let F be any field, let A=diag(a), B=diag(b), and let U range over GL_n(F).
Then the image of det(A+UBU^(-1)) is a singleton if all z_pi are equal and is
the whole field F otherwise.

For every invertible U, the same determinant grouping gives the affine
identity d=sum_pi c_pi z_pi with c_pi=sgn(pi) product_j U[pi(j),j]/det U and
sum c_pi=1. This proves the singleton assertion.

Otherwise two vertices joined by a transposition differ, because the
transposition Cayley graph of S_n is connected. Insert the block

G(t)=[[1,t],[1,t-1]],  det G(t)=-1,

on the two corresponding coordinates, and compose with the appropriate
permutation matrix. The resulting determinant is exactly
(1-t)z_pi+t z_pi_tau. As t ranges over F, this runs through all of F.

There is a complete spectral classification of the singleton case:

* A or B is scalar; or
* some alpha in F satisfies m_A(alpha)+m_B(-alpha)>n.

The second alternative makes every vertex zero. To prove the converse for
zero vertices, consider the bipartite graph with an edge (i,j) whenever
a_i+b_j is nonzero. A nonzero vertex is a perfect matching. A row subset
containing two different a-values has all columns as its combined neighbor
set. Thus a Hall obstruction can only consist of rows with one common value
alpha; its condition is precisely m_A(alpha)>n-m_B(-alpha).

If the common vertex value is nonzero, every individual sum a_i+b_j is
nonzero, since every pair occurs in a permutation. Swapping rows r,s assigned
to columns j,k changes the vertex by

(a_r-a_s)(b_k-b_j) product_(remaining pairs)(a_i+b_j).

All remaining factors are nonzero, so equality of every vertex forces one
of the two spectra to be scalar.

## 4. Finite commutative chain rings

Let R be a finite commutative chain ring, so its ideals are linearly ordered,
and keep A,B diagonal with entries in R. Put

J=(z_pi-z_id : pi in S_n).

Then the exact image over GL_n(R) is the single ideal coset

{det(A+UBU^(-1)): U in GL_n(R)} = z_id+J.

The affine determinant identity proves containment in that coset. If J=0,
the image is the singleton z_id and equality is immediate. Otherwise differences
along transposition edges generate J. Because the finitely many principal
ideals generated by those differences are linearly ordered, one edge
difference g generates J. The same G(t) construction realizes its entire
coset z_edge+gR=z_id+J, proving equality.

In particular, over Z/(p^m) or F_q[t]/(t^m), the image is exactly one
congruence class z_id+pi^e R, where e is the smallest valuation of a
transposition-edge difference, truncated at m. This proof does not assert
the same image formula for arbitrary finite local rings whose ideals are
not linearly ordered.

## Exact finite checks

Run `python code/run.py number_systems/finite/finite_unitary_check.py` from the project root. The standard-library script enumerates all
3,18,648,4,96 unitary matrices in dimensions/fields (1,F4),(2,F4),(3,F4),
(1,F9),(2,F9), respectively. It checks all 13,658 subset-marginal identities
using finite-field arithmetic and checks affine-hull membership for all 4,096 diagonal
spectral pairs in F4^3 x F4^3. These checks corroborate the algebraic proofs;
they are not floating-point experiments.
