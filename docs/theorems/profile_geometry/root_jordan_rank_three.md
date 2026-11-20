# An abstract complex MOC theorem in Jordan rank at most three

This is a proved extension of the elementary low-rank mechanism. It does not settle rank four or unrestricted matrix MOC. No claim of historical priority is made.

## The setting

Let V be a finite-dimensional Euclidean Jordan algebra of rank r, with unit e, Jordan trace tr, and determinant det. A Jordan frame is a collection e_1,...,e_r of orthogonal primitive idempotents summing to e. Normalize the trace by tr(e_i)=1. Extend the trace, product, and determinant complex-linearly or polynomially to V_C.

Call x in V_C frame-diagonal if x=sum_i a_i e_i for a real Jordan frame and arbitrary complex a_i. This is the appropriate normal-element class here. In the Hermitian-matrix Jordan algebra its complexification is the full complex matrix algebra, and frame-diagonal elements are exactly normal matrices.

For two possibly different frames (e_i),(f_j), put

    x = sum_i a_i e_i,     y = sum_j b_j f_j,
    P_ij = tr(e_i o f_j).

### Frame overlap is doubly stochastic

The Peirce operator L_f for an idempotent f is self-adjoint with eigenvalues among 0,1/2,1. Hence it is positive semidefinite. Trace associativity and e_i^2=e_i give

    P_ij = <e_i,e_i o f_j> = <e_i,L_fj e_i> >= 0.

Furthermore sum_j P_ij=tr(e_i)=1, and similarly every column sum is one. Thus P is a doubly stochastic matrix. By the finite Birkhoff decomposition, there are nonnegative weights w_pi, summing to one, such that

    P_ij = sum_{pi:pi(i)=j} w_pi.

These weights depend only on the two frames, not on either complex spectrum.

## Theorem: complex Jordan MOC holds in rank three

If r=3, then for every pair of frames and every complex a,b,

    det(x+y) = sum_pi w_pi product_i(a_i+b_pi(i)).

In particular the desired real convex-hull inclusion holds, even in the exceptional Albert algebra of three-by-three Hermitian octonionic matrices after complexification.

### Proof

For rank three define

    x# = x^2 - tr(x)x + sigma_2(x)e,
    sigma_2(x) = ((tr x)^2-tr(x^2))/2.

The determinant Newton identity is

    det x = ((tr x)^3 - 3 tr(x)tr(x^2) + 2 tr(x^3))/6.

Expanding this identity and using the associative trace form proves the cubic polarization identity

    det(x+y) = det x + det y + <x#,y> + <x,y#>.

No matrix associativity is required. On a frame,

    x# = sum_i (product_{k != i} a_k)e_i,
    y# = sum_j (product_{l != j} b_l)f_j.

Consequently

    det(x+y) = product_i a_i + product_j b_j
      + sum_ij P_ij [ (product_{k != i} a_k)b_j
                     + a_i(product_{l != j} b_l) ].

Substitute the Birkhoff decomposition. For each pi, the bracketed cross terms are exactly the degree-(2,1) and degree-(1,2) terms in product_i(a_i+b_pi(i)). The pure terms agree because sum_pi w_pi=1. This proves the identity over C, with the same nonnegative real weights for all spectra. QED.

## Rank two and Clifford spin factors

For r=2,

    det(x+y) = det x + det y + tr(x)tr(y)-<x,y>.

The same Birkhoff argument applies. In a spin factor R plus R^m, write x=(s,t n) and y=(u,v m), where n,m are real unit vectors and s,t,u,v are complex. The determinant is s^2-t^2 on x and similarly on y. The two spectral products are

    z_id   = (s+u)^2-(t+v)^2,
    z_swap = (s+u)^2-(t-v)^2.

The exact formula is

    det(x+y) = ((1+n dot m)/2) z_id
             + ((1-n dot m)/2) z_swap.

Both weights are nonnegative. This proves the normal/frame-diagonal complex MOC statement for every Clifford spin factor, regardless of its ambient vector-space dimension. The relevant determinant rank remains two.

## Direct products

If a Euclidean Jordan algebra is a direct product of factors each of rank at most three, its determinant is the product of the factor determinants. Tensoring the positive laws gives a law on the block-preserving permutations. These permutations are among all permutations of the full spectrum, so the same MOC inclusion holds on the product algebra, in arbitrarily large total rank.

## Exact obstruction to extrapolation

Starting in rank four, the determinant expansion has mixed degree (2,2). Frame overlaps P_ij control only the mixed degrees (r-1,1) and (1,r-1). The missing middle coefficients are precisely the squared two-by-two minors in the matrix model, and their joint permutation law can fail. Thus rank-three polarization is a complete theorem but does not provide an induction to irreducible rank four.

## Context and source

The real-spectrum Fiedler inequality in Euclidean Jordan algebras was proved by David Sossa, Linear Algebra and its Applications 667 (2023), 151–164, DOI 10.1016/j.laa.2023.03.011:
https://www.sciencedirect.com/science/article/abs/pii/S0024379523000952

The argument above is supplied explicitly for complex frame-diagonal spectra in ranks two and three; it is not being attributed to that paper, whose abstract and introduction concern the real Euclidean Jordan algebra inequality.
