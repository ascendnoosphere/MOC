### 1. Nearest-torus geodesic: left/right handling is correct  
**Lines 37–47; permutation version at line 33.**

A minimizing geodesic from the compact torus exists. Writing it as
\[
\gamma(t)=e^{tK}D
\]
is legitimate for the bi-invariant Frobenius metric. Its initial velocity is \(KD\), while torus tangent vectors are \(HD\), with \(H\) imaginary diagonal. Orthogonality therefore gives precisely \(\operatorname{diag}K=0\).

The gauge elimination uses the **rightmost** diagonal factor correctly:
\[
\gamma(t)B\gamma(t)^*=e^{tK}DBD^*e^{-tK}
=e^{tK}Be^{-tK}.
\]
If instead written \(De^{tL}\), the generator changes to \(L=D^*KD\); its diagonal remains zero and its Frobenius norm is unchanged. No uniqueness or injectivity-radius assumption is needed.

For \(PT\), set \(V=UP^*\), \(B'=PBP^*\). Then \(UBU^*=VB'V^*\), and right translation maps \(PT\) isometrically onto \(T\). Thus the permutation reduction also works.

### 2. Hessian: signs, factors, and singular cases are correct  
**Lines 49–67.**

Writing \(c_i=a_i+b_i\), the coefficient of \(t^2\) associated with \(i<j\) is
\[
|K_{ij}|^2\Big[(b_j-b_i)(c_j-c_i)-(b_j-b_i)^2\Big]
\prod_{\ell\ne i,j}c_\ell
=
|K_{ij}|^2(z_{(ij)}-z_{\rm id}).
\]
The first term comes from diagonal second derivatives; the subtracted square comes from the two off-diagonal first derivatives.

Consequently,
\[
f''(0)=-2\sum_{i<j}\delta_{ij}|K_{ij}|^2
\le-\delta\|K\|_F^2,
\]
because \(\|K\|_F^2=2\sum_{i<j}|K_{ij}|^2\). Both the sign and factor \(2\) are correct.

This is a polynomial computation: **zero paired sums and singular \(A+B\) cause no exception**. The same reasoning gives \(f'(0)=0\) without invertibility.

### 3. Third derivative and sharpening: constants are correct  
**Lines 69–91 and 102–117.**

The column-product-rule multiplicities are exactly
\[
n,\qquad 3n(n-1),\qquad n(n-1)(n-2).
\]
Hadamard bounds each term by the product of its column norms, each bounded by the corresponding operator norm. Since
\[
\|C^{(j)}(t)\|_{\rm op}\le(2\|K\|_{\rm op})^j\beta,
\]
all three groups have the common factor \(8\|K\|_{\rm op}^3\). Using \(\beta\le R\), \(\|K\|_{\rm op}\le\|K\|_F\), and the stated multiplicity identity yields
\[
|f'''(t)|\le8|\eta|n^3R^n\|K\|_F^3.
\]
There is no missing dimension factor. For \(n=2\), the three-distinct-columns term is absent, as stated.

Centering preserves the full matrix sum. Conjugating \(A\) instead of \(B\) replaces the moving-spectrum norm by \(\alpha\), with generator \(-K\). Therefore choosing \(m=\min(\alpha,\beta)\) gives precisely the stated \(L_\lambda\). Under \(\delta>0\), neither centered spectrum can be identically zero, so \(L_\lambda>0\).

### 4. Final radius is correct  
**Lines 93–100 and 117.**

Taylor’s remainder is bounded by
\[
\frac{8|\eta|n^3R^n}{6}q^3.
\]
At
\[
q\le\frac{3\delta}{16|\eta|n^3R^n},
\]
this is at most \(\delta q^2/4\). Combining with the quadratic term \(-\delta q^2/2\) gives the claimed margin.

Likewise, \(L_\lambda q^3/6\le\delta q^2/4\) gives exactly the sharpened radius \(3\delta/(2L_\lambda)\).

### 5. Exact order-four sample checks out  
**Lines 119–133.**

Exact enumeration confirms:
- \(z_{\rm id}=81+54i\);
- \(h=81\), with identity the unique maximizing permutation;
- gaps \((9,36,90,9,45,18)\), hence \(\delta=9\);
- \(R=\sqrt{10}+3<7\);
- \(r_0=27/2458624\), giving margin \((9/4)d(U,T)^2\).

I also checked the complex Hessian identity and third-derivative column product rule exactly for a mixed complex skew-Hermitian \(4\times4\) generator, both for this example and after replacing \(b_1=3\) by \(0\), making \(A+B\) singular. Both checks passed.

