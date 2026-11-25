# Gaussian spectra and Haar mixing

[Proof map index](README.md) · [Unrestricted conjecture](../README.md) · [All-order proof maps](all-orders-proof-map.md)

Fix an order $n$. Let $a$ and $b$ be two lists of $n$ complex numbers.
Let $U$ be a unitary matrix. Write $d$ for the determinant of
$\mathrm{diag}(a)+U\mathrm{diag}(b)U^*$. The matching hull is the real
convex hull of the products obtained by matching the two lists.

The random ensemble in the paper note gives every spectral entry the
complex Gaussian density $e^{-|z|^2}/\pi$. All entries are independent.
The mixer $U$ has Haar probability measure and is independent of the
entries. Its result is a bound on the probability that $d$ is outside
the matching hull. It concerns this specified ensemble.

The registered almost-sure reformulation requires inclusion almost
everywhere in every order on every probability space where the mixer
is unitary almost everywhere. A singleton probability space recovers
the deterministic conjecture. The Gaussian–Haar
theorem bounds failure in one ensemble under a second-moment premise.
[Almost-sure equivalence](../Lean/MOC/Reformulations/SecondNative.lean#L271) · [Gaussian bound](../Lean/MOC/GaussianHaarContainment.lean#L1131)

```mermaid
flowchart BT
    A["Two exchanges on disjoint pairs"] --> S["Three products surround a disk"]
    G["Eight disk masses and independence of disjoint coordinates"] --> B["Probability of no good block"]
    C["Gaussian convolution"] --> N["Gamma formula for the negative moment"]
    L["Finite Bohr–Mollerup bound"] --> P["Lower tail of the identity product"]
    N --> P
    H["Haar determinant second moment<br/>Ensemble evaluation pending in Lean"] --> D["Upper tail of the determinant"]
    S --> U["Failure is in the union of three events"]
    B --> U
    P --> U
    D --> U
```

## Deterministic inclusion

Let $z_0$ denote the identity matching product. For two disjoint
transpositions, let $q_1$ and $q_2$ denote their ratios to $z_0$.
Each ratio uses only the two affected factors. The three products
$z_0$, $z_0q_1$, and $z_0q_1q_2$ are matching vertices.

Put $\omega=(-1+i\sqrt3)/2$. If both ratios are within $1/10$ of
$\omega$, the normalized triangle contains the centered disk of
radius $1/4$. For an arbitrary support direction, the three
equilateral projections sum to zero. Their squared sum is three
halves of the squared norm of the direction. These identities give
a support bound of one half of that norm. The perturbation changes
each projection by at most $21/100$ of the norm. The proof applies
the resulting support bound to every direction.
[Disk inclusion](../Lean/MOC/GaussianHaarContainment.lean#L140)

For each pair, put the four disk centers at $0$, $1$, $1$, and
$(-2+i\sqrt3)/7$ in the order of the two entries of $a$ and the two
entries of $b$. Take radius $1/200$ at each center. The denominator
stays nonzero and the ratio is within $1/10$ of $\omega$. Two such
pairs give a matching triangle block.
[Ratio estimate](../Lean/MOC/GaussianHaarContainment.lean#L262) · [Block construction](../Lean/MOC/GaussianHaarContainment.lean#L425)

## Failure bound

For a disk with center $c$ and radius $r$, the Gaussian mass is at
least $r^2e^{-(|c|+r)^2}$. The proof multiplies its area by a lower
bound on the density on that disk. For the eight independent
coordinates of one block, this gives the lower bound
$p_0=e^{-5}/200^{16}$. The coordinates in different consecutive
blocks are disjoint. Their independence makes the block failure
probabilities multiply. The probability of no good block is at most
$(1-p_0)^{\lfloor n/4\rfloor}$.
[One disk](../Lean/MOC/GaussianHaarContainment.lean#L322) · [Eight disks](../Lean/MOC/GaussianHaarContainment.lean#L453) · [Consecutive blocks of independent spectra](../Lean/MOC/GaussianHaarContainment.lean#L623)

The sum of two independent spectral entries has density
$e^{-|z|^2/2}/(2\pi)$. Complete the square in the convolution of the
two original densities. Polar integration gives the expectation of
$|z|^{-1/10}$ as $2^{-1/20}\Gamma(19/20)$, where $\Gamma$ is the
Euler gamma function. The finite Bohr–Mollerup comparison at $255$
and bounds on two reciprocal sums give an upper bound of $e^{-7/2000}$.
Each sum $a_j+b_j$ uses its own pair of independent entries. The product
law of the pairs gives independence of these sums.
[Gaussian convolution](../Lean/MOC/GaussianHaarContainment.lean#L957) · [Gamma formula](../Lean/MOC/GaussianHaarContainment.lean#L991) · [Gamma bound](../Lean/MOC/GaussianHaarContainment.lean#L832)

| Premise | Consequence | Lean source |
| --- | --- | --- |
| The spectral entries are independent standard complex Gaussians. | The probability that $|z_0|$ is less than $e^{n/100}$ is at most $e^{-n/400}$. | [Lower tail](../Lean/MOC/GaussianHaarContainment.lean#L1066) |
| The second moment of $d$ is at most $(n+2)(n+3)/6$. | The probability that $|d|$ is greater than $e^{n/100}/4$ is at most $\frac83(n+2)(n+3)e^{-n/50}$. | [Determinant upper tail](../Lean/MOC/GaussianHaarContainment.lean#L727) |

Assume independent standard complex Gaussian spectral entries, a
measurable determinant magnitude, and the stated determinant second
moment bound. The union bound gives

$$
\Pr(d\text{ is outside the matching hull})
\le (1-p_0)^{\lfloor n/4\rfloor} + e^{-n/400}
   + \frac83(n+2)(n+3)e^{-n/50}.
$$

The three events in this union may be correlated. The displayed
estimate decays exponentially in $n$. Its small value of $p_0$
gives no useful bound at moderate orders.
[Failure bound from the determinant moment](../Lean/MOC/GaussianHaarContainment.lean#L1131)

## Remaining Haar input

The paper argument evaluates the determinant second moment by
orthogonality of the spectral monomials in the expansion by squared
unitary minors. It uses Gaussian Gram–Schmidt to compute fourth
moments of the Haar minors. The Lean source starts at the resulting
second-moment inequality.
[Gaussian Gram–Schmidt construction, section 1.2](https://case.edu/artsci/math/esmeckes/Haar_book.pdf)

The numerical constants and algebraic identities passed an exact
arithmetic check. Lean kernel verification is pending.
