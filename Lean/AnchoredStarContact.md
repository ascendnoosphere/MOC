# Two difference charts and a sparse contact exclusion

The Lean files check the statements below except the final functional rank count, which is a direct marker argument. These results do not give a covering theorem for all terminal contact families.

## The full difference map reconstructs any strict profile

Write $P_\sigma=\prod_j(a_{\sigma j}+b_j)$ and fix any pivot $r$; $r$ itself need not have a nonzero product. If the determinant is outside the matching hull, some product $P_s$ is nonzero, since the real signed determinant law represents the determinant. Use the graph on labels with an edge $ij$ if both $a_{s i}\ne a_{s j}$ and $b_i\ne b_j$. A pair of disjoint edges gives a disjoint-swap mixed difference equal to the product of those four nonzero differences and untouched factors from $P_s$.

If there are no disjoint edges, the graph is either a star or a triangle. In a triangle the three values in each coordinate are pairwise distinct. A fourth vertex must share one coordinate with each vertex of the triangle, which two coordinates cannot do. Thus the graph is a star. Away from its center there are no edges, which implies one of the two spectra is constant there. The checked one-exception theorem covers that case. Orders at most three are already covered.

For the four ordered labels $q_0,q_1,q_2,q_3$ of the resulting rectangle, $P_{q_0}P_{q_3}=P_{q_1}P_{q_2}$. Set $d_q=P_q-P_r$. Then
$$
 P_r=\frac{d_{q_1}d_{q_2}-d_{q_0}d_{q_3}}{d_{q_0}+d_{q_3}-d_{q_1}-d_{q_2}} .
$$
This is a regular inverse on a rectangle chart of the image. It applies to collisions and zero factors. Globally, the full vector of differences determines any potentially strict exact profile, not merely up to a finite ambiguity. This does not imply that a subset of contact differences determines it. In fact after absorbing the direction, reflection $P\mapsto-\bar P$ gives a second exact point of the contact-only fibre with opposite real determinant gap, since all its pinned differences are imaginary. Isolation is consistent with this second point.

## A full-rank 2n−1 contact pattern cannot be strict

Take four different labels $o,i,j,k$, with $o$ the anchor and $i$ the star center. Work relative to a pivot $r$, or equivalently relabel so $r=1$. Assume simple spectra and no zero matching products. Use these contact labels:

1. The pivot and all $n-1$ transpositions $(o,l)$.
2. One orientation of the three-cycle on $\{o,i,l\}$ for each $l\notin\{o,i\}$, with $j$ using $(o,i)(o,j)$ and $k$ using $(o,i)(i,k)$.
3. The four-cycle $(o,i)(o,j)(i,k)$.

The transposition $(o,i)$, the two specified three-cycles and the four-cycle form the disjoint-swap rectangle with exchanges $(o,j),(i,k)$. Its nonzero mixed difference forces the common support height to be zero. Each triple $\{o,i,l\}$ now has two even and two odd products on the imaginary axis. The three-slot sum and product identities put both missing products on that axis as well.

Normalize the additive kernel at $o$ to $K_{uv}=1+x_u y_v$. For each $l\ne o$, the ratio of the pivot to $(o,l)$ gives the real diagonal $K_{ll}$. The completed triples give real $K_{il}$ and $K_{li}$ by ratios of a transposition to a three-cycle. The residual $E=K-1$ satisfies $E_{uv}E_{ii}=E_{ui}E_{iv}$, and simple spectra give $E_{ii}\ne0$. Hence $K$ is real everywhere. The common profile multiplier is imaginary because the nonzero pivot product is imaginary. Every projected matching product therefore vanishes. The real signed determinant law also has zero projected value, and the checked common-line comparison gives actual hull inclusion for every mixer.

The $2n-2$ pivot differences of these $2n-1$ labels are linearly independent as functions on the exact profile locus. Use the checked equivalence between linear profile identities and subset-image marker identities. The pair marker $\{o,i\}\mapsto\{j,k\}$ isolates the four-cycle: every other chosen label moves at most one label outside $\{o,i\}$ into that image. After its coefficient is zero, use, for each chosen three-cycle, its directed arrow between $i$ and its third label $l$. No other remaining label realizes the arrow. After all those coefficients are zero, the singleton arrow $o\mapsto l$ isolates each anchor swap. These markers vanish at the pivot. Multiplying all labels on the left by $r$ simply applies $r$ to the target sets.

The pattern meets the terminal functional rank threshold; its exclusion uses spectral realizability, not the rank test alone.
