# Cycle 02: zero-height contacts and transposition degree

## Checked contribution

Let $P_\sigma=\prod_j(a_{\sigma j}+b_j)$, and suppose all projected products $\Re(\eta P_\sigma)$ are nonpositive. Let $r$ be a contact with $\eta P_r\ne0$.

- If every transposition at $r$ is a contact, all matching products lie on the support line. The determinant hull inclusion then holds for every mixer.
- More generally, let $S$ be any set of labels. If every transposition within $S$ at $r$ is a contact, the whole fibre obtained by permuting the labels within $S$ is active.
- Consequently any strict zero-height witness has an inactive, nonzero transposition neighbor at every nonzero contact. Any connected component of the nonzero transposition graph containing a contact also contains an inactive matching. An isolated nonzero matching cannot be a contact.

These statements allow spectral collisions and zero products. They do not assume connectivity of the nonzero graph or use a permutation search.

### Proof

Relabel so that $r$ is the identity. For any subset $S$, the alternating sum of profiles on its permutation fibre is the outside pivot factor times the determinant of $(a_i+b_j)_{i,j\in S}$. It is zero for $|S|>2$ by the explicit rank-two factorization. Go by strong induction on moved-support size. The identity and transpositions are the base cases. A permutation with more than one nontrivial cycle factors as two disjoint nonidentity permutations of smaller support. Their active products and the nonzero pivot are imaginary. The product rectangle identity therefore makes their combination imaginary as well. For a cycle moving exactly $S$, every term not already known to be active in the local alternating sum is another full cycle on $S$. Such terms have one common parity. Their projected values are nonpositive and have sum zero, so each vanishes.

## Exact finite consequences

At a nonzero pivot, let $Z$ be the number of forbidden cross-entries $a_i+b_j=0$. A swap whose new product is zero has a newly used forbidden entry $(i,j)$ with $i\ne r(j)$. It determines the swap $\{j,r^{-1}(i)\}$, so distinct zero neighbors can be assigned distinct forbidden entries. The nonzero transposition degree is at least $\binom n2-Z$.

The [checked rank-two-overlap comparison](../../MOC/UnequalColorHall.lean) gives $r_z+s_z+2<n$ for every color of a strict witness, even if only one list contains it. In order four this forces simple lists and no zero entries. In order five this leaves only $1\times1$ zero blocks and $Z\le5$, so nonzero degree is at least five. In order six it leaves $1\times1$, $1\times2$ and $2\times1$ blocks. Each contributes at most $(2/3)(r_z+s_z)$ entries and the class sizes sum to at most twelve. Thus $Z\le8$ and the nonzero degree is at least seven. At a nonzero zero-height contact at least one such neighbor must be inactive. These order-five and order-six conclusions follow by symbolic counting, not a census.

For the order-three forbidden-diagonal example in Path 15, the two nonzero vertices can indeed be isolated in the allowed transposition graph. If one were a zero-height contact, the cycle theorem would force both products onto the supporting line, consistent with the explicit equality $P_{(012)}=-P_{(021)}$ for $b=-a$. Disconnectedness does not defeat the alternating-sum method.

## Gates

- **Path 01:** The proof works on every individual zero profile, including its forced-zero coordinates. The [fixed-zero profile locus](../../MOC/FixedZeroProfiles.lean) now has a checked prime description for any marked relation. [Relative fixed-gap transfer](../../MOC/FixedZeroContactTransfer.lean) preserves every marked zero when the stated bound on the number of controlling observables holds. The relative dimension bound is still needed.
- **Path 07:** The multiplicity bound and the inactive-neighbor requirement are compatible at zero height. A face with a nonzero pivot and all its transpositions active is excluded for every mixer. At a globally contact-maximal strict witness, [two contacts have distinct complex products](../../MOC/DistinctTerminalContacts.lean), so at least one is nonzero. Thus every such zero-height witness has a nonzero contact with an inactive nonzero swap neighbor. The inequality for profiles satisfying that requirement remains open. Nonzero-height faces are also not classified here.
- **Path 15:** The checked clique saturation and neighbor obstruction are exact substitutes for a connectivity assumption. No claim follows about generic connectivity, winding, polygon enclosure, or constructing a positive minor law.
