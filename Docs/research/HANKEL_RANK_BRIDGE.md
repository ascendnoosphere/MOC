# A legitimate Hankel rank theorem, its conditional bridge, and exact obstructions

The [independent original-source/bridge audit](hankel_rank_bridge_independent_review.md) validates the full-Hankel theorem and conditional bridge below. **No unrestricted MOC proof and no general atomicity theorem for the joint cone.**

Sources: [oracle report](hankel_rank_bridge_oracle.md); Grigoriy Blekherman, *Nonnegative polynomials and sums of squares*, [arXiv:1010.3465v2](https://arxiv.org/abs/1010.3465v2), Theorem 1.7.

## 1. The original full-Hankel theorem

Blekherman, **Theorem1.7**, arXiv1010.3465v2, printedp4, originalTeX139–141:

> If ell spans an extreme ray of the dual SOS cone Sigma_(4,4)^*, its quadratic moment form has rank1or6.

The form acts on **all ten quaternary quadrics**. In monomial coordinates it is a10by10**full Hankel** matrix. Lemma2.1, originalTeX151–164, explicitly identifies the cone as PSD intersected with this full Hankel subspace. PSD plus an arbitrary selection of polynomial identities is not the same cone.

The original proof chain, TeX166–265, is Lemmas2.2/2.4/2.6, Corollary2.3, Gorenstein Theorem2.5 and the unified Theorem2.7. A non-evaluation extreme kernel has no common complex projective zero. Four parameter quadrics form a complete intersection with degree-four socle; any extra kernel quadric would force the functional to vanish on the socle and hence identically. Therefore kernel dimension4and matrix rank10-4=6. Rank-one Hankel PSD forms are real evaluations by Lemma2.4.

**Usable corollary.** Every full-Hankel PSD matrix H with rankH<=5 is a finite positive sum of real point-evaluation matrices, without requiring H itself to be extreme. Indeed its compact trace-one base admits an extreme-ray decomposition. Each PSD summand has range contained in rangeH and therefore rank<=5. The original theorem forces rank1, and Lemma2.4 identifies evaluations.

This corollary is the actual theorem connection, not an analogy between two small ranks.

## 2. Fourteen versus twenty relations

Use natural quadratic coordinates

    (z,u,v)=(beta²,beta p,vech(pp^T)),
    vech(V)=(V11,V22,V33,V12,V13,V23).

Their55unordered quadratic products represent35quaternary quartics, leaving20independent equal-product relations. These are six adj(V)relations, eight independent V[u]_cross relations and six u_i u_j=zV_ij relations.

The canonical14free Gram directions have the following exact polynomial row spaces on either pure-parity block:

    span(project quadrics)=span(TC,adj(C)-dT), rank14.

This is a statement about spaces, not an identification of each allocation basis matrix with one adjugate entry. Also, a general **joint** certificate does not annihilate the six allocation directions: scalar multipliers balance them. Only its eight gauges necessarily vanish.

- **Plus:** T=i[u]_cross,C=V,d=0. The z coordinate is omitted. Its45products represent31quartics, leaving exactly the14project relations.
- **Minus:** T=-V,C=i[u]_cross,d=z. All ten coordinates remain, but six full-Hankel relations, adj(T)=0, are missing.

The main verifier reconstructs equal-product relations directly from degree-two exponent vectors and checks complete rational coefficient-row spaces against all14canonical matrices.

## 3. Exact plus-block PSD completion criterion

Let a plus-block moment matrix in natural (u,vechV)order be

    Y=[[A,B],[B^T,D]] >=0,

and assume all14project moment relations vanish. Put

    a=(A11,A22,A33,A12,A13,A23)^T.

**Theorem.** A full-Hankel PSD completion adding the z row/column exists iff a is in rangeD. When it exists, it can preserve rank exactly.

Necessity follows from the required principal block [[t,a^T],[a,D]]>=0. Conversely choose k=D^dagger a and set

    H=[[a^T k,(Bk)^T,a^T],
       [Bk,A,B],
       [a,B^T,D]].

The added row is the k-linear combination of the old V rows. Thus H>=0 and rankH=rankY. Its six new zV=uu identities, together with the14old identities, make it full Hankel. This is an exact range test, not an assumption about a pseudoinverse at a singular D.

If rankY<=5, the corollary then decomposes this particular plus-block matrix into projected-Veronese evaluations. It does not prove those evaluations satisfy the MOC order inequality; the general pure-plus gap bound is a separate target.

### Two exact instances

- Evaluations (beta,p)=(1,(1,0,0)) and (2,(0,1,0)) have rankY=rankH=2,a=(1,4,0,0,0,0),Bk=(1,8,0),a^Tk=17. The formula reproduces the full evaluation moment matrix exactly.
- Y=diag(I3,0_6) has rank3and all14old relations, but D0and a=(1,1,1,0,0,0)!=0. There is **no PSD full-Hankel completion of any rank**.

Shorting off the PSD pure-T block S=A-BD^dagger B^T leaves a PSD residual of rankD, but the residual still needs the range test vech(BD^dagger B^T) in rangeD. Automatic validity is not asserted.


## 5. Rank-one geometry, not rank-one decomposition

When all14quadratic evaluations vanish, the elementary classifications are:

- Plus: C0with arbitrary imaginary T; otherwise C=lambda pp^T and T=i beta[p]_cross. These are the real points of the inner-projected Veronese closure.
- Minus: if d!=0 then T=adj(C)/d and, projectively, (T,C,d)=(-pp^T,i[p]_cross,1). If d0then C0and real symmetric T is arbitrary. Thus there is a Veronese component **plus an exceptional linear space**.

These are actual projective Cayley limits, but that fact alone does not prove order positivity. For example the inverse-Cayley construction with C0=C/d and X_epsilon=(C0+epsilon I)^-1 gives the projective limit [adjC0,C0,1]. Pure-T points follow from q(epsilon T)/epsilon. Plus limits follow from q(i r[p]_cross)=(i r[p]_cross,-r²pp^T,0), projective scaling and r tending to0or infinity.

