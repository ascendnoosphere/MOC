### 1. Original-source and coordinate audit: PASS

- **Affine contraction, not merely projective contraction.**  
  `organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:919–954` explicitly constructs a diagram of **affine-scheme morphisms**, identifies its bottom arrow as the partial-derivative map, and proves commutativity up to a nonzero scalar. Its addition map has dense image in the affine secant cone. Consequently,
  \[
  \dim\overline{G(S)}\le \dim\widehat{N_8}=10.
  \]
  Taking closures handles secant-cone points not represented by a particular sum. The import at `organized/research/CORANK_TWO_LIFT_EXACTNESS.md:20–23` is justified.

- **The representation dependency checks out.**  
  `organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:687–702` gives exactly one \(V_{2,2,2,2}\) in \(R_1(M_8)^{\otimes2}\) and none in \(R_2(M_8)\), supporting the uniqueness argument in the affine diagram.

- **Dimensions, irreducibility, and characteristic zero are appropriate.**  
  The active secant-dimension argument is at `organized/research/external/m8_hmsv/1103.5255v1/8pts-032711.tex:1190–1203`. The invariant ring defining \(X\) is a domain; \(S\) is the closure of the image of the irreducible variety \(X\times X\) under addition. Thus both cones are irreducible. Working over \(\mathbb C\) supplies the generic smoothness/separability needed for the differential-rank argument.

- **The singular-cone identification is genuinely affine and scheme-theoretic.**  
  `organized/research/external/m8_hmsv/0809.1233v1/8pts-090708.tex:245–255` states that the fourteen partial derivatives generate the defining ideal of the affine \(M_8\) cone.

- **The Fourier-coordinate transport is sufficient.**  
  `organized/research/HMSV_COMPATIBILITY.md:48–56` supplies an invertible bridge \(L\) and
  \[
  \Phi_F(Lv)=\alpha\Phi_{\rm primitive}(v),\qquad \alpha=-20736.
  \]
  Differentiation gives
  \[
  G_F(Lv)=\alpha L^{-T}G_{\rm primitive}(v),
  \]
  so image dimensions transport correctly, as do Hessian ranks through the displayed congruence.

**Neither the suppressed septic argument nor the determinant-square inference is needed.** The dependency separation at `organized/research/CORANK_TWO_LIFT_EXACTNESS.md:20–25` is sound.

### 2. Global minors argument and adjoint factors: PASS

The proof at `organized/research/CORANK_TWO_LIFT_EXACTNESS.md:35–58` is valid:

1. Generically on the smooth 12-dimensional \(S\),
   \[
   \operatorname{rank}(H_f|_{T_fS})\le10.
   \]
   Hence \(\dim\ker H_f\ge2\).
2. Every \(13\times13\) Hessian minor therefore vanishes on a dense open subset and consequently everywhere on \(S\).
3. Fixing \(P=(U,K)\), the corresponding bordered minors of \(P^TH_xP\) vanish on \(S\). Their differentials at \(f\) are exactly
   \[
   \det(C)(K^TH_hK)_{ij}.
   \]
4. A polynomial vanishing on the reduced variety has differential zero on its **full Zariski tangent space**, including at singular points. Thus
   \[
   T_fS\subseteq\ker(h\mapsto K^TH_hK).
   \]
5. Cubic polarization gives the stated factors:
   \[
   K^TH_hK=
   \begin{pmatrix}
   2b_0^Th&b_1^Th\\
   b_1^Th&2b_2^Th
   \end{pmatrix}.
   \]
   Therefore this map has the same rank as \(B_f\), proving both
   \[
   \operatorname{rank}B_f\le2,\qquad
   \operatorname{im}B_f\subseteq(T_fS)^\perp.
   \]

### 3. Consequences and exceptional ranks: PASS

The conclusions at `organized/research/CORANK_TWO_LIFT_EXACTNESS.md:62–75` follow:

- \(g=G(f)\neq0\): otherwise \(f\in X\), and \(H_f\) annihilates \(T_fX\), whose dimension is at least six, forcing Hessian rank at most eight.
- If \(\operatorname{rank}B_f=2\), the conormal inclusion forces \(\dim T_fS=12\), hence smoothness and
  \[
  \operatorname{im}B_f=(T_fS)^\perp.
  \]
  Since \(\Phi|_S=0\), \(g\) belongs to that plane. **Compatibility is automatic.**
- Rank one requires compatibility followed by the positive-direction test.
- Rank zero rejects because \(g\neq0\).
- A singular **actual** rank-12 point must have restriction rank one and tangent dimension thirteen: actuality supplies a lift, excluding restriction rank zero.

The constructive PSD lemma at `organized/research/JOINT_CERTIFICATE_RANK.md:169–181` is correct, including its rank-zero qualification and lack of compactness assumptions. Combining it with the global restriction-rank theorem proves the stated PSD exactness.

### 4. Algorithm and exact examples: PASS

At `organized/research/CORANK_TWO_LIFT_EXACTNESS.md:79–91`, rank two ensures that \(r\) is a nonzero binary quadratic. Its at most two real projective roots give at most four real lifts after the sign test and **both** scaling choices.

For rational input, choose rational \(K,n\). A projective root lies in an extension of degree at most two; adjoining its normalization square root adds degree at most two. Thus the lift coordinates lie in an extension of degree at most four. Rank-one feasibility is correctly treated separately and need not have finitely many lifts.

Both read-only reproductions passed:

```text
python -B organized/research/verify_joint_certificate_rank.py --check-record
python -B organized/research/verify_m8_fourier_bridge.py --check-record
```

They confirmed the complete normal forms, all fourteen adjoint identities, and the nonzero restriction minor reported at `organized/research/CORANK_TWO_LIFT_EXACTNESS.md:95–109`:

- Actual point: \(q=1/576\) and \(-23/193442\) on the two root directions; precisely \(y=\pm K(284,24)\).
- Fake secant: \(q=-1/324\) and \(-1/100\); no real lift.
- The displayed nonzero minor establishes occurrence of rank two and therefore generic rank two on the nonempty rank-12 chart.

These are regression checks, **not** the justification for universality.

