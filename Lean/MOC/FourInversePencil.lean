import MOC.FourKleinSpectralSquares
import MOC.FourSupportConeClassification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Lean.Elab.Tactic.Omega

/-! The order-four inverse pencil in row-major tetrahedral coordinates. -/

open BigOperators Matrix

namespace MOC

private def inverseRow (i : Fin 9) : Fin 3 := ⟨i.val / 3, by omega⟩
private def inverseCol (i : Fin 9) : Fin 3 := ⟨i.val % 3, by omega⟩

-- These are twice the rows of the tetrahedral frame, with the constant column removed.
private def inverseFrameRow (i : Fin 4) : Fin 3 → ℤ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]] i

private def inverseSkew (v : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, v 2, -v 1; -v 2, 0, v 0; v 1, -v 0, 0]

-- Twice the cross products of the tetrahedral rows in lexicographic pair order.
private def inversePairRow (i : Fin 6) : Fin 3 → ℤ :=
  ![![0, 1, -1], ![-1, 0, 1], ![1, -1, 0],
    ![1, 1, 0], ![-1, 0, -1], ![0, 1, 1]] i

private def inversePairSign (i : Fin 6) : ℤ := ![-1, 1, -1, -1, 1, -1] i
private def inversePairCompl (i : Fin 6) : Fin 6 := ⟨5 - i.val, by omega⟩

/-- The integer matrix of an ordinary matching indicator. Its quadratic
form is thirty-two times the corresponding inverse-coordinate polynomial. -/
def fourInverseRayMatrix (r : Fin 34) : Matrix (Fin 9) (Fin 9) ℤ := fun i j =>
  if r.val < 16 then
    let a : Fin 4 := ⟨r.val / 4 % 4, by omega⟩
    let b : Fin 4 := ⟨r.val % 4, by omega⟩
    inverseSkew (inverseFrameRow a) (inverseRow i) (inverseRow j) *
      inverseSkew (inverseFrameRow b) (inverseCol i) (inverseCol j)
  else
    let a : Fin 6 := ⟨(r.val - 16) / 6 % 6, by omega⟩
    let b : Fin 6 := ⟨(r.val - 16) % 6, by omega⟩
    let v (k : Fin 9) := inversePairRow a (inverseRow k) * inversePairRow b (inverseCol k)
    let w (k : Fin 9) := inversePairRow (inversePairCompl a) (inverseRow k) *
      inversePairRow (inversePairCompl b) (inverseCol k)
    inversePairSign a * inversePairSign b * (v i * w j + w i * v j)

/-- Add the scaled inverse matrices with the supplied ordinary-ray coefficients. -/
def fourInversePencil {R : Type*} [CommRing R] (c : Fin 34 → R) :
    Matrix (Fin 9) (Fin 9) R :=
  fun i j => ∑ r, c r * (fourInverseRayMatrix r i j : R)

set_option maxRecDepth 2048 in
private theorem inverse_ray_symmetric (r : Fin 34) (i j : Fin 9) :
    fourInverseRayMatrix r j i = fourInverseRayMatrix r i j := by
  revert r i j
  decide +kernel

theorem fourInversePencil_symmetric {R : Type*} [CommRing R] (c : Fin 34 → R) :
    (fourInversePencil c)ᵀ = fourInversePencil c := by
  ext i j
  simp only [Matrix.transpose_apply, fourInversePencil, inverse_ray_symmetric]

noncomputable section

/-- Flatten the three-by-three inverse coordinate matrix in row-major order. -/
def fourInversePencilCoordinates (H : Matrix (Fin 3) (Fin 3) ℝ) : Fin 9 → ℝ :=
  ![H 0 0, H 0 1, H 0 2, H 1 0, H 1 1, H 1 2, H 2 0, H 2 1, H 2 2]

private def inverseUnvec {R : Type*} [CommRing R] : (Fin 9 → R) →ₗ[R] Matrix (Fin 3) (Fin 3) R where
  toFun x := !![x 0, x 1, x 2; x 3, x 4, x 5; x 6, x 7, x 8]
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' c x := by ext i j; fin_cases i <;> fin_cases j <;> rfl

private theorem inverseCoordinates_unvec (x : Fin 9 → ℝ) :
    fourInversePencilCoordinates (inverseUnvec x) = x := by
  funext i
  fin_cases i <;> rfl

private theorem inverseCoordinates_scale (c : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    fourInversePencilCoordinates (c • H) = c • fourInversePencilCoordinates H := by
  funext i
  fin_cases i <;> rfl

-- Each case is the centered singleton or complementary-pair expansion.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 64000000 in
private theorem inverse_ray_form (r : Fin 34) (K : Matrix (Fin 3) (Fin 3) ℝ) :
    32 * kleinSignedCost (ordinaryCostRay r) (kleinCenteredMatrix K) =
      fourInversePencilCoordinates (kleinCofactor K) ⬝ᵥ
        ((fun i j => (fourInverseRayMatrix r i j : ℝ)) *ᵥ
          fourInversePencilCoordinates (kleinCofactor K)) := by
  fin_cases r <;>
    norm_num [kleinSignedCost, ordinaryCostRay, ordinaryCostRayInt, fourCostPermutation,
      fourCostPair, fourInverseRayMatrix, inverseRow, inverseCol, inverseFrameRow,
      inverseSkew, inversePairRow, inversePairSign, inversePairCompl, kleinPermutationSign,
      kleinCenteredMatrix, kleinTetrahedralColumns, kleinCofactor, fourInversePencilCoordinates,
      fourPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.prod_univ_four, Matrix.cons_val] <;>
    ring

private theorem inverse_signedCost_sum (c : Fin 34 → ℝ) (K : Matrix (Fin 3) (Fin 3) ℝ) :
    kleinSignedCost (fun p => ∑ r, c r * ordinaryCostRay r p) (kleinCenteredMatrix K) =
      ∑ r, c r * kleinSignedCost (ordinaryCostRay r) (kleinCenteredMatrix K) := by
  simp only [kleinSignedCost, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem inverse_pencil_form_sum (c : Fin 34 → ℝ) (x : Fin 9 → ℝ) :
    x ⬝ᵥ (fourInversePencil c *ᵥ x) =
      ∑ r, c r * (x ⬝ᵥ ((fun i j => (fourInverseRayMatrix r i j : ℝ)) *ᵥ x)) := by
  let t (i j : Fin 9) (r : Fin 34) := x i * (c r * (fourInverseRayMatrix r i j : ℝ)) * x j
  calc
    _ = ∑ i, ∑ j, ∑ r, t i j r := by
      simp only [fourInversePencil, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, t]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ i, ∑ r, ∑ j, t i j r := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ i, ∑ j, t i j r := Finset.sum_comm
    _ = _ := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, t]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem inverse_form_scale (Q : Matrix (Fin 9) (Fin 9) ℝ)
    (c : ℝ) (x : Fin 9 → ℝ) :
    (c • x) ⬝ᵥ (Q *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (Q *ᵥ x)) := by
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Evaluate the scaled inverse pencil at the inverse transpose of the
centered coordinate matrix. -/
theorem fourInversePencil_form_of_inverse (c : Fin 34 → ℝ)
    (K H : Matrix (Fin 3) (Fin 3) ℝ) (hKH : K * Hᵀ = 1) :
    32 * kleinSignedCost (fun p => ∑ r, c r * ordinaryCostRay r p) (kleinCenteredMatrix K) =
      K.det ^ 2 * (fourInversePencilCoordinates H ⬝ᵥ (fourInversePencil c *ᵥ fourInversePencilCoordinates H)) := by
  rw [inverse_signedCost_sum, Finset.mul_sum, ← inverse_form_scale,
    ← inverseCoordinates_scale, ← kleinCofactor_eq_det_smul K H hKH, inverse_pencil_form_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← inverse_ray_form]
  ring

/-- The scaled real pencil of a spectral gap is the real part of the
bordered inverse-coordinate determinant with the negative support phase. -/
theorem fourInversePencil_form_of_spectralGap (c : Fin 34 → ℝ) (a b : Fin 4 → ℂ)
    (η : ℂ) (h : ℝ)
    (hgap : ∀ p, (∑ r, c r * ordinaryCostRay r p) =
      h - (η * matchingProduct a b (fourPerm p).symm).re)
    (H : Matrix (Fin 3) (Fin 3) ℝ) :
    fourInversePencilCoordinates H ⬝ᵥ (fourInversePencil c *ᵥ fourInversePencilCoordinates H) =
      ((-32 * η) * SpectralProfile.tetrahedralInverseProfile a b (kleinComplexification H)).re := by
  let Q (X : Matrix (Fin 3) (Fin 3) ℝ) :=
    fourInversePencilCoordinates X ⬝ᵥ (fourInversePencil c *ᵥ fourInversePencilCoordinates X)
  have hQ : Continuous Q := by
    dsimp only [Q, dotProduct, Matrix.mulVec, fourInversePencilCoordinates]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    fun_prop
  apply klein_tetrahedral_continuous_eq_of_invertible a b (-32 * η) Q hQ _ H
  intro W hW
  let K := (Wᵀ)⁻¹
  have hunit : IsUnit Wᵀ.det := isUnit_iff_ne_zero.mpr (by rwa [Matrix.det_transpose])
  have hKW : K * Wᵀ = 1 := Matrix.nonsing_inv_mul _ hunit
  have hWK : Wᵀ * K = 1 := Matrix.mul_nonsing_inv _ hunit
  have hK : K.det ≠ 0 := by
    have hm := congrArg Matrix.det hKW
    rw [Matrix.det_mul, Matrix.det_one] at hm
    intro hz
    rw [hz, zero_mul] at hm
    exact zero_ne_one hm
  have hcost : (fun p => ∑ r, c r * ordinaryCostRay r p) = kleinRealCost a b η h :=
    funext hgap
  have hcal := fourInversePencil_form_of_inverse c K W hKW
  rw [hcost, kleinSignedCost_spectral a b η h K W hWK hKW] at hcal
  have hphase (z : ℂ) : ((-32 * η) * z).re = -32 * (η * z).re := by
    rw [mul_assoc, show (-32 : ℂ) = ((-32 : ℝ) : ℂ) by norm_num]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hphase]
  change fourInversePencilCoordinates W ⬝ᵥ (fourInversePencil c *ᵥ fourInversePencilCoordinates W) = _
  apply mul_left_cancel₀ (pow_ne_zero 2 hK)
  linear_combination -hcal

private theorem inverse_form_polar (Q : Matrix (Fin 9) (Fin 9) ℝ)
    (hQ : Qᵀ = Q) (x y : Fin 9 → ℝ) :
    (x + y) ⬝ᵥ (Q *ᵥ (x + y)) =
      (x ⬝ᵥ (Q *ᵥ x)) + (y ⬝ᵥ (Q *ᵥ y)) + 2 * (y ⬝ᵥ (Q *ᵥ x)) := by
  have hcross : x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ, dotProduct_comm]
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, hcross]
  ring

private theorem inverse_symmetric_eq_of_form {P Q : Matrix (Fin 9) (Fin 9) ℝ}
    (hP : Pᵀ = P) (hQ : Qᵀ = Q)
    (h : ∀ x : Fin 9 → ℝ, x ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (Q *ᵥ x)) : P = Q := by
  ext i j
  let x : Fin 9 → ℝ := Pi.single j 1
  let y : Fin 9 → ℝ := Pi.single i 1
  have he := h (x + y)
  rw [inverse_form_polar P hP, inverse_form_polar Q hQ, h x, h y] at he
  have him (M : Matrix (Fin 9) (Fin 9) ℝ) : y ⬝ᵥ (M *ᵥ x) = M i j := by
    simp only [y, x, Matrix.mulVec_single_one, single_dotProduct, one_mul]
  rw [him P, him Q] at he
  linarith only [he]

private theorem inverse_form_complex_re (M : Matrix (Fin 9) (Fin 9) ℂ) (x : Fin 9 → ℝ) :
    ((fun i => (x i : ℂ)) ⬝ᵥ (M *ᵥ (fun i => (x i : ℂ)))).re =
       x ⬝ᵥ ((fun i j => (M i j).re) *ᵥ x) := by
  simp only [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]

private theorem inverse_form_complex_im (M : Matrix (Fin 9) (Fin 9) ℂ) (x : Fin 9 → ℝ) :
    ((fun i => (x i : ℂ)) ⬝ᵥ (M *ᵥ (fun i => (x i : ℂ)))).im =
       x ⬝ᵥ ((fun i j => (M i j).im) *ᵥ x) := by
  simp only [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero]

private theorem inverse_spectralGram (a b : Fin 4 → ℂ) (η : ℂ) :
    ∃ C : Matrix (Fin 9) (Fin 4) ℂ,
      ∀ x : Fin 9 → ℂ, x ⬝ᵥ ((C * Cᵀ) *ᵥ x) =
        η * SpectralProfile.tetrahedralInverseProfile a b (inverseUnvec x) := by
  obtain ⟨L, hL⟩ := SpectralProfile.tetrahedralInverseProfile_four_squares a b η
  let F (k : Fin 4) := (L k).comp (inverseUnvec (R := ℂ))
  let C : Matrix (Fin 9) (Fin 4) ℂ := fun i k => F k (Pi.single i 1)
  have hC (x : Fin 9 → ℂ) : Cᵀ *ᵥ x = fun i => F i x := by
    funext r
    change (∑ i, C i r * x i) = F r x
    rw [LinearMap.pi_apply_eq_sum_univ (F r) x]
    apply Finset.sum_congr rfl
    intro i _
    have he : (Pi.single i 1 : Fin 9 → ℂ) = fun j => if i = j then 1 else 0 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    simp only [C, he, smul_eq_mul, mul_comm]
  refine ⟨C, fun x => ?_⟩
  rw [← Matrix.mulVec_mulVec x C Cᵀ, dotProduct_mulVec, ← Matrix.mulVec_transpose, hC,
    hL (inverseUnvec x)]
  simp only [dotProduct, F, LinearMap.comp_apply, pow_two]

private theorem inverseUnvec_complexify (x : Fin 9 → ℝ) :
    inverseUnvec (fun i => (x i : ℂ)) = kleinComplexification (inverseUnvec x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem inverse_spectralGram_re (c : Fin 34 → ℝ) (a b : Fin 4 → ℂ)
    (η : ℂ) (h : ℝ)
    (hgap : ∀ p, (∑ r, c r * ordinaryCostRay r p) =
      h - (η * matchingProduct a b (fourPerm p).symm).re)
    (C : Matrix (Fin 9) (Fin 4) ℂ)
    (hC : ∀ x : Fin 9 → ℂ, x ⬝ᵥ ((C * Cᵀ) *ᵥ x) =
      (-32 * η) * SpectralProfile.tetrahedralInverseProfile a b (inverseUnvec x)) :
    fourInversePencil c = fun i j => ((C * Cᵀ) i j).re := by
  apply inverse_symmetric_eq_of_form (fourInversePencil_symmetric c)
  · ext i j
    have hs : (C * Cᵀ)ᵀ = C * Cᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    exact congrArg (fun M : Matrix (Fin 9) (Fin 9) ℂ => (M i j).re) hs
  · intro x
    have hp := fourInversePencil_form_of_spectralGap c a b η h hgap (inverseUnvec x)
    rw [inverseCoordinates_unvec] at hp
    rw [← inverse_form_complex_re, hC, inverseUnvec_complexify]
    exact hp

/-- The real pencil of an actual spectral gap is singular, including
when some matching products or inverse coordinates are singular. -/
theorem fourInversePencil_det_eq_zero_of_spectralGap (c : Fin 34 → ℝ) (a b : Fin 4 → ℂ)
    (η : ℂ) (h : ℝ)
    (hgap : ∀ p, (∑ r, c r * ordinaryCostRay r p) =
      h - (η * matchingProduct a b (fourPerm p).symm).re) :
    (fourInversePencil c).det = 0 := by
  obtain ⟨C, hC⟩ := inverse_spectralGram a b (-32 * η)
  have hP := inverse_spectralGram_re c a b η h hgap C hC
  let F : Matrix (Fin 9) (Fin 4 ⊕ Fin 4) ℝ :=
    fun i k => Sum.elim (fun r => (C i r).re) (fun r => (C i r).im) k
  let G : Matrix (Fin 4 ⊕ Fin 4) (Fin 9) ℝ :=
    fun k j => Sum.elim (fun r => (C j r).re) (fun r => -(C j r).im) k
  have hFG : fourInversePencil c = F * G := by
    rw [hP]
    ext i j
    simp only [F, G, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Complex.re_sum, Complex.mul_re, Finset.sum_sub_distrib,
      mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  have hr : (fourInversePencil c).rank ≤ 8 := by
    rw [hFG]
    have hf := (Matrix.rank_mul_le_left F G).trans (Matrix.rank_le_card_width F)
    simpa only [Fintype.card_sum, Fintype.card_fin] using hf
  by_contra hn
  have hu := Matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hn)
  rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin] at hr
  omega

/-- Each strictly positive subspace of the real pencil of an actual
spectral gap has real dimension at most four. -/
theorem fourInversePencil_positive_dimension_of_spectralGap
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (c : Fin 34 → ℝ) (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ)
    (hgap : ∀ p, (∑ r, c r * ordinaryCostRay r p) =
      h - (η * matchingProduct a b (fourPerm p).symm).re)
    (J : W →ₗ[ℝ] (Fin 9 → ℝ))
    (hpos : ∀ x : W, x ≠ 0 → 0 < J x ⬝ᵥ (fourInversePencil c *ᵥ J x)) :
    Module.finrank ℝ W ≤ 4 := by
  let E := SpectralProfile.tetrahedralFrame
  let A := Eᵀ * diagonal (a ∘ finSumFinEquiv) * E
  let B := Eᵀ * diagonal (b ∘ finSumFinEquiv) * E
  let T := SpectralProfile.inverseCore A.toBlocks₂₂ B.toBlocks₂₂
  let L := kleinComplexification.comp ((inverseUnvec (R := ℝ)).comp J)
  apply SpectralProfile.border_det_four_positive_dimension A.toBlocks₁₂ B.toBlocks₂₁ T
    (-32 * η) L
  intro x hx
  have hp := fourInversePencil_form_of_spectralGap c a b η h hgap (inverseUnvec (J x))
  rw [inverseCoordinates_unvec] at hp
  rw [show ((-32 * η) * (SpectralProfile.border A.toBlocks₁₂ B.toBlocks₂₁
      (T (L x))).det).re = _ from hp.symm]
  exact hpos x hx

/-- Each strictly negative subspace of the real pencil of an actual
spectral gap also has real dimension at most four. -/
theorem fourInversePencil_negative_dimension_of_spectralGap
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (c : Fin 34 → ℝ) (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ)
    (hgap : ∀ p, (∑ r, c r * ordinaryCostRay r p) =
      h - (η * matchingProduct a b (fourPerm p).symm).re)
    (J : W →ₗ[ℝ] (Fin 9 → ℝ))
    (hneg : ∀ x : W, x ≠ 0 → J x ⬝ᵥ (fourInversePencil c *ᵥ J x) < 0) :
    Module.finrank ℝ W ≤ 4 := by
  let E := SpectralProfile.tetrahedralFrame
  let A := Eᵀ * diagonal (a ∘ finSumFinEquiv) * E
  let B := Eᵀ * diagonal (b ∘ finSumFinEquiv) * E
  let T := SpectralProfile.inverseCore A.toBlocks₂₂ B.toBlocks₂₂
  let L := kleinComplexification.comp ((inverseUnvec (R := ℝ)).comp J)
  apply SpectralProfile.border_det_four_negative_dimension A.toBlocks₁₂ B.toBlocks₂₁ T
    (-32 * η) L
  intro x hx
  have hp := fourInversePencil_form_of_spectralGap c a b η h hgap (inverseUnvec (J x))
  rw [inverseCoordinates_unvec] at hp
  rw [show ((-32 * η) * (SpectralProfile.border A.toBlocks₁₂ B.toBlocks₂₁
      (T (L x))).det).re = _ from hp.symm]
  exact hneg x hx

/-- The imaginary part of the matching profile supplies a compatible
ordinary-ray pencil. Together the two parts have complex rank at most four. -/
theorem fourInversePencil_exists_rank_four_lift
    (c : Fin 34 → ℝ) (a b : Fin 4 → ℂ) (η : ℂ) (h : ℝ)
    (hgap : ∀ p, (∑ r, c r * ordinaryCostRay r p) =
      h - (η * matchingProduct a b (fourPerm p).symm).re) :
    ∃ d : Fin 34 → ℝ,
      (fun i j => ((fourInversePencil c i j : ℝ) : ℂ) +
        Complex.I * ((fourInversePencil d i j : ℝ) : ℂ) : Matrix (Fin 9) (Fin 9) ℂ).rank ≤ 4 := by
  let m (j : Fin 14) :=
    (Complex.I * η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re
  have hm : fourMatchingEvaluation m ∈
      (Submodule.span ℝ (Set.range ordinaryCostRay) : Set (Fin 24 → ℝ)) := by
    rw [← four_matching_space_eq_ordinary_span]
    exact ⟨m, rfl⟩
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun
    (R := ℝ) (v := ordinaryCostRay)).mp hm
  refine ⟨d, ?_⟩
  have hgapIm (p : Fin 24) : (∑ r, d r * ordinaryCostRay r p) =
      0 - ((-Complex.I * η) * matchingProduct a b (fourPerm p).symm).re := by
    have hh := congrFun hd p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
    rw [hh]
    change fourMatchingEvaluation
      (fun j => ((Complex.I * η) * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re) p = _
    rw [fourMatchingEvaluation_spectral_real_part]
    simp only [neg_mul, Complex.neg_re, zero_sub, neg_neg]
  obtain ⟨C, hC⟩ := inverse_spectralGram a b (-32 * η)
  have hRe := inverse_spectralGram_re c a b η h hgap C hC
  have hIm : fourInversePencil d = fun i j => ((C * Cᵀ) i j).im := by
    apply inverse_symmetric_eq_of_form (fourInversePencil_symmetric d)
    · ext i j
      have hs : (C * Cᵀ)ᵀ = C * Cᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      exact congrArg (fun M : Matrix (Fin 9) (Fin 9) ℂ => (M i j).im) hs
    · intro x
      have hp := fourInversePencil_form_of_spectralGap d a b (-Complex.I * η) 0 hgapIm
        (inverseUnvec x)
      rw [inverseCoordinates_unvec] at hp
      rw [← inverse_form_complex_im, hC, inverseUnvec_complexify, hp]
      let z := SpectralProfile.tetrahedralInverseProfile a b (kleinComplexification (inverseUnvec x))
      change ((-32 * (-Complex.I * η)) * z).re = ((-32 * η) * z).im
      rw [show (-32 * (-Complex.I * η)) * z = -Complex.I * ((-32 * η) * z) by ring]
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
        one_mul, zero_sub, neg_neg]
  have hlift : (fun i j => ((fourInversePencil c i j : ℝ) : ℂ) +
      Complex.I * ((fourInversePencil d i j : ℝ) : ℂ) : Matrix (Fin 9) (Fin 9) ℂ) = C * Cᵀ := by
    rw [hRe, hIm]
    ext i j
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
        one_mul, sub_zero, zero_add, add_zero]
  rw [hlift]
  exact (Matrix.rank_mul_le_left C Cᵀ).trans (Matrix.rank_le_width C)

end

end MOC
