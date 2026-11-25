import MOC.FourSymmetricSixContact
import MOC.FourKleinSpectralSquares

/-! The nine-dimensional inverse-coordinate pencil for the symmetric
six-contact family. The two borders in the spectral determinant bound
force a real null vector for this pencil. -/

open BigOperators Matrix

namespace MOC

/-- Integer matrices for the nine squared-minor rays, before imposing
the linear relation between their coefficients. -/
def symmetricSixContactRayPencil (k : Fin 9) : Matrix (Fin 9) (Fin 9) ℤ :=
  ![!![0, 0, 0, 0, 1, -1, 0, -1, 1;
      0, 0, 0, -1, 0, 1, 1, 0, -1;
      0, 0, 0, 1, -1, 0, -1, 1, 0;
      0, -1, 1, 0, 0, 0, 0, 1, -1;
      1, 0, -1, 0, 0, 0, -1, 0, 1;
      -1, 1, 0, 0, 0, 0, 1, -1, 0;
      0, 1, -1, 0, -1, 1, 0, 0, 0;
      -1, 0, 1, 1, 0, -1, 0, 0, 0;
      1, -1, 0, -1, 1, 0, 0, 0, 0],
    !![0, 0, 0, 0, -1, -1, 0, 1, 1;
      0, 0, 0, 1, 0, 1, -1, 0, -1;
      0, 0, 0, 1, -1, 0, -1, 1, 0;
      0, 1, 1, 0, 0, 0, 0, 1, 1;
      -1, 0, -1, 0, 0, 0, -1, 0, -1;
      -1, 1, 0, 0, 0, 0, -1, 1, 0;
      0, -1, -1, 0, -1, -1, 0, 0, 0;
      1, 0, 1, 1, 0, 1, 0, 0, 0;
      1, -1, 0, 1, -1, 0, 0, 0, 0],
    !![0, 0, 0, 0, 1, 1, 0, 1, 1;
      0, 0, 0, -1, 0, 1, -1, 0, 1;
      0, 0, 0, -1, -1, 0, -1, -1, 0;
      0, -1, -1, 0, 0, 0, 0, 1, 1;
      1, 0, -1, 0, 0, 0, -1, 0, 1;
      1, 1, 0, 0, 0, 0, -1, -1, 0;
      0, -1, -1, 0, -1, -1, 0, 0, 0;
      1, 0, -1, 1, 0, -1, 0, 0, 0;
      1, 1, 0, 1, 1, 0, 0, 0, 0],
    !![0, 0, 0, 0, -1, 1, 0, -1, 1;
      0, 0, 0, 1, 0, 1, 1, 0, 1;
      0, 0, 0, -1, -1, 0, -1, -1, 0;
      0, 1, -1, 0, 0, 0, 0, 1, -1;
      -1, 0, -1, 0, 0, 0, -1, 0, -1;
      1, 1, 0, 0, 0, 0, 1, 1, 0;
      0, 1, -1, 0, -1, 1, 0, 0, 0;
      -1, 0, -1, 1, 0, 1, 0, 0, 0;
      1, 1, 0, -1, -1, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0, 2, 0;
      0, 0, 0, 0, -2, 0, -2, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, -2, 0, -2, 0, 0;
      0, 0, 0, 2, 0, 0, 0, 2, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0],
    !![2, 0, 0, 0, 0, 0, 0, 0, 2;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, -2, 0, 0, 0, -2, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, -2, 0, 0, 0, -2, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      2, 0, 0, 0, 0, 0, 0, 0, 2],
    !![0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 2, 0, 0, 0, 2, 0, 0, 0;
      0, 0, -2, 0, -2, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, -2, 0, -2, 0, 0, 0, 0;
      0, 2, 0, 0, 0, 2, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -2, 0, 0, 0, 0, -2;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 2, 2, 0, 0;
      0, 0, 0, 0, 0, 2, 2, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, -2, 0, 0, 0, 0, -2],
    !![-2, 0, 0, 0, 0, 0, 0, 2, 0;
      0, 2, 0, 0, 0, 0, -2, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, -2, 0, 0, 0, 0, 2, 0, 0;
      2, 0, 0, 0, 0, 0, 0, -2, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0]] k

def symmetricSixContactPencil {R : Type*} [CommRing R] (b : Fin 7 → R) (λ : R) :
    Matrix (Fin 9) (Fin 9) R :=
  fun i j => ∑ k, (![b 0, b 1 + λ, b 2 + λ, b 3, b 4, b 5, b 6, λ, -λ] : Fin 9 → R) k *
    (symmetricSixContactRayPencil k i j : R)

noncomputable section

private def pencilCoordinates (H : Matrix (Fin 3) (Fin 3) ℝ) : Fin 9 → ℝ :=
  ![H 0 0, H 0 1, H 0 2, H 1 0, H 1 1, H 1 2, H 2 0, H 2 1, H 2 2]

private def pencilUnvec (x : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x 0, x 1, x 2; x 3, x 4, x 5; x 6, x 7, x 8]

private theorem pencilCoordinates_unvec (x : Fin 9 → ℝ) :
    pencilCoordinates (pencilUnvec x) = x := by
  funext i
  fin_cases i <;> rfl

private def pencilUnvecLinear : (Fin 9 → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ where
  toFun := pencilUnvec
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' c x := by ext i j; fin_cases i <;> fin_cases j <;> rfl

private def rayIndicator (k : Fin 9) (i : Fin 24) : ℝ :=
  if k ∈ symmetricSixContactActiveMinors i then 1 else 0

private theorem signedCost_profile (b : Fin 7 → ℝ) (λ : ℝ) (S : Matrix (Fin 4) (Fin 4) ℝ) :
    kleinSignedCost (symmetricSixContactProfile b λ) S =
      ∑ k, symmetricSixContactWeights b λ k * kleinSignedCost (rayIndicator k) S := by
  have hterm (i : Fin 24) : symmetricSixContactProfile b λ i =
      ∑ k, symmetricSixContactWeights b λ k * rayIndicator k i := by
    simp only [symmetricSixContactProfile, symmetricSixContactMinorAgreement, rayIndicator,
      mul_ite, mul_one, mul_zero]
  simp only [kleinSignedCost, hterm, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option maxHeartbeats 16000000 in
private theorem ray_pencil_identity (k : Fin 9) (K : Matrix (Fin 3) (Fin 3) ℝ) :
    32 * kleinSignedCost (rayIndicator k) (kleinCenteredMatrix K) =
      (pencilCoordinates (kleinCofactor K)) ⬝ᵥ
        ((fun i j => (symmetricSixContactRayPencil k i j : ℝ)) *ᵥ
          pencilCoordinates (kleinCofactor K)) := by
  fin_cases k <;>
    norm_num [kleinSignedCost, rayIndicator, symmetricSixContactActiveMinors,
      symmetricSixContactRayPencil, kleinPermutationSign, kleinCenteredMatrix,
      kleinTetrahedralColumns, kleinCofactor, pencilCoordinates, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Fin.prod_univ_four, Matrix.cons_val] <;>
    ring

private theorem pencil_form_sum (b : Fin 7 → ℝ) (λ : ℝ) (x : Fin 9 → ℝ) :
    x ⬝ᵥ (symmetricSixContactPencil b λ *ᵥ x) =
      ∑ k, symmetricSixContactWeights b λ k *
        (x ⬝ᵥ ((fun i j => (symmetricSixContactRayPencil k i j : ℝ)) *ᵥ x)) := by
  let term (i j k : Fin 9) := x i * (symmetricSixContactWeights b λ k *
    (symmetricSixContactRayPencil k i j : ℝ)) * x j
  calc
    _ = ∑ i, ∑ j, ∑ k, term i j k := by
      simp only [symmetricSixContactPencil, symmetricSixContactWeights, Matrix.mulVec, dotProduct,
        Finset.sum_mul, Finset.mul_sum, term]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ i, ∑ k, ∑ j, term i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, term i j k := Finset.sum_comm
    _ = _ := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, term]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem pencil_ray_symm (k i j : Fin 9) :
    symmetricSixContactRayPencil k j i = symmetricSixContactRayPencil k i j := by
  revert k i j
  decide +kernel

private theorem pencil_symm (b : Fin 7 → ℝ) (λ : ℝ) :
    (symmetricSixContactPencil b λ)ᵀ = symmetricSixContactPencil b λ := by
  ext i j
  simp only [Matrix.transpose_apply, symmetricSixContactPencil]
  apply Finset.sum_congr rfl
  intro k _
  rw [pencil_ray_symm k i j]

private theorem pencil_scale (c : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    pencilCoordinates (c • H) = c • pencilCoordinates H := by
  funext i
  fin_cases i <;> rfl

private theorem pencil_form_scale (Q : Matrix (Fin 9) (Fin 9) ℝ)
    (c : ℝ) (x : Fin 9 → ℝ) :
    (c • x) ⬝ᵥ (Q *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (Q *ᵥ x)) := by
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pencil_form_of_inverse (b : Fin 7 → ℝ) (λ : ℝ)
    (K H : Matrix (Fin 3) (Fin 3) ℝ) (hKH : K * Hᵀ = 1) :
    32 * kleinSignedCost (symmetricSixContactProfile b λ) (kleinCenteredMatrix K) =
      K.det ^ 2 * ((pencilCoordinates H) ⬝ᵥ
        (symmetricSixContactPencil b λ *ᵥ pencilCoordinates H)) := by
  rw [signedCost_profile, Finset.mul_sum, ← pencil_form_scale,
    ← pencil_scale, ← kleinCofactor_eq_det_smul K H hKH, pencil_form_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← ray_pencil_identity]
  ring

private theorem pencil_form_spectral (a c : Fin 4 → ℂ) (η : ℂ) (b : Fin 7 → ℝ) (λ h : ℝ)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b λ i) (H : Matrix (Fin 3) (Fin 3) ℝ) :
    pencilCoordinates H ⬝ᵥ (symmetricSixContactPencil b λ *ᵥ pencilCoordinates H) =
      ((32 * η) * SpectralProfile.tetrahedralInverseProfile a c (kleinComplexification H)).re := by
  let Q (H : Matrix (Fin 3) (Fin 3) ℝ) :=
    pencilCoordinates H ⬝ᵥ (symmetricSixContactPencil b λ *ᵥ pencilCoordinates H)
  have hQ : Continuous Q := by
    dsimp only [Q, dotProduct, Matrix.mulVec, pencilCoordinates]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    fun_prop
  apply klein_tetrahedral_continuous_eq_of_invertible a c (32 * η) Q hQ _ H
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
  have hcost : kleinRealCost a c (-η) h = symmetricSixContactProfile b λ := by
    funext i
    simpa only [kleinRealCost, neg_mul, Complex.neg_re, sub_neg_eq_add, add_comm] using hgap i
  have hcal := pencil_form_of_inverse b λ K W hKW
  rw [← hcost, kleinSignedCost_spectral a c (-η) h K W hWK hKW] at hcal
  have hphase (z : ℂ) : ((32 * η) * z).re = 32 * (η * z).re := by
    rw [mul_assoc, show (32 : ℂ) = ((32 : ℝ) : ℂ) by norm_num]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hphase]
  change pencilCoordinates W ⬝ᵥ (symmetricSixContactPencil b λ *ᵥ pencilCoordinates W) = _
  simp only [neg_mul, Complex.neg_re, mul_neg, neg_neg] at hcal
  apply mul_left_cancel₀ (pow_ne_zero 2 hK)
  linear_combination -hcal

private theorem symmetric_form_polar (Q : Matrix (Fin 9) (Fin 9) ℝ)
    (hsymm : Qᵀ = Q) (x y : Fin 9 → ℝ) :
    (x + y) ⬝ᵥ (Q *ᵥ (x + y)) =
      (x ⬝ᵥ (Q *ᵥ x)) + (y ⬝ᵥ (Q *ᵥ y)) + 2 * (y ⬝ᵥ (Q *ᵥ x)) := by
  have hcross : x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ (Q *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, hcross]
  ring

/-- Every actual spectral profile in this family has a singular real
inverse pencil. This includes all zero coefficient boundaries. -/
theorem symmetricSixContact_spectralPencil_singular (a c : Fin 4 → ℂ) (η : ℂ)
    (b : Fin 7 → ℝ) (λ h : ℝ)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b λ i) :
    (symmetricSixContactPencil b λ).det = 0 := by
  let Q := symmetricSixContactPencil b λ
  obtain ⟨L, hL⟩ := SpectralProfile.tetrahedralInverseProfile_four_squares a c (32 * η)
  let A (k : Fin 4) : (Fin 9 → ℝ) →ₗ[ℝ] ℂ :=
    ((L k).restrictScalars ℝ).comp (kleinComplexification.comp pencilUnvecLinear)
  let A₁ (k : Fin 4) := Complex.reLm.comp (A k)
  let A₂ (k : Fin 4) := Complex.imLm.comp (A k)
  let T : (Fin 9 → ℝ) →ₗ[ℝ] ((Fin 4 ⊕ Fin 4) → ℝ) :=
    LinearMap.pi (Sum.elim A₁ A₂)
  have hnot : ¬ Function.Injective T := by
    intro hi
    have hf := LinearMap.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hf
    norm_num at hf
  obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hnot
  let x := u - v
  have hx : x ≠ 0 := sub_ne_zero.mpr hne
  have hTx : T x = 0 := by rw [show x = u - v from rfl, map_sub, huv, sub_self]
  have hAx (k : Fin 4) : A k x = 0 := by
    apply Complex.ext
    · exact congrFun hTx (.inl k)
    · exact congrFun hTx (.inr k)
  have hform (z : Fin 9 → ℝ) :
      z ⬝ᵥ (Q *ᵥ z) = (∑ k, (A k z) ^ 2).re := by
    have hf := pencil_form_spectral a c η b λ h hgap (pencilUnvec z)
    rw [pencilCoordinates_unvec, hL] at hf
    exact hf
  have hQx : Q *ᵥ x = 0 := by
    have hxform : x ⬝ᵥ (Q *ᵥ x) = 0 := by
      rw [hform]
      simp only [hAx, zero_pow (by decide : 2 ≠ (0 : ℕ)), Finset.sum_const_zero, Complex.zero_re]
    funext i
    let e : Fin 9 → ℝ := Pi.single i 1
    have hadd : (x + e) ⬝ᵥ (Q *ᵥ (x + e)) = e ⬝ᵥ (Q *ᵥ e) := by
      simp only [hform, map_add, hAx, zero_add]
    rw [symmetric_form_polar Q (pencil_symm b λ) x e, hxform, zero_add] at hadd
    change (Q *ᵥ x) i = 0
    rw [show e ⬝ᵥ (Q *ᵥ x) = (Q *ᵥ x) i by simp only [e, single_dotProduct, one_mul]]
      at hadd
    linarith only [hadd]
  by_contra hn
  have hunit : IsUnit Q := Matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hn)
  exact hx (Matrix.mulVec_injective_iff_isUnit.mpr hunit (hQx.trans (Matrix.mulVec_zero Q).symm))

end

end MOC
