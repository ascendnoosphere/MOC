import MOC.MixedBound
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FinCases

/-! The left-right unit quaternion representation of real rotations in dimension four. -/

open BigOperators Matrix
open scoped Quaternion RealInnerProductSpace

namespace MOC

noncomputable section

private abbrev quatCoords : ℍ ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)

private theorem quatCoords_zero (x : ℍ) : quatCoords x 0 = x.re := rfl
private theorem quatCoords_one (x : ℍ) : quatCoords x 1 = x.imI := rfl
private theorem quatCoords_two (x : ℍ) : quatCoords x 2 = x.imJ := rfl
private theorem quatCoords_three (x : ℍ) : quatCoords x 3 = x.imK := rfl

private theorem quatCoords_dot (x : ℍ) :
    quatCoords x ⬝ᵥ quatCoords x = Quaternion.normSq x := by
  simp only [dotProduct, Fin.sum_univ_four, quatCoords_zero, quatCoords_one, quatCoords_two,
    quatCoords_three, Quaternion.normSq_def', sq]

private theorem quatCoords_unit (x : ℍ) (hx : ‖x‖ = 1) : ∑ i, quatCoords x i ^ 2 = 1 := by
  have hnorm : Quaternion.normSq x = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hx, mul_one]
  simpa only [dotProduct, ← sq] using (quatCoords_dot x).trans hnorm

private def quaternionIsometry (U : Matrix (Fin 4) (Fin 4) ℝ) (hU : Uᵀ * U = 1) :
    ℍ ≃ₗᵢ[ℝ] ℍ where
  toLinearEquiv := quatCoords.trans
    ((Matrix.toLin'OfInv hU (Matrix.mul_eq_one_comm.mp hU)).trans quatCoords.symm)
  norm_map' x := by
    change ‖quatCoords.symm (U *ᵥ quatCoords x)‖ = ‖x‖
    apply (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp
    simp only [← Quaternion.normSq_eq_norm_mul_self, ← quatCoords_dot,
      LinearEquiv.apply_symm_apply]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hU, Matrix.vecMul_one]

private theorem quaternionIsometry_det (U : Matrix (Fin 4) (Fin 4) ℝ)
    (hU : Uᵀ * U = 1) : LinearMap.det (quaternionIsometry U hU).toLinearMap = U.det := by
  change LinearMap.det ((quatCoords.symm : (Fin 4 → ℝ) →ₗ[ℝ] ℍ) ∘ₗ Matrix.toLin' U ∘ₗ
    (quatCoords : ℍ →ₗ[ℝ] (Fin 4 → ℝ))) = U.det
  simpa only [LinearEquiv.symm_symm, LinearMap.det_toLin'] using
    LinearMap.det_conj (Matrix.toLin' U) quatCoords.symm

private theorem reflection_unit_quaternion (u : ℍ) (hu : ‖u‖ = 1) (x : ℍ) :
    (ℝ ∙ u)ᗮ.reflection x = (-u) * star x * u := by
  have hunit : star u * u = 1 := by
    simp [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hu]
  have hreal : u * star x + x * star u = (↑(2 * ⟪u, x⟫) : ℍ) := by
    simpa only [Quaternion.inner_def, StarMul.star_mul, star_star] using
      Quaternion.self_add_star' (u * star x)
  have hmul : u * star x * u + x = (2 * ⟪u, x⟫) • u := calc
    _ = (u * star x + x * star u) * u := by
      rw [add_mul, mul_assoc x (star u) u, hunit, mul_one]
    _ = _ := by rw [hreal, Quaternion.coe_mul_eq_smul]
  have htwo : (2 : ℕ) • (⟪u, x⟫ • u) = (2 * ⟪u, x⟫) • u := by
    rw [two_nsmul, two_mul, add_smul]
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_apply,
    Submodule.orthogonalProjection_unit_singleton ℝ hu, htwo, ← hmul]
  simp [neg_mul]

private theorem reflection_quaternion (v : ℍ) (hv : v ≠ 0) :
    ∃ u : ℍ, ‖u‖ = 1 ∧ ∀ x, (ℝ ∙ v)ᗮ.reflection x = (-u) * star x * u := by
  let u := ‖v‖⁻¹ • v
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖u‖ = 1 := by
    rw [show u = ‖v‖⁻¹ • v from rfl, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ hvn]
  have hspan : (ℝ ∙ u) = ℝ ∙ v :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hvn)) v
  refine ⟨u, hu, fun x => ?_⟩
  exact (congrArg (fun K : Submodule ℝ ℍ => Kᗮ.reflection x) hspan.symm).trans
    (reflection_unit_quaternion u hu x)

private def reflectionProduct (l : List ℍ) : ℍ ≃ₗᵢ[ℝ] ℍ :=
  (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod

private theorem reflectionProduct_quaternion (l : List ℍ) :
    ∃ q r : ℍ, ‖q‖ = 1 ∧ ‖r‖ = 1 ∧
      ((LinearMap.det (reflectionProduct l).toLinearMap = 1 ∧
        ∀ x, reflectionProduct l x = q * x * r) ∨
      (LinearMap.det (reflectionProduct l).toLinearMap = -1 ∧
        ∀ x, reflectionProduct l x = q * star x * r)) := by
  induction l with
  | nil =>
      refine ⟨1, 1, norm_one, norm_one, Or.inl ⟨?_, fun x => ?_⟩⟩
      · change LinearMap.det (LinearMap.id : ℍ →ₗ[ℝ] ℍ) = 1
        exact LinearMap.det_id
      · change x = 1 * x * 1
        simp
  | cons v l ih =>
      rw [show reflectionProduct (v :: l) = (ℝ ∙ v)ᗮ.reflection * reflectionProduct l from rfl]
      by_cases hv : v = 0
      · have hzero : (ℝ ∙ v)ᗮ.reflection = (1 : ℍ ≃ₗᵢ[ℝ] ℍ) := by
          apply LinearIsometryEquiv.ext
          intro x
          apply Submodule.reflection_mem_subspace_eq_self
          rw [hv, Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top]
          exact Submodule.mem_top
        simpa only [hzero, one_mul] using ih
      obtain ⟨u, hu, hreflection⟩ := reflection_quaternion v hv
      have hd : LinearMap.det ((ℝ ∙ v)ᗮ.reflection).toLinearMap = -1 := by
        rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
          finrank_span_singleton (K := ℝ) hv, pow_one]
      have hdet : LinearMap.det ((ℝ ∙ v)ᗮ.reflection * reflectionProduct l).toLinearMap =
          - LinearMap.det (reflectionProduct l).toLinearMap := by
        change LinearMap.det (((ℝ ∙ v)ᗮ.reflection).toLinearMap.comp
          (reflectionProduct l).toLinearMap) = _
        rw [LinearMap.det_comp, hd, neg_one_mul]
      obtain ⟨q, r, hq, hr, hform⟩ := ih
      refine ⟨(-u) * star r, star q * u, ?_, ?_, ?_⟩
      · simp [norm_mul, Quaternion.norm_star, hu, hr]
      · simp [norm_mul, Quaternion.norm_star, hu, hq]
      rcases hform with ⟨hd', hqform⟩ | ⟨hd', hqform⟩
      · refine Or.inr ⟨by rw [hdet, hd'], fun x => ?_⟩
        change (ℝ ∙ v)ᗮ.reflection (reflectionProduct l x) = _
        simp only [hreflection, hqform, StarMul.star_mul, mul_assoc]
      · refine Or.inl ⟨by rw [hdet, hd', neg_neg], fun x => ?_⟩
        change (ℝ ∙ v)ᗮ.reflection (reflectionProduct l x) = _
        simp only [hreflection, hqform, StarMul.star_mul, star_star, mul_assoc]

private theorem vector4_zero {R : Type*} (a b c d : R) : ![a, b, c, d] 0 = a := rfl
private theorem vector4_one {R : Type*} (a b c d : R) : ![a, b, c, d] 1 = b := rfl
private theorem vector4_two {R : Type*} (a b c d : R) : ![a, b, c, d] 2 = c := rfl
private theorem vector4_three {R : Type*} (a b c d : R) : ![a, b, c, d] 3 = d := rfl

private theorem quaternionRotation_mulVec (q r x : ℍ) :
    quaternionRotation (quatCoords q) (quatCoords r) *ᵥ quatCoords x = quatCoords (q * x * r) := by
  funext i
  have h : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases h i with rfl | rfl | rfl | rfl <;>
    simp only [quaternionRotation, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.of_apply, vector4_zero, vector4_one, vector4_two, vector4_three,
      quatCoords_zero, quatCoords_one, quatCoords_two, quatCoords_three,
      Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ, Quaternion.mul_imK] <;> ring

/-- Every real special orthogonal matrix of order four is left and right multiplication
by real unit quaternions in the basis `1, i, j, k`. -/
theorem exists_quaternionRotation_of_specialOrthogonal (U : Matrix (Fin 4) (Fin 4) ℝ)
    (hU : Uᵀ * U = 1) (hdet : U.det = 1) :
    ∃ q r : Fin 4 → ℝ, (∑ i, q i ^ 2) = 1 ∧ (∑ i, r i ^ 2) = 1 ∧
      U = quaternionRotation q r := by
  let φ := quaternionIsometry U hU
  obtain ⟨l, _, hl⟩ := φ.reflections_generate_dim
  change φ = reflectionProduct l at hl
  obtain ⟨q, r, hq, hr, hform⟩ := reflectionProduct_quaternion l
  have hφ : LinearMap.det φ.toLinearMap = 1 := (quaternionIsometry_det U hU).trans hdet
  have hmul : ∀ x, φ x = q * x * r := by
    rcases hform with ⟨_, hm⟩ | ⟨hd, _⟩
    · simpa only [hl] using hm
    · rw [hl, hd] at hφ
      norm_num at hφ
  refine ⟨quatCoords q, quatCoords r, quatCoords_unit q hq, quatCoords_unit r hr, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro i
  have hx := congrArg quatCoords (hmul (quatCoords.symm (Pi.single i 1)))
  change quatCoords (quatCoords.symm (U *ᵥ quatCoords (quatCoords.symm (Pi.single i 1)))) = _ at hx
  rw [← quaternionRotation_mulVec] at hx
  simpa only [LinearEquiv.apply_symm_apply] using hx

/-- A row sign change suffices to bring any real orthogonal four-matrix into
unit quaternion coordinates. The row signs disappear on squaring minors. -/
theorem exists_quaternionRotation_after_row_signs (U : Matrix (Fin 4) (Fin 4) ℝ)
    (hU : Uᵀ * U = 1) :
    ∃ s q r : Fin 4 → ℝ, (∀ i, s i ^ 2 = 1) ∧ (∑ i, q i ^ 2) = 1 ∧
      (∑ i, r i ^ 2) = 1 ∧ diagonal s * U = quaternionRotation q r := by
  let s (i : Fin 4) := if i = 0 then U.det else 1
  let D := diagonal s
  have hdet : U.det ^ 2 = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using
      congrArg Matrix.det hU
  have hs (i : Fin 4) : s i ^ 2 = 1 := by
    by_cases hi : i = 0 <;> simp [s, hi, hdet]
  have hD : D * D = 1 := by
    change diagonal s * diagonal s = _
    rw [Matrix.diagonal_mul_diagonal]
    have h : (fun i => s i * s i) = fun _ => (1 : ℝ) := by
      funext i
      simpa only [pow_two] using hs i
    rw [h, Matrix.diagonal_one]
  have hDt : Dᵀ = D := Matrix.diagonal_transpose _
  have hDU : (D * U)ᵀ * (D * U) = 1 := calc
    _ = Uᵀ * ((D * D) * U) := by simp only [Matrix.transpose_mul, hDt, Matrix.mul_assoc]
    _ = 1 := by rw [hD, Matrix.one_mul, hU]
  have hDdet : D.det = U.det := by
    simp [D, Matrix.det_diagonal, Fin.prod_univ_four, s]
  have hDUdet : (D * U).det = 1 := by
    rw [Matrix.det_mul, hDdet, ← pow_two, hdet]
  obtain ⟨q, r, hq, hr, hrot⟩ := exists_quaternionRotation_of_specialOrthogonal (D * U) hDU hDUdet
  exact ⟨s, q, r, hs, hq, hr, hrot⟩

end

end MOC
