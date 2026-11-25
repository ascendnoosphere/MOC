import MOC.FourMatchingHessian
import MOC.FourSupportCostProfiles
import Mathlib.Tactic.LinearCombination

/-! The negative-height normalization and two eleven-contact Hessian
certificates for the order-four directional bound. -/

namespace MOC

noncomputable section

/-- A normalized external lower bound implies the upper support bound at
negative height. The premise is the directional conclusion of Drury,
Theorem 1.1 and Corollary 1.2, for the given spectra and mixer. -/
theorem four_support_le_of_external_lower_bound
    (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (η : ℂ) (H : ℝ)
    (hH : H < 0) (hmax : ∀ σ, (η * matchingProduct a b σ).re ≤ H)
    (hexternal : ∀ ξ : ℂ, (∀ σ, 1 ≤ (ξ * matchingProduct a b σ).re) →
      1 ≤ (ξ * determinantValue a b U).re) :
    (η * determinantValue a b U).re ≤ H := by
  have ht : 0 < -H := neg_pos.mpr hH
  let ξ : ℂ := ((1 / (-H) : ℝ) : ℂ) * (-η)
  have hprojection (z : ℂ) : (ξ * z).re = -(η * z).re / (-H) := by
    dsimp only [ξ]
    rw [mul_assoc, neg_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.neg_re, one_div, div_eq_mul_inv, mul_comm]
  have he (σ : FourPerm) : 1 ≤ (ξ * matchingProduct a b σ).re := by
    rw [hprojection, le_div_iff₀ ht, one_mul]
    exact neg_le_neg (hmax σ)
  have hd := hexternal ξ he
  rw [hprojection, le_div_iff₀ ht, one_mul] at hd
  exact neg_le_neg_iff.mp hd

private theorem mixedSeedIndex (p : Fin 24) :
    mixedCostRayInt 0 p = mixedCostSeedInt p := by
  change mixedCostSeedInt (fourPermIndex (1 * fourPerm p * 1)) = mixedCostSeedInt p
  rw [one_mul, mul_one, fourPermIndex_fourPerm]

private def elevenContactLiftOfRays18And23 (c d H : ℝ) : Fin 14 → ℝ :=
  ![d + 1, -d, 0, 0, 0, -c - d, d - 1, -1, 0, 1, c, -1, 0, -H]

private def elevenContactLiftOfRays18And27 (c d H : ℝ) : Fin 14 → ℝ :=
  ![1, d, 0, -d, 0, -c, -d - 1, -1, 0, d + 1, c, -d - 1, 0, -H]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem elevenContactLiftOfRays18And23_profile (c d H : ℝ) (p : Fin 24) :
    fourMatchingEvaluation (elevenContactLiftOfRays18And23 c d H) p =
      mixedCostRay 0 p + c * ordinaryCostRay 18 p + d * ordinaryCostRay 23 p - H := by
  fin_cases p <;>
    norm_num [elevenContactLiftOfRays18And23, fourMatchingEvaluation, mixedCostRay,
      mixedSeedIndex, mixedCostSeedInt, ordinaryCostRay, ordinaryCostRayInt,
      fourCostPermutation, fourPerm, FourPerm, Equiv.swap_apply_def,
      Equiv.Perm.mul_apply, fourCostPair, Matrix.cons_val] <;> ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem elevenContactLiftOfRays18And27_profile (c d H : ℝ) (p : Fin 24) :
    fourMatchingEvaluation (elevenContactLiftOfRays18And27 c d H) p =
      mixedCostRay 0 p + c * ordinaryCostRay 18 p + d * ordinaryCostRay 27 p - H := by
  fin_cases p <;>
    norm_num [elevenContactLiftOfRays18And27, fourMatchingEvaluation, mixedCostRay,
      mixedSeedIndex, mixedCostSeedInt, ordinaryCostRay, ordinaryCostRayInt,
      fourCostPermutation, fourPerm, FourPerm, Equiv.swap_apply_def,
      Equiv.Perm.mul_apply, fourCostPair, Matrix.cons_val] <;> ring

private theorem elevenContactLiftOfRays18And23_kernel (c d H : ℝ) (v : Fin 14 → ℝ)
    (hv : (fourMatchingHessian (elevenContactLiftOfRays18And23 c d H)).mulVec v = 0) :
    fourMatchingEvaluation v 12 = fourMatchingEvaluation v 20 := by
  have h₂ := congrFun hv 2
  have h₄ := congrFun hv 4
  have h₇ := congrFun hv 7
  have h₈ := congrFun hv 8
  have h₁₀ := congrFun hv 10
  have h₁₂ := congrFun hv 12
  simp only [fourMatchingHessian_mulVec_apply, Pi.zero_apply, fourMatchingGradient,
    elevenContactLiftOfRays18And23, Matrix.cons_val] at h₂ h₄ h₇ h₈ h₁₀ h₁₂
  simp only [fourMatchingEvaluation, Matrix.cons_val]
  linear_combination -h₂ + h₄ + h₇ - h₈ - h₁₀ + h₁₂

private theorem elevenContactLiftOfRays18And27_kernel (c d H : ℝ) (v : Fin 14 → ℝ)
    (hv : (fourMatchingHessian (elevenContactLiftOfRays18And27 c d H)).mulVec v = 0) :
    fourMatchingEvaluation v 6 = fourMatchingEvaluation v 8 := by
  have h₂ := congrFun hv 2
  have h₁₃ := congrFun hv 13
  simp only [fourMatchingHessian_mulVec_apply, Pi.zero_apply, fourMatchingGradient,
    elevenContactLiftOfRays18And27, Matrix.cons_val] at h₂ h₁₃
  simp only [fourMatchingEvaluation, Matrix.cons_val]
  linear_combination -h₂ + h₁₃

private theorem fourMatchingEvaluation_spectral_imaginary_part
    (a b : Fin 4 → ℂ) (η : ℂ) (p : Fin 24) :
    fourMatchingEvaluation
        (fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).im) p =
      (η * matchingProduct a b (fourPerm p).symm).im := by
  rw [← fourMatchingEvaluation_spectral]
  generalize fourNoncrossingCoordinates (fourSpectralPoints a b) = m
  fin_cases p <;> simp [fourMatchingEvaluation] <;> ring

private theorem spectral_matches_eq_of_hessian_kernel (a b : Fin 4 → ℂ) (η : ℂ)
    (hη : η ≠ 0) (m : Fin 14 → ℝ) (p q : Fin 24)
    (hm : ∀ i, fourMatchingEvaluation m i = (η * matchingProduct a b (fourPerm i).symm).re)
    (hreal : fourMatchingEvaluation m p = fourMatchingEvaluation m q)
    (hkernel : ∀ v : Fin 14 → ℝ, (fourMatchingHessian m).mulVec v = 0 →
      fourMatchingEvaluation v p = fourMatchingEvaluation v q) :
    matchingProduct a b (fourPerm p).symm = matchingProduct a b (fourPerm q).symm := by
  let w : Fin 14 → ℂ := fun j => η * fourNoncrossingCoordinates (fourSpectralPoints a b) j
  have hm' : m = fun j => (w j).re := by
    apply fourMatchingEvaluation_injective
    funext j
    exact (hm j).trans (fourMatchingEvaluation_spectral_real_part a b η j).symm
  have hv : (fourMatchingHessian m).mulVec (fun j => (w j).im) = 0 := by
    funext j
    change (fourMatchingHessian m).mulVec (fun j => (w j).im) j = 0
    rw [hm', fourMatchingHessian_mulVec_im]
    have hgrad : fourMatchingGradient w j = 0 := by
      dsimp only [w]
      rw [fourMatchingGradient_scale, fourMatchingGradient_noncrossing, mul_zero]
    rw [hgrad, Complex.zero_im]
  have him := hkernel _ hv
  dsimp only [w] at him
  simp only [fourMatchingEvaluation_spectral_imaginary_part] at him
  apply mul_left_cancel₀ hη
  exact Complex.ext ((hm p).symm.trans (hreal.trans (hm q))) him

/-- The normalized mixed profile with ordinary rays 18 and 23 forces
matching products 12 and 20 to coincide, at every support height. -/
theorem fourElevenContactRays18And23_impossible
    (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0) (c d H : ℝ)
    (hdistinct : Function.Injective (matchingProduct a b))
    (hgap : ∀ p : Fin 24, H - (η * matchingProduct a b (fourPerm p).symm).re =
      mixedCostRay 0 p + c * ordinaryCostRay 18 p + d * ordinaryCostRay 23 p) :
    False := by
  let m := elevenContactLiftOfRays18And23 c d H
  have he (p : Fin 24) :
      fourMatchingEvaluation m p = ((-η) * matchingProduct a b (fourPerm p).symm).re := by
    dsimp only [m]
    rw [elevenContactLiftOfRays18And23_profile, ← hgap p, neg_mul, Complex.neg_re]
    ring
  have hr : fourMatchingEvaluation m 12 = fourMatchingEvaluation m 20 := by
    simp only [m, elevenContactLiftOfRays18And23, fourMatchingEvaluation, Matrix.cons_val]
    ring
  have heq := spectral_matches_eq_of_hessian_kernel a b (-η) (neg_ne_zero.mpr hη)
    m 12 20 he hr (elevenContactLiftOfRays18And23_kernel c d H)
  have hperm := congrArg Equiv.symm (hdistinct heq)
  exact (by decide : fourPerm 12 ≠ fourPerm 20) (by simpa only [Equiv.symm_symm] using hperm)

/-- The normalized mixed profile with ordinary rays 18 and 27 forces
matching products 6 and 8 to coincide, at every support height. -/
theorem fourElevenContactRays18And27_impossible
    (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0) (c d H : ℝ)
    (hdistinct : Function.Injective (matchingProduct a b))
    (hgap : ∀ p : Fin 24, H - (η * matchingProduct a b (fourPerm p).symm).re =
      mixedCostRay 0 p + c * ordinaryCostRay 18 p + d * ordinaryCostRay 27 p) :
    False := by
  let m := elevenContactLiftOfRays18And27 c d H
  have he (p : Fin 24) :
      fourMatchingEvaluation m p = ((-η) * matchingProduct a b (fourPerm p).symm).re := by
    dsimp only [m]
    rw [elevenContactLiftOfRays18And27_profile, ← hgap p, neg_mul, Complex.neg_re]
    ring
  have hr : fourMatchingEvaluation m 6 = fourMatchingEvaluation m 8 := by
    simp only [m, elevenContactLiftOfRays18And27, fourMatchingEvaluation, Matrix.cons_val]
    ring
  have heq := spectral_matches_eq_of_hessian_kernel a b (-η) (neg_ne_zero.mpr hη)
    m 6 8 he hr (elevenContactLiftOfRays18And27_kernel c d H)
  have hperm := congrArg Equiv.symm (hdistinct heq)
  exact (by decide : fourPerm 6 ≠ fourPerm 8) (by simpa only [Equiv.symm_symm] using hperm)

end

end MOC
