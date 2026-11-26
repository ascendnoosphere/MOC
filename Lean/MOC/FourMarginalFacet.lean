import MOC.FourMatchingHessian
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp

/-! The order-four obstruction facet and its cubic and Hessian certificates. -/

open BigOperators Matrix Finset

namespace MOC

/-- The order-four facet in the row-to-column permutation convention. -/
def fourMarginalFacet (p : Equiv.Perm (Fin 4)) : ℤ :=
  (if p 0 = 0 then 1 else 0) + (if p 3 = 2 then 1 else 0) -
    (if ({0, 1} : Finset (Fin 4)).map p.toEmbedding = {0, 3} then 1 else 0) +
    (if ({0, 2} : Finset (Fin 4)).map p.toEmbedding = {2, 3} then 1 else 0)

/-- The facet normal, with a free translation of its constant coordinate. -/
def fourMarginalFacetLift {R : Type*} [CommRing R] (t : R) : Fin 14 → R :=
  ![0, 1, 0, -1, 1, 1, -1, 0, -1, 1, -1, 0, 0, t]

theorem fourMarginalFacet_profile (i : Fin 24) :
    fourMatchingEvaluation (fourMarginalFacetLift (0 : ℤ)) i = fourMarginalFacet (fourPerm i) := by
  have h : ∀ j : Fin 24,
      fourMatchingEvaluation (fourMarginalFacetLift (0 : ℤ)) j = fourMarginalFacet (fourPerm j) := by
    decide +kernel
  exact h i

theorem fourMarginalFacet_nonneg (i : Fin 24) : 0 ≤ fourMarginalFacet (fourPerm i) := by
  have h : ∀ j : Fin 24, 0 ≤ fourMarginalFacet (fourPerm j) := by decide +kernel
  exact h i

/-- The evaluations at the thirteen zero permutations leave exactly one
real direction in the fourteen-coordinate matching space. -/
theorem fourMarginalFacet_zero_span (m : Fin 14 → ℝ)
    (hm : ∀ i : Fin 24, fourMarginalFacet (fourPerm i) = 0 → fourMatchingEvaluation m i = 0) :
    m = fun k => m 1 * fourMarginalFacetLift 0 k := by
  have h05 := hm 5 (by decide +kernel)
  have h06 := hm 6 (by decide +kernel)
  have h08 := hm 8 (by decide +kernel)
  have h09 := hm 9 (by decide +kernel)
  have h11 := hm 11 (by decide +kernel)
  have h12 := hm 12 (by decide +kernel)
  have h14 := hm 14 (by decide +kernel)
  have h16 := hm 16 (by decide +kernel)
  have h17 := hm 17 (by decide +kernel)
  have h18 := hm 18 (by decide +kernel)
  have h19 := hm 19 (by decide +kernel)
  have h22 := hm 22 (by decide +kernel)
  have h23 := hm 23 (by decide +kernel)
  norm_num [fourMatchingEvaluation] at h05 h06 h08 h09 h11 h12 h14 h16 h17 h18 h19 h22 h23
  funext k
  fin_cases k <;> norm_num [fourMarginalFacetLift] <;>
    linarith only [h05, h06, h08, h09, h11, h12, h14, h16, h17, h18, h19, h22, h23]

theorem fourMarginalFacet_cubic (t : ℝ) :
    fourMatchingCubic (fourMarginalFacetLift t) = -1 - t := by
  norm_num [fourMatchingCubic, fourMarginalFacetLift] <;> ring

private def twiceFacetHessianInverse : Matrix (Fin 14) (Fin 14) ℤ :=
  !![0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0;
    0, -1, -1, 1, 0, 1, 1, 0, 0, 0, -1, 0, 1, -1;
    0, -1, 0, 1, -1, 1, 1, 0, -1, -1, 1, 2, -2, 1;
    0, 1, 1, -1, 0, -1, -1, 0, 0, 0, 1, 0, 1, -1;
    0, 0, -1, 0, 1, 0, 2, 0, 1, -1, 0, 0, -1, 2;
    0, 1, 1, -1, 0, -1, 1, 0, 0, 0, 1, 0, -1, -1;
    -2, 1, 1, -1, 2, 1, -1, 0, 0, 0, -1, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0;
    0, 0, -1, 0, 1, 0, 0, 0, 1, 1, 0, 0, -1, 0;
    0, 0, -1, 0, -1, 0, 0, 0, 1, 1, 0, 0, -1, 0;
    0, -1, 1, 1, 0, 1, -1, 0, 0, 0, -1, 0, 1, -1;
    0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0;
    0, 1, -2, 1, -1, -1, 1, 2, -1, -1, 1, 0, 0, 1;
    0, -1, 1, -1, 2, -1, 1, 0, 0, 0, -1, 0, 1, -1]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 5000 in
private theorem facetHessian_integer_certificate :
    fourMatchingHessian (fourMarginalFacetLift (-1 : ℤ)) * twiceFacetHessianInverse = (2 : ℤ) • 1 := by
  have h : ∀ i j : Fin 14,
      (fourMatchingHessian (fourMarginalFacetLift (-1 : ℤ)) * twiceFacetHessianInverse) i j =
        ((2 : ℤ) • (1 : Matrix (Fin 14) (Fin 14) ℤ)) i j := by
    decide +kernel
  exact Matrix.ext h

private theorem facetHessian_integer_det_ne_zero :
    (fourMatchingHessian (fourMarginalFacetLift (-1 : ℤ))).det ≠ 0 := by
  intro h
  have he := congrArg Matrix.det facetHessian_integer_certificate
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, mul_one] at he
  norm_num at he

private theorem matchingHessian_map_int (m : Fin 14 → ℤ) :
    (fourMatchingHessian m).map (Int.castRingHom ℝ) =
      fourMatchingHessian (fun j => (m j : ℝ)) := by
  let f := Int.castRingHom ℝ
  apply Matrix.ext
  intro i j
  let v := Pi.single j (1 : ℤ)
  have hv : (fun k => f (v k)) = Pi.single j (1 : ℝ) := by
    funext k
    by_cases h : k = j <;> simp [v, Pi.single_apply, h]
  have h₁ := fourMatchingHessian_mulVec_apply m v i
  have h₂ := fourMatchingHessian_mulVec_apply (fun k => f (m k)) (Pi.single j (1 : ℝ)) i
  simp only [v, Matrix.mulVec_single_one, Matrix.transpose_apply] at h₁ h₂
  change f (fourMatchingHessian m i j) = fourMatchingHessian (fun k => f (m k)) i j
  rw [h₁, h₂]
  simp only [map_sub, fourMatchingGradient_map, map_add]
  rw [show (fun k => f ((Pi.single j (1 : ℤ)) k)) = _ from hv]

/-- At the only translated lift on the cubic, the matching Hessian is nonsingular. -/
theorem fourMarginalFacet_hessian_ne_zero :
    (fourMatchingHessian (fourMarginalFacetLift (-1 : ℝ))).det ≠ 0 := by
  let f := Int.castRingHom ℝ
  let m := fourMarginalFacetLift (-1 : ℤ)
  have hcast : (fun j => f (m j)) = fourMarginalFacetLift (-1 : ℝ) := by
    funext j
    fin_cases j <;> norm_num [m, f, fourMarginalFacetLift]
  rw [← hcast, ← matchingHessian_map_int, ← RingHom.map_det f]
  exact_mod_cast facetHessian_integer_det_ne_zero

/-- This facet is separated from every actual projected spectral profile,
even after allowing an arbitrary additive constant. -/
theorem fourMarginalFacet_no_spectral_translation (t : ℝ) (a b : Fin 4 → ℂ) (η : ℂ) :
    ¬ ∀ i, fourMatchingEvaluation (fourMarginalFacetLift t) i =
      (η * matchingProduct a b (fourPerm i).symm).re := by
  intro h
  have hc := fourMatchingCubic_zero_of_evaluation_eq_spectral a b η _ h
  rw [fourMarginalFacet_cubic] at hc
  have ht : t = -1 := by linarith
  have he : fourMarginalFacetLift t =
      fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re := by
    apply fourMatchingEvaluation_injective
    funext i
    rw [h, fourMatchingEvaluation_spectral_real_part]
  rw [ht] at he
  apply fourMarginalFacet_hessian_ne_zero
  rw [he]
  exact fourMatchingHessian_det_spectral_real_part_eq_zero a b η

noncomputable section

/-- Remove the coordinate of the constant matching function. -/
def centeredMatchingLift (m : Fin 14 → ℝ) : Fin 14 → ℝ :=
  fun j => if j = 13 then 0 else m j

private def constantSlope (m : Fin 14 → ℝ) : ℝ := m 0 * m 6 - m 1 * m 5

private theorem cubic_split_constant (m : Fin 14 → ℝ) :
    fourMatchingCubic m = fourMatchingCubic (centeredMatchingLift m) + m 13 * constantSlope m := by
  norm_num [fourMatchingCubic, centeredMatchingLift, constantSlope] <;> ring

private def clearedSpectralLift (m : Fin 14 → ℝ) : Fin 14 → ℝ :=
  fun j => if j = 13 then -fourMatchingCubic (centeredMatchingLift m) else constantSlope m * m j

private theorem clearedSpectralLift_center (m : Fin 14 → ℝ) :
    clearedSpectralLift (centeredMatchingLift m) = clearedSpectralLift m := by
  have h : centeredMatchingLift (centeredMatchingLift m) = centeredMatchingLift m := by
    funext j
    by_cases hj : j = 13 <;> simp [centeredMatchingLift, hj]
  funext j
  by_cases hj : j = 13 <;> simp [clearedSpectralLift, hj, h, constantSlope, centeredMatchingLift]

private theorem clearedSpectralLift_eq_scale (m : Fin 14 → ℝ) (h : fourMatchingCubic m = 0) :
    clearedSpectralLift m = fun j => constantSlope m * m j := by
  funext j
  by_cases hj : j = 13
  · subst j
    rw [clearedSpectralLift, if_pos rfl]
    have he := cubic_split_constant m
    rw [h] at he
    nlinarith only [he]
  · simp [clearedSpectralLift, hj]

private theorem continuous_matchingHessian :
    Continuous (fourMatchingHessian : (Fin 14 → ℝ) → Matrix (Fin 14) (Fin 14) ℝ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have he (m : Fin 14 → ℝ) : fourMatchingHessian m i j =
      fourMatchingGradient (fun k => m k + Pi.single j (1 : ℝ) k) i -
        fourMatchingGradient m i - fourMatchingGradient (Pi.single j (1 : ℝ)) i := by
    simpa only [Matrix.mulVec_single_one, Matrix.transpose_apply] using
      fourMatchingHessian_mulVec_apply m (Pi.single j (1 : ℝ)) i
  simp_rw [he]
  fin_cases i <;> simp only [fourMatchingGradient, Matrix.cons_val] <;> fun_prop

/-- A polynomial obstruction on centered matching profiles. It is obtained
by eliminating the free constant coordinate from the cubic and Hessian tests. -/
def centeredSpectralObstruction (m : Fin 14 → ℝ) : ℝ :=
  (fourMatchingHessian (clearedSpectralLift m)).det

theorem isClosed_centeredSpectralObstruction_zero :
    IsClosed {m : Fin 14 → ℝ | centeredSpectralObstruction m = 0} := by
  apply isClosed_eq _ continuous_const
  unfold centeredSpectralObstruction
  apply Continuous.matrix_det
  apply continuous_matchingHessian.comp
  unfold clearedSpectralLift
  refine continuous_pi fun j => ?_
  by_cases hj : j = 13 <;>
    simp only [hj, if_true, if_false, fourMatchingCubic, centeredMatchingLift, constantSlope] <;>
    norm_num <;> fun_prop

theorem centeredSpectralObstruction_of_spectral (a b : Fin 4 → ℂ) (η : ℂ) :
    centeredSpectralObstruction (centeredMatchingLift
      (fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re)) = 0 := by
  let m (j : Fin 14) := (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re
  change (fourMatchingHessian (clearedSpectralLift (centeredMatchingLift m))).det = 0
  rw [clearedSpectralLift_center, clearedSpectralLift_eq_scale m
    (fourMatchingCubic_of_spectral_real_part a b η), fourMatchingHessian_scale,
    Matrix.det_smul, fourMatchingHessian_det_spectral_real_part_eq_zero a b η, mul_zero]

theorem fourMarginalFacet_centeredSpectralObstruction_ne_zero :
    centeredSpectralObstruction (fourMarginalFacetLift (0 : ℝ)) ≠ 0 := by
  have he : clearedSpectralLift (fourMarginalFacetLift (0 : ℝ)) =
      fun j => (-1 : ℝ) * fourMarginalFacetLift (-1) j := by
    have hcenter : centeredMatchingLift (fourMarginalFacetLift (0 : ℝ)) = fourMarginalFacetLift 0 := by
      funext j
      fin_cases j <;> norm_num [centeredMatchingLift, fourMarginalFacetLift]
    funext j
    simp only [clearedSpectralLift, hcenter, fourMarginalFacet_cubic]
    fin_cases j <;> norm_num [constantSlope, fourMarginalFacetLift]
  rw [centeredSpectralObstruction, he, fourMatchingHessian_scale, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) fourMarginalFacet_hessian_ne_zero

end

end MOC
