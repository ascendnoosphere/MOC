import MOC.FourContact0710ShiftedQuadratic
import MOC.FourMatchingHessian
import MOC.FourMatchingHessianKernel

/-!
The order-four gap with ordinary rays 0, 7, 10, 18, and 22 and mixed
ray 34. The real matching values equal the gap plus the radial height.
This module derives the signed height equation and uses the actual
gradient equations to exclude the entire fourth-weight-zero boundary.
-/

namespace MOC.FourContact0710

noncomputable section

/-- All matching gaps in lexicographic order, with the mixed weight set
to one and ray 22 divided by two to have primitive nonzero value one. -/
def gap (a b c d e : ℝ) : Fin 24 → ℝ :=
  ![a + c + 1, a, a + e + 1, a + 1, a + b + d + e + 1, a + b + c + d + 2,
    c, 0, e, 0, b + e + 1, b + c + 1, 0, 1, 0, 0, b + 1, b, d, c + d + 1, 0, c + 1, 0, 0]

/-- The signed height is the common value at the zero gaps. -/
def lift (a b c d e height : ℝ) : Fin 14 → ℝ :=
  ![1, e, b, 0, a, -d, -e - 1, -b - c - 1, c, c + 1, d, -c - 1, 0, height]

def cubicValue (a b c e : ℝ) : ℝ := -(c + 1) * (p a b + e)

theorem gap_nonneg {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (i : Fin 24) :
    0 ≤ gap a b c d e i := by
  fin_cases i <;> simp [gap] <;> positivity

theorem lift_evaluation (a b c d e height : ℝ) (i : Fin 24) :
    fourMatchingEvaluation (lift a b c d e height) i = gap a b c d e i + height := by
  fin_cases i <;> simp [fourMatchingEvaluation, lift, gap] <;> ring

theorem lift_cubic (a b c d e height : ℝ) :
    fourMatchingCubic (lift a b c d e height) =
      cubicValue a b c e + height * heightDenominator d e := by
  simp [fourMatchingCubic, lift, cubicValue, p, heightDenominator] <;> ring

theorem lift_radial_gradient (a b c d e height : ℝ) :
    fourMatchingGradient (lift a b c d e height) 13 = heightDenominator d e := by
  simp [fourMatchingGradient, lift, heightDenominator] <;> ring

/-- The normalized gap has these actual spectral projections in the
indicated direction. No rank or simplicity condition is part of this definition. -/
def HasSpectralLift (a b c d e height : ℝ) : Prop :=
  ∃ (α β : Fin 4 → ℂ) (η : ℂ), ∀ i : Fin 24,
    (η * matchingProduct α β (fourPerm i).symm).re = gap a b c d e i + height

theorem lift_eq_spectral_real_coordinates {a b c d e height : ℝ}
    (α β : Fin 4 → ℂ) (η : ℂ)
    (h : ∀ i : Fin 24,
      (η * matchingProduct α β (fourPerm i).symm).re = gap a b c d e i + height) :
    lift a b c d e height =
      fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints α β) j).re := by
  apply fourMatchingEvaluation_injective
  funext i
  rw [lift_evaluation, fourMatchingEvaluation_spectral_real_part, h i]

theorem cubicValue_neg {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) : cubicValue a b c e < 0 := by
  have hc' : 0 < c + 1 := by linarith only [hc]
  have hp : 0 < p a b + e := add_pos_of_pos_of_nonneg (p_pos ha hb) he
  unfold cubicValue
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc') hp

/-- All actual points in the normalized family have nonzero height
and a nonzero denominator in the height equation. -/
theorem height_of_spectralLift {a b c d e height : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hs : HasSpectralLift a b c d e height) :
    heightDenominator d e ≠ 0 ∧ height ≠ 0 ∧
      height = -cubicValue a b c e / heightDenominator d e := by
  obtain ⟨α, β, η, h⟩ := hs
  have hx := lift_eq_spectral_real_coordinates α β η h
  have hf := fourMatchingCubic_of_spectral_real_part α β η
  rw [← hx, lift_cubic] at hf
  have hF := cubicValue_neg ha hb hc he
  have hQ : heightDenominator d e ≠ 0 := by
    intro hz
    rw [hz, mul_zero, add_zero] at hf
    exact (ne_of_lt hF) hf
  have hh : height ≠ 0 := by
    intro hz
    rw [hz, zero_mul, add_zero] at hf
    exact (ne_of_lt hF) hf
  exact ⟨hQ, hh, (eq_div_iff hQ).mpr (by linarith only [hf])⟩

theorem hessian_singular_of_spectralLift {a b c d e height : ℝ}
    (hs : HasSpectralLift a b c d e height) :
    (fourMatchingHessian (lift a b c d e height)).det = 0 := by
  obtain ⟨α, β, η, h⟩ := hs
  rw [lift_eq_spectral_real_coordinates α β η h]
  exact fourMatchingHessian_det_spectral_real_part_eq_zero α β η

/-- The coordinates required of the imaginary part of an actual gap. -/
theorem real_lift_equations_of_spectralLift {a b c d e height : ℝ}
    (hs : HasSpectralLift a b c d e height) :
    ∃ y : Fin 14 → ℝ, fourMatchingHessianAction (lift a b c d e height) y = 0 ∧
      fourMatchingGradient y = fourMatchingGradient (lift a b c d e height) := by
  obtain ⟨α, β, η, h⟩ := hs
  let z := fun j => η * fourNoncrossingCoordinates (fourSpectralPoints α β) j
  have hx : lift a b c d e height = fun j => (z j).re :=
    lift_eq_spectral_real_coordinates α β η h
  have hg : fourMatchingGradient z = 0 := by
    funext i
    change fourMatchingGradient (fun j =>
      η * fourNoncrossingCoordinates (fourSpectralPoints α β) j) i = 0
    rw [fourMatchingGradient_scale, fourMatchingGradient_noncrossing, mul_zero]
  refine ⟨fun j => (z j).im, ?_⟩
  rw [hx]
  exact (fourMatchingGradient_eq_zero_iff z).mp hg

open private cubicGradient from MOC.FourMatchingPolarization

private theorem kernel_row_one_at_zero (a b c e height : ℝ) (y : Fin 14 → ℝ) :
    fourMatchingHessianAction (lift a b c 0 e height) y 1 =
      -(c + 1) * (y 0 + y 10) - (b + c + 1) * y 12 - (c + height + 1) * y 5 - y 9 := by
  simp [fourMatchingHessianAction, cubicGradient, lift] <;> ring

private theorem kernel_row_three_at_zero (a b c e height : ℝ) (y : Fin 14 → ℝ) :
    fourMatchingHessianAction (lift a b c 0 e height) y 3 =
      -(c + 1) * (y 0 + y 10 + y 5) - (b + c + 1) * y 12 - y 9 := by
  simp [fourMatchingHessianAction, cubicGradient, lift] <;> ring

private theorem kernel_radial_row (a b c d e height : ℝ) (y : Fin 14 → ℝ) :
    fourMatchingHessianAction (lift a b c d e height) y 13 =
      d * y 1 - e * y 5 - (e + 1) * y 0 + y 6 := by
  simp [fourMatchingHessianAction, cubicGradient, lift] <;> ring

/-- With zero fourth weight, two Hessian rows force the fifth
imaginary coordinate to vanish. The radial gradient is then nonnegative. -/
theorem radial_gradient_nonneg_of_kernel_at_zero {a b c e height : ℝ}
    (he : 0 ≤ e) (hh : height ≠ 0) (y : Fin 14 → ℝ)
    (hy : fourMatchingHessianAction (lift a b c 0 e height) y = 0) :
    0 ≤ fourMatchingGradient y 13 := by
  have h1 := congrFun hy 1
  have h3 := congrFun hy 3
  have h13 := congrFun hy 13
  change fourMatchingHessianAction (lift a b c 0 e height) y 1 = 0 at h1
  change fourMatchingHessianAction (lift a b c 0 e height) y 3 = 0 at h3
  change fourMatchingHessianAction (lift a b c 0 e height) y 13 = 0 at h13
  rw [kernel_row_one_at_zero] at h1
  rw [kernel_row_three_at_zero] at h3
  rw [kernel_radial_row] at h13
  have hp : height * y 5 = 0 := by linear_combination h3 - h1
  have h5 : y 5 = 0 := (mul_eq_zero.mp hp).resolve_left hh
  simp only [h5, zero_mul, mul_zero, zero_sub] at h13
  have h6 : y 6 = (e + 1) * y 0 := by linarith only [h13]
  simp only [fourMatchingGradient, Matrix.cons_val, h5, h6, mul_zero, sub_zero]
  have he' : 0 ≤ e + 1 := by positivity
  nlinarith only [mul_nonneg he' (sq_nonneg (y 0))]

/-- No actual spectral profile has this normalized five-ray gap when
the weight of ray 18 is zero. All other ordinary weights may vanish. -/
theorem no_spectralLift_at_zero_fourth_weight {a b c e height : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) :
    ¬ HasSpectralLift a b c 0 e height := by
  intro hs
  have hheight := (height_of_spectralLift ha hb hc he hs).2.1
  obtain ⟨y, hy, hg⟩ := real_lift_equations_of_spectralLift hs
  have hpos := radial_gradient_nonneg_of_kernel_at_zero he hheight y hy
  have heq := congrFun hg 13
  rw [lift_radial_gradient] at heq
  norm_num [heightDenominator] at heq
  nlinarith only [he, heq, hpos]

set_option maxHeartbeats 2500000 in
/-- On both rational unequal anchors the radial gradient on the kernel
is the same positive semidefinite binary form. -/
theorem radial_gradient_nonneg_at_unequal_anchor
    (a b : ℝ) (hab : (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0)) (y : Fin 14 → ℝ)
    (hy : fourMatchingHessianAction (lift a b 0 1 10 (-15)) y = 0) :
    0 ≤ fourMatchingGradient y 13 := by
  have hrows (j : Fin 14) : fourMatchingHessianAction (lift a b 0 1 10 (-15)) y j = 0 :=
    congrFun hy j
  have h0 := hrows 0
  have h1 := hrows 1
  have h2 := hrows 2
  have h3 := hrows 3
  have h4 := hrows 4
  have h5 := hrows 5
  have h6 := hrows 6
  have h7 := hrows 7
  have h8 := hrows 8
  have h9 := hrows 9
  have h10 := hrows 10
  have h11 := hrows 11
  have hkernel : y 5 = -y 0 - y 1 / 55 ∧ y 6 = y 0 - 13 * y 1 / 11 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      simp only [fourMatchingHessianAction, cubicGradient, lift, Matrix.cons_val,
        Matrix.cons_val_succ', Matrix.cons_val_zero'] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      constructor <;> linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  obtain ⟨hfifth, hsixth⟩ := hkernel
  change 0 ≤ y 0 * y 6 - y 1 * y 5
  rw [hfifth, hsixth]
  nlinarith only [sq_nonneg (y 0 - y 1 / 11), sq_nonneg (y 1)]

/-- The two rational anchors of the unequal continuation are exact
obstructions to real spectral realization. -/
theorem no_spectralLift_at_unequal_anchor
    (a b : ℝ) (hab : (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0)) :
    ¬ HasSpectralLift a b 0 1 10 (-15) := by
  intro hs
  obtain ⟨y, hy, hg⟩ := real_lift_equations_of_spectralLift hs
  have hpos := radial_gradient_nonneg_at_unequal_anchor a b hab y hy
  have heq := congrFun hg 13
  rw [lift_radial_gradient] at heq
  norm_num [heightDenominator] at heq
  linarith only [heq, hpos]

set_option maxHeartbeats 2500000 in
/-- The rational anchor on the equal-weight branch is excluded by a
rank-one square for the imaginary radial gradient. -/
theorem no_spectralLift_at_equal_anchor : ¬ HasSpectralLift 2 2 1 1 9 (-36) := by
  intro hs
  obtain ⟨y, hy, hg⟩ := real_lift_equations_of_spectralLift hs
  have hrows (j : Fin 14) : fourMatchingHessianAction (lift 2 2 1 1 9 (-36)) y j = 0 :=
    congrFun hy j
  have h0 := hrows 0
  have h1 := hrows 1
  have h2 := hrows 2
  have h3 := hrows 3
  have h4 := hrows 4
  have h5 := hrows 5
  have h6 := hrows 6
  have h7 := hrows 7
  have h8 := hrows 8
  have h9 := hrows 9
  have h10 := hrows 10
  have h11 := hrows 11
  simp only [fourMatchingHessianAction, cubicGradient, lift, Matrix.cons_val,
    Matrix.cons_val_succ', Matrix.cons_val_zero'] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have hfirst : y 1 = 31 * y 0 / 3 := by
    linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have hfifth : y 5 = -11 * y 0 / 9 := by
    linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have hsixth : y 6 = -34 * y 0 / 3 := by
    linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have heq := congrFun hg 13
  rw [lift_radial_gradient] at heq
  change y 0 * y 6 - y 1 * y 5 = heightDenominator 1 9 at heq
  rw [hfirst, hfifth, hsixth] at heq
  norm_num [heightDenominator] at heq
  nlinarith only [heq, sq_nonneg (y 0)]

end

end MOC.FourContact0710
