import MOC.FourContact0710HessianPencil

/-! On the equal-weight branch, a single linear combination of the Hessian
rows gives the sign of the radial gradient on its kernel. -/

open BigOperators
open private cubicGradient from MOC.FourMatchingPolarization

namespace MOC.FourContact0710

noncomputable section

private def equalBranchLinear (a c e : ℝ) : ℝ :=
  (a + 1) ^ 2 * (c + 1) + e * (c + 1 - a ^ 2)

private def equalBranchPositive (a c d e : ℝ) : ℝ :=
  a ^ 4 * (c + 1) + 2 * a ^ 3 * (c + 1) * (d + 2) +
    a ^ 2 * (5 * c * d + c * e + 6 * c + e * (d ^ 2 - d + 1) + 5 * d + 6) +
    2 * a * (c * d * e + 2 * c * d + c * e + 2 * c + d ^ 2 * e + 2 * d + e + 2) +
    c * d * e + c * d + c * e + c + d ^ 2 * e + d * e + d + e + 1

private theorem branchPolynomial_at_equal_weights (a c d e : ℝ) :
    branchPolynomial a a c d e = equalBranchLinear a c e * equalBranchPositive a c d e := by
  unfold branchPolynomial equalBranchLinear equalBranchPositive rootPolynomial
    linearParameter constantParameter q p
  ring

private theorem equalBranchPositive_pos {a c d e : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 < equalBranchPositive a c d e := by
  have hdq : 0 ≤ d ^ 2 - d + 1 := by nlinarith only [sq_nonneg (d - 1 / 2)]
  unfold equalBranchPositive
  positivity

private def radialEvenZero (y : Fin 14 → ℝ) : ℝ := (y 0 - y 1 - y 6) / 2

private def radialEvenFive (y : Fin 14 → ℝ) : ℝ := (y 0 + y 1 + 2 * y 5 + y 6) / 2

private def radialEvenSix (y : Fin 14 → ℝ) : ℝ := (y 6 - y 0 - y 1) / 2

private def radialOddZero (y : Fin 14 → ℝ) : ℝ := (y 0 + y 1 + y 6) / 2

/-- Row coefficients for the radial relation after imposing the equal branch. -/
private def equalKernelCertificate (a d e : ℝ) : Fin 14 → ℝ :=
  let Q := heightDenominator d e
  let k₂ := Q * (2 * a ^ 2 * d + a ^ 2 * e + 2 * a * d ^ 2 +
    2 * a * d * e + 2 * a * d + d ^ 2 + d * e + d)
  let k₃ := -(a ^ 2 * e * Q)
  let k₅ := d * e * (a + 1) * Q
  let k₆ := -(d * Q * (2 * a ^ 2 + 2 * a * d + a * e + 2 * a + d + e + 1))
  let k₇ := -(d * e * Q)
  let k₈ := d * e * (a + 1) * Q
  let k₉ := -(a * d * e * (a - Q))
  ![-k₂ - k₅ - k₆, k₂ - k₃ + k₅ + k₆, 0,
    -k₂ - k₆ + k₇ + k₈, 0, k₂, k₃, 0, k₅, -k₇ - k₈, k₆, k₇, k₈, k₉]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 10000000 in
private theorem equalKernelCertificate_identity (a d e : ℝ) (y : Fin 14 → ℝ)
    (hv : (a + 1) ^ 2 + e ≠ 0) (hQ : heightDenominator d e ≠ 0) :
    (∑ i, equalKernelCertificate a d e i *
      fourMatchingHessianAction
        (lift a a (a ^ 2 * e / ((a + 1) ^ 2 + e) - 1) d e
          (e * a ^ 2 / heightDenominator d e)) y i) =
      (2 * a ^ 2 * e * (a + d)) *
        (d * e * radialEvenZero y - d * (a + 1) * y 1 - a * e * radialEvenFive y) := by
  norm_num [equalKernelCertificate, fourMatchingHessianAction, cubicGradient, lift,
    Matrix.cons_val, Fin.sum_univ_succ, radialEvenZero, radialEvenFive] <;>
    field_simp [hv, hQ] <;> unfold heightDenominator <;> ring

private theorem radialGradient_nonneg_of_equalKernel {a c d e t : ℝ}
    (ha : 0 < a) (hd : 0 < d) (he : 0 < e) (hQ : heightDenominator d e < 0)
    (hJ : equalBranchLinear a c e = 0)
    (ht : t = -cubicValue a a c e / heightDenominator d e)
    (y : Fin 14 → ℝ) (hy : fourMatchingHessianAction (lift a a c d e t) y = 0) :
    0 ≤ fourMatchingGradient y 13 := by
  have hv : 0 < (a + 1) ^ 2 + e := by positivity
  have hc' : c = a ^ 2 * e / ((a + 1) ^ 2 + e) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    apply (eq_div_iff hv.ne').mpr
    unfold equalBranchLinear at hJ
    linear_combination hJ
  have ht' : t = e * a ^ 2 / heightDenominator d e := by
    have hnum : -cubicValue a a c e = e * a ^ 2 := by
      unfold cubicValue p
      unfold equalBranchLinear at hJ
      linear_combination hJ
    rw [ht, hnum]
  have hcert := equalKernelCertificate_identity a d e y hv.ne' hQ.ne
  rw [← hc', ← ht', hy] at hcert
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hcert
  have hscale : 2 * a ^ 2 * e * (a + d) ≠ 0 := ne_of_gt (by positivity)
  have hrelation :=
    (mul_eq_zero.mp hcert.symm).resolve_left hscale
  let x := radialEvenZero y
  let z := radialEvenFive y
  let w := radialEvenSix y
  let u := radialOddZero y
  change d * e * x - d * (a + 1) * y 1 - a * e * z = 0 at hrelation
  have hrow : d * y 1 - e * y 5 - (e + 1) * y 0 + y 6 = 0 := by
    have h := congrFun hy 13
    norm_num [fourMatchingHessianAction, cubicGradient, lift, Matrix.cons_val] at h
    linear_combination h
  have hwr : w = e * z + (e + 1) * x - d * y 1 := by
    dsimp only [x, z, w, radialEvenZero, radialEvenFive, radialEvenSix]
    linear_combination hrow
  have hsign : 0 ≤ (e * x - y 1) * (z + d * x) := by
    have hpair : d * (a + 1) * ((e * x - y 1) * (z + d * x)) =
        a * e * (z + d * x) ^ 2 := by
      linear_combination (z + d * x) * hrelation
    have hfactor : 0 < d * (a + 1) := by positivity
    apply nonneg_of_mul_nonneg_left _ hfactor
    rw [hpair]
    positivity
  have hdecomp : fourMatchingGradient y 13 = x * w - y 1 * z + u ^ 2 := by
    simp only [fourMatchingGradient, Matrix.cons_val, x, z, w, u,
      radialEvenZero, radialEvenFive, radialEvenSix, radialOddZero]
    ring
  have hrest : 0 ≤ (-heightDenominator d e) * x ^ 2 + u ^ 2 := by positivity
  rw [hdecomp, hwr]
  unfold heightDenominator at hrest
  nlinarith only [hsign, hrest]

/-- The equal-weight normalized family has no actual spectral lift at
a negative signed height. Zero fourth weight is included. -/
theorem no_equal_spectralLift_of_negative_height {a c d e t : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (htneg : t < 0) :
    ¬ HasSpectralLift a a c d e t := by
  intro hs
  rcases hd.eq_or_lt with rfl | hdp
  · exact no_spectralLift_at_zero_fourth_weight ha ha hc he hs
  have hP := branchPolynomial_zero_of_spectralLift ha ha hc hdp he hs
  rw [branchPolynomial_at_equal_weights] at hP
  have hJ := (mul_eq_zero.mp hP).resolve_right
    (equalBranchPositive_pos ha hc hdp.le he).ne'
  have hnum : 0 < (a + 1) ^ 2 * (c + 1) := by positivity
  have hdelta : e * (a ^ 2 - (c + 1)) = (a + 1) ^ 2 * (c + 1) := by
    unfold equalBranchLinear at hJ
    linear_combination -hJ
  have hep : 0 < e := by
    rcases he.eq_or_lt with rfl | hp
    · rw [zero_mul] at hdelta
      exact (hnum.ne' hdelta.symm).elim
    · exact hp
  have hadd : 0 < a ^ 2 - (c + 1) := by
    apply (mul_pos_iff_of_pos_left hep).mp
    rwa [hdelta]
  have hap : 0 < a := by
    rcases ha.eq_or_lt with rfl | hp
    · norm_num at hadd
      linarith only [hc, hadd]
    · exact hp
  obtain ⟨hQ, _, ht⟩ := height_of_spectralLift ha ha hc he hs
  have hQneg : heightDenominator d e < 0 := by
    have hz := (eq_div_iff hQ).mp ht
    have hF := cubicValue_neg ha ha hc he
    exact (mul_pos_iff.mp (show 0 < t * heightDenominator d e by rw [hz]; exact neg_pos.mpr hF)).elim
      (fun h => (not_lt_of_ge htneg.le h.1).elim) And.right
  obtain ⟨y, hy, hg⟩ := real_lift_equations_of_spectralLift hs
  have hpos := radialGradient_nonneg_of_equalKernel hap hdp hep hQneg hJ ht y hy
  have hradial := congrFun hg 13
  rw [lift_radial_gradient] at hradial
  exact (not_lt_of_ge (hradial ▸ hpos)) hQneg

end

end MOC.FourContact0710
