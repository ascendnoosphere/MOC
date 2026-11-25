import MOC.FourContact0710SpectralLift

/-! The scalar factors of the order-four five-ray contact pencil.
The positivity of the predicted quadratic coefficient on the unequal
branch follows directly from the two factor slopes. -/

namespace MOC.FourContact0710

noncomputable section

def linearConstant (a b c d e : ℝ) : ℝ :=
  d * p a b * (c + 1) * (p a b * (c + 1) + e * (c + 1 - a * b))

def linearSlope (a b c d e : ℝ) : ℝ :=
  p a b * (c + 1) * ((c + 1) * q a b d + d) +
    e * (rootPolynomial a b d c - d * p a b * (c + 1 - a * b) * (d - 1))

def linearFactor (a b c d e t : ℝ) : ℝ :=
  linearConstant a b c d e + t * linearSlope a b c d e

def couplingParameter (a b d : ℝ) : ℝ := d * (a + b + 1) + a * b

def quadraticConstant (a b c d e : ℝ) : ℝ := d * e ^ 2 * a * b * (c + 1)

def quadraticLinear (a b c d e : ℝ) : ℝ :=
  e * ((c + 1) * d * (d * p a b + p a b + 2 * a * b) +
    e * ((c + 1) * couplingParameter a b d + a * b * d * (1 - d)))

def quadraticLeading (a b c d e : ℝ) : ℝ :=
  heightDenominator d e * ((c + 1) * q a b d - e * couplingParameter a b d)

def quadraticFactor (a b c d e t : ℝ) : ℝ :=
  quadraticConstant a b c d e + quadraticLinear a b c d e * t +
    quadraticLeading a b c d e * t ^ 2

def quadraticSlope (a b c d e t : ℝ) : ℝ :=
  quadraticLinear a b c d e + 2 * quadraticLeading a b c d e * t

theorem linearFactor_at_height {a b c d e : ℝ} (hQ : heightDenominator d e ≠ 0) :
    linearFactor a b c d e (-cubicValue a b c e / heightDenominator d e) =
      (c + 1) * branchPolynomial a b c d e / heightDenominator d e := by
  unfold linearFactor linearConstant linearSlope cubicValue branchPolynomial
  field_simp [hQ]
  unfold heightDenominator rootPolynomial linearParameter constantParameter q p
  ring

theorem quadraticFactor_at_height {a b c d e : ℝ} (hQ : heightDenominator d e ≠ 0) :
    quadraticFactor a b c d e (-cubicValue a b c e / heightDenominator d e) =
      (c + 1) * branchPolynomial a b c d e / heightDenominator d e := by
  unfold quadraticFactor quadraticConstant quadraticLinear quadraticLeading
    cubicValue branchPolynomial
  field_simp [hQ]
  unfold heightDenominator couplingParameter rootPolynomial linearParameter constantParameter q p
  ring

/-- At a scalar branch root with unequal first weights, the intercept
of the linear factor is strictly positive. -/
theorem linearConstant_pos_of_unequal_branch {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 < e)
    (hne : a ≠ b) (hP : branchPolynomial a b c d e = 0) :
    0 < linearConstant a b c d e := by
  let w := c + p a b * (c + 1) / e
  have hp := p_pos ha hb
  have hq := q_pos ha hb hd.le
  have hcw : c < w := lt_add_of_pos_right _ (div_pos (mul_pos hp (by positivity)) he)
  have hw := hc.trans_lt hcw
  have hA : rootPolynomial a b d w = 0 := by
    rw [branchPolynomial_shift he.ne'] at hP
    exact (mul_eq_zero.mp hP).resolve_left (pow_ne_zero 2 he.ne')
  have hS := constantParameter_pos_of_rootPolynomial_nonpos ha hb hd hne hw hA.le
  have hlt : a * b - 1 < w := by
    by_cases hab : a * b ≤ 1
    · exact (sub_nonpos.mpr hab).trans_lt hw
    · have hprod : 0 < a * b := zero_lt_one.trans (lt_of_not_ge hab)
      have hneg : rootPolynomial a b d (a * b - 1) < 0 := by
        rw [rootPolynomial_at_product_sub_one]
        have hsq := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
        have hpos := mul_pos (mul_pos hprod hd) hsq
        linarith only [hpos]
      have htest := (rootPolynomial_neg_iff_lt_positiveRoot hp hq hS
        (sub_pos.mpr (lt_of_not_ge hab))).mp hneg
      rwa [← positive_root_eq hp hq hS hw hA] at htest
  have hid : p a b * (c + 1) + e * (c + 1 - a * b) =
      e * (w - (a * b - 1)) := by
    dsimp only [w]
    field_simp [he.ne']
    ring
  unfold linearConstant
  rw [hid]
  have hpos := sub_pos.mpr hlt
  positivity

/-- The first coefficient of the quadratic factor exceeds twice a
nonnegative part coming from the radial denominator. -/
theorem quadraticLinear_gt_negative_denominator {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 < e) :
    2 * e * (-heightDenominator d e * d * a * b) < quadraticLinear a b c d e := by
  have hp := p_pos ha hb
  have hsq : 0 < 1 - d + d ^ 2 := by nlinarith only [sq_nonneg (d - 1 / 2)]
  have hcd : 0 ≤ c + 1 - d + d ^ 2 := by linarith only [hc, hsq]
  have hbranch :
      quadraticLinear a b c d e - 2 * e * (-heightDenominator d e * d * a * b) =
        e * (e * ((c + 1) * d * (a + b + 1) + a * b * (c + 1 - d + d ^ 2)) +
          d * ((c + 1) * (d * p a b + p a b) + 2 * c * a * b)) := by
    unfold quadraticLinear heightDenominator couplingParameter
    ring
  have hfirst :
      0 ≤ e * ((c + 1) * d * (a + b + 1) + a * b * (c + 1 - d + d ^ 2)) := by
    positivity
  have hsecond : 0 < d * ((c + 1) * (d * p a b + p a b) + 2 * c * a * b) := by
    positivity
  have hpos := mul_pos he (add_pos_of_nonneg_of_pos hfirst hsecond)
  rw [← hbranch] at hpos
  exact sub_pos.mp hpos

/-- On the unequal positive-height branch the two scalar factors
have opposite nonzero slopes. Here the signed contact height is negative.
The proof uses no sign continuation or discriminant coefficient table. -/
theorem slopes_of_unequal_branch {a b c d e t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 < e)
    (hne : a ≠ b) (hP : branchPolynomial a b c d e = 0) (hQ : heightDenominator d e < 0)
    (ht : t = -cubicValue a b c e / heightDenominator d e) :
    0 < linearSlope a b c d e ∧ quadraticSlope a b c d e t < 0 := by
  have hp := p_pos ha hb
  have hF := cubicValue_neg ha hb hc he.le
  have htneg : t < 0 := by
    rw [ht]
    exact div_neg_of_pos_of_neg (neg_pos.mpr hF) hQ
  have hL : linearFactor a b c d e t = 0 := by
    rw [ht, linearFactor_at_height hQ.ne, hP, mul_zero, zero_div]
  have hR : quadraticFactor a b c d e t = 0 := by
    rw [ht, quadraticFactor_at_height hQ.ne, hP, mul_zero, zero_div]
  have hC := linearConstant_pos_of_unequal_branch ha hb hc hd he hne hP
  have hLin : 0 < linearSlope a b c d e := by
    have hprod : 0 < (-t) * linearSlope a b c d e := by
      unfold linearFactor at hL
      nlinarith only [hC, hL]
    exact (mul_pos_iff_of_pos_left (neg_pos.mpr htneg)).mp hprod
  refine ⟨hLin, ?_⟩
  have htQ : (-t) * (-heightDenominator d e) = (c + 1) * (p a b + e) := by
    rw [ht]
    unfold cubicValue
    field_simp [hQ.ne]
    ring
  have hlow := mul_lt_mul_of_pos_right
    (quadraticLinear_gt_negative_denominator ha hb hc hd he) (neg_pos.mpr htneg)
  have hfirst :
      2 * e * (-heightDenominator d e * d * a * b) * (-t) =
        2 * e * d * a * b * (c + 1) * (p a b + e) := by
    linear_combination (2 * e * d * a * b) * htQ
  have hsecond :
      2 * quadraticConstant a b c d e ≤ 2 * e * d * a * b * (c + 1) * (p a b + e) := by
    unfold quadraticConstant
    have hmul := mul_le_mul_of_nonneg_left
      (show e ≤ p a b + e by linarith only [hp])
      (show 0 ≤ 2 * e * d * a * b * (c + 1) by positivity)
    nlinarith only [hmul]
  have hprod : 2 * quadraticConstant a b c d e < quadraticLinear a b c d e * (-t) :=
    hsecond.trans_lt (hfirst ▸ hlow)
  have hdiff : 0 < t * quadraticSlope a b c d e t := by
    unfold quadraticFactor at hR
    unfold quadraticSlope
    nlinarith only [hR, hprod]
  exact (mul_pos_iff.mp hdiff).elim (fun h => (not_lt_of_ge htneg.le h.1).elim) And.right

/-- The scalar product of the two factors has a strictly positive
quadratic term at the candidate height. The formula here is for the
factor polynomial; identifying it with the matrix pencil is separate. -/
theorem positive_quadratic_term_of_unequal_factor_product {a b c d e t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 < e)
    (hne : a ≠ b) (hP : branchPolynomial a b c d e = 0) (hQ : heightDenominator d e < 0)
    (ht : t = -cubicValue a b c e / heightDenominator d e) :
    let u := -4 * linearSlope a b c d e * quadraticSlope a b c d e t
    0 < u ∧ ∀ z : ℝ,
      -4 * linearFactor a b c d e (t + z) * quadraticFactor a b c d e (t + z) =
        u * z ^ 2 + (-4 * linearSlope a b c d e * quadraticLeading a b c d e) * z ^ 3 := by
  obtain ⟨hLs, hRs⟩ := slopes_of_unequal_branch ha hb hc hd he hne hP hQ ht
  have hL : linearFactor a b c d e t = 0 := by
    rw [ht, linearFactor_at_height hQ.ne, hP, mul_zero, zero_div]
  have hR : quadraticFactor a b c d e t = 0 := by
    rw [ht, quadraticFactor_at_height hQ.ne, hP, mul_zero, zero_div]
  refine ⟨mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by norm_num) hLs) hRs, fun z => ?_⟩
  have hLz : linearFactor a b c d e (t + z) = linearSlope a b c d e * z := by
    unfold linearFactor at *
    linear_combination hL
  have hRz : quadraticFactor a b c d e (t + z) =
      quadraticSlope a b c d e t * z + quadraticLeading a b c d e * z ^ 2 := by
    unfold quadraticFactor at *
    unfold quadraticSlope
    linear_combination hR
  rw [hLz, hRz]
  ring

end

end MOC.FourContact0710
