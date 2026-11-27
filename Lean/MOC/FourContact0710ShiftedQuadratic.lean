import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
The scalar equations of the order-four contact family with ordinary rays
0, 7, 10, 18, and 22 of the order-four support-cost cone. The mixed ray
has coefficient one. The scalar deformation stays in the region where
the rational height is defined.
-/

namespace MOC.FourContact0710

noncomputable section

def p (a b : ℝ) : ℝ := (a + 1) * (b + 1)

def q (a b d : ℝ) : ℝ := p a b + d * (a + b + 1)

def linearParameter (a b d : ℝ) : ℝ :=
  a * b + d * (a + b) - d ^ 2 - 2 * d - 2

def constantParameter (a b d : ℝ) : ℝ :=
  (a * b - 1) * (d ^ 2 + 1) - (a - 1) * (b - 1) * d

def rootPolynomial (a b d w : ℝ) : ℝ :=
  q a b d * w ^ 2 - p a b * linearParameter a b d * w - p a b * constantParameter a b d

def branchPolynomial (a b c d e : ℝ) : ℝ :=
  rootPolynomial a b d c * e ^ 2 +
    p a b * (c + 1) * (2 * q a b d * c - p a b * linearParameter a b d) * e +
    p a b ^ 2 * (c + 1) ^ 2 * q a b d

def heightDenominator (d e : ℝ) : ℝ := e * (d - 1) - 1

def liftedWeight (a b w c : ℝ) : ℝ := p a b * (c + 1) / (w - c)

def comparisonPolynomial (a b d : ℝ) : ℝ :=
  (a + b + 2) * d ^ 2 + (a * b - a - b + 1) * d - 2 * a * b - a - b

def positiveRoot (a b d : ℝ) : ℝ :=
  let B := p a b * linearParameter a b d
  (B + Real.sqrt (B ^ 2 + 4 * q a b d * p a b * constantParameter a b d)) / (2 * q a b d)

theorem p_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 < p a b := by
  unfold p
  positivity

theorem q_pos {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) : 0 < q a b d := by
  unfold q
  exact add_pos_of_pos_of_nonneg (p_pos ha hb) (mul_nonneg hd (by positivity))

theorem branchPolynomial_shift {a b c d e : ℝ} (he : e ≠ 0) :
    branchPolynomial a b c d e =
      e ^ 2 * rootPolynomial a b d (c + p a b * (c + 1) / e) := by
  unfold branchPolynomial rootPolynomial
  field_simp [he]
  ring

theorem branchPolynomial_pos_at_zero {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 < branchPolynomial a b c d 0 := by
  have hp := p_pos ha hb
  have hq := q_pos ha hb hd
  have hmain : 0 < p a b ^ 2 * (c + 1) ^ 2 * q a b d := by positivity
  simpa [branchPolynomial] using hmain

theorem constantParameter_eq (a b d : ℝ) :
    constantParameter a b d = (a * b - 1) * (d - 1) ^ 2 + d * (p a b - 4) := by
  unfold constantParameter p
  ring

theorem rootPolynomial_at_product_sub_one (a b d : ℝ) :
    rootPolynomial a b d (a * b - 1) = -a * b * d * (a - b) ^ 2 := by
  unfold rootPolynomial q p linearParameter constantParameter
  ring

private theorem p_gt_four_of_product_ge_one {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a ≠ b) (hab : 1 ≤ a * b) :
    4 < p a b := by
  have hsq := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hsum : 2 < a + b := by
    by_contra! h
    have hh := mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 2 + (a + b) by positivity)
    nlinarith only [hh, hsq, hab]
  unfold p
  nlinarith only [hsum, hab]

/-- A nonpositive value at a positive argument forces a negative
constant term in the normalized quadratic. -/
theorem constantParameter_pos_of_rootPolynomial_nonpos {a b d w : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (hne : a ≠ b)
    (hw : 0 < w) (hA : rootPolynomial a b d w ≤ 0) :
    0 < constantParameter a b d := by
  by_cases hab : 1 ≤ a * b
  · rw [constantParameter_eq]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _))
      (mul_pos hd (sub_pos.mpr (p_gt_four_of_product_ge_one ha hb hne hab)))
  · let r := a * b - 1
    have hr : r < 0 := sub_neg.mpr (lt_of_not_ge hab)
    have hAt : rootPolynomial a b d r ≤ 0 := by
      change rootPolynomial a b d (a * b - 1) ≤ 0
      rw [rootPolynomial_at_product_sub_one]
      have h := mul_nonneg (mul_nonneg (mul_nonneg ha hb) hd.le) (sq_nonneg (a - b))
      nlinarith only [h]
    have hidentity :
        rootPolynomial a b d r * w - r * rootPolynomial a b d w =
          (r - w) * (q a b d * r * w + p a b * constantParameter a b d) := by
      unfold rootPolynomial
      ring
    by_contra! h
    have hleft := sub_nonpos.mpr
      ((mul_nonpos_of_nonpos_of_nonneg hAt hw.le).trans
        (mul_nonneg_of_nonpos_of_nonpos hr.le hA))
    have hright := mul_pos_of_neg_of_neg (sub_neg.mpr (hr.trans hw))
      (add_neg_of_neg_of_nonpos
        (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (q_pos ha hb hd.le) hr) hw)
        (mul_nonpos_of_nonneg_of_nonpos (p_pos ha hb).le h))
    rw [hidentity] at hleft
    exact (not_lt_of_ge hleft) hright

/-- The explicit root is positive and solves the quadratic throughout
the negative-constant-term region. -/
theorem positiveRoot_spec {a b d : ℝ} (hp : 0 < p a b) (hq : 0 < q a b d)
    (hS : 0 < constantParameter a b d) :
    0 < positiveRoot a b d ∧ rootPolynomial a b d (positiveRoot a b d) = 0 := by
  let B := p a b * linearParameter a b d
  let D := B ^ 2 + 4 * q a b d * p a b * constantParameter a b d
  have hD : 0 < D := add_pos_of_nonneg_of_pos (sq_nonneg _)
    (by change 0 < 4 * q a b d * p a b * constantParameter a b d; positivity)
  have hsq : (Real.sqrt D) ^ 2 = D := Real.sq_sqrt hD.le
  have habs : |B| < Real.sqrt D := by
    apply (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, hsq]
    exact lt_add_of_pos_right _ (by positivity)
  have hnum : 0 < B + Real.sqrt D := by
    have hB := neg_le_abs B
    linarith only [hB, habs]
  constructor
  · change 0 < (B + Real.sqrt D) / (2 * q a b d)
    exact div_pos hnum (by positivity)
  · change q a b d * ((B + Real.sqrt D) / (2 * q a b d)) ^ 2 -
      B * ((B + Real.sqrt D) / (2 * q a b d)) - p a b * constantParameter a b d = 0
    field_simp [ne_of_gt hq]
    have hsquare : (Real.sqrt D) ^ 2 = B ^ 2 + 4 * q a b d * p a b * constantParameter a b d := hsq
    linear_combination 2 * q a b d ^ 2 * hsquare

/-- The sign of the quadratic on the positive axis changes at its
unique positive root. -/
theorem rootPolynomial_neg_iff_lt_positiveRoot {a b d x : ℝ} (hp : 0 < p a b)
    (hq : 0 < q a b d) (hS : 0 < constantParameter a b d) (hx : 0 < x) :
    rootPolynomial a b d x < 0 ↔ x < positiveRoot a b d := by
  let w := positiveRoot a b d
  obtain ⟨hw, hAw⟩ := positiveRoot_spec hp hq hS
  have hfactor :
      w * rootPolynomial a b d x =
        (x - w) * (q a b d * w * x + p a b * constantParameter a b d) := by
    change rootPolynomial a b d w = 0 at hAw
    unfold rootPolynomial at *
    linear_combination x * hAw
  have hpos : 0 < q a b d * w * x + p a b * constantParameter a b d :=
    add_pos (mul_pos (mul_pos hq hw) hx) (mul_pos hp hS)
  calc
    _ ↔ w * rootPolynomial a b d x < w * 0 := (mul_lt_mul_left hw).symm
    _ ↔ (x - w) * (q a b d * w * x + p a b * constantParameter a b d) <
          0 * (q a b d * w * x + p a b * constantParameter a b d) := by
      rw [hfactor, mul_zero, zero_mul]
    _ ↔ _ := (mul_lt_mul_right hpos).trans sub_neg

theorem positive_root_eq {a b d x : ℝ} (hp : 0 < p a b) (hq : 0 < q a b d)
    (hS : 0 < constantParameter a b d) (hx : 0 < x)
    (hA : rootPolynomial a b d x = 0) : x = positiveRoot a b d := by
  let w := positiveRoot a b d
  obtain ⟨hw, hAw⟩ := positiveRoot_spec hp hq hS
  have hfactor :
      (x - w) * (q a b d * w * x + p a b * constantParameter a b d) = 0 := by
    change rootPolynomial a b d w = 0 at hAw
    unfold rootPolynomial at *
    linear_combination w * hA - x * hAw
  have hpos : 0 < q a b d * w * x + p a b * constantParameter a b d :=
    add_pos (mul_pos (mul_pos hq hw) hx) (mul_pos hp hS)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpos))

theorem rootPolynomial_comparison (a b d : ℝ) :
    rootPolynomial a b d (p a b * (d - 1)) =
      p a b * (p a b * (d - 1) + 1) * comparisonPolynomial a b d := by
  unfold rootPolynomial q p linearParameter constantParameter comparisonPolynomial
  ring

theorem comparisonPolynomial_one (a b : ℝ) :
    comparisonPolynomial a b 1 = 4 - p a b := by
  unfold comparisonPolynomial p
  ring

theorem comparisonPolynomial_monotone {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    comparisonPolynomial a b x ≤ comparisonPolynomial a b y := by
  have hsec : comparisonPolynomial a b y - comparisonPolynomial a b x =
      (y - x) * (a * b + a + b + 5 + (a + b + 2) * ((x - 1) + (y - 1))) := by
    unfold comparisonPolynomial
    ring
  have hy : 1 ≤ y := hx.trans hxy
  have hnonneg : 0 ≤ (y - x) * (a * b + a + b + 5 +
      (a + b + 2) * ((x - 1) + (y - 1))) := by
    have hx₀ := sub_nonneg.mpr hx
    have hy₀ := sub_nonneg.mpr hy
    have hxy₀ := sub_nonneg.mpr hxy
    positivity
  exact sub_nonneg.mp (hsec.symm ▸ hnonneg)

theorem liftedWeight_pos {a b w c : ℝ} (hp : 0 < p a b) (hc : 0 ≤ c) (hw : c < w) :
    0 < liftedWeight a b w c := by
  unfold liftedWeight
  exact div_pos (mul_pos hp (by positivity)) (sub_pos.mpr hw)

theorem branchPolynomial_liftedWeight_eq_zero {a b c d w : ℝ}
    (hp : 0 < p a b) (hc : 0 ≤ c) (hw : c < w) (hA : rootPolynomial a b d w = 0) :
    branchPolynomial a b c d (liftedWeight a b w c) = 0 := by
  have he := ne_of_gt (liftedWeight_pos hp hc hw)
  have hn : p a b * (c + 1) ≠ 0 := ne_of_gt (mul_pos hp (by positivity))
  have hrecover : c + p a b * (c + 1) / liftedWeight a b w c = w := by
    unfold liftedWeight
    field_simp [hn, ne_of_gt (sub_pos.mpr hw)]
  rw [branchPolynomial_shift he, hrecover, hA, mul_zero]

theorem heightDenominator_liftedWeight {a b c d w : ℝ} (hw : c < w) :
    heightDenominator d (liftedWeight a b w c) =
      (p a b * (d - 1) - w + c * (p a b * (d - 1) + 1)) / (w - c) := by
  unfold heightDenominator liftedWeight
  field_simp [ne_of_gt (sub_pos.mpr hw)]
  ring

private theorem divide_neg_iff_of_positive_denominator {u v : ℝ} (hv : 0 < v) :
    u / v < 0 ↔ u < 0 := by
  constructor
  · intro h
    rcases div_neg_iff.mp h with h | h
    · exact (not_lt_of_ge hv.le h.2).elim
    · exact h.1
  · exact fun h => div_neg_of_neg_of_pos h hv

/-- Holding the root and the other ordinary coefficients fixed, every
smaller nonnegative third coefficient remains feasible for the height equation. -/
theorem heightDenominator_neg_on_c_interval {a b c c' d w : ℝ} (hp : 0 < p a b)
    (hc' : 0 ≤ c') (hcc : c' ≤ c) (hw : c < w)
    (hQ : heightDenominator d (liftedWeight a b w c) < 0) :
    heightDenominator d (liftedWeight a b w c') < 0 := by
  by_cases hd : d ≤ 1
  · unfold heightDenominator
    have he := (liftedWeight_pos hp hc' (hcc.trans_lt hw)).le
    have hprod := mul_nonpos_of_nonneg_of_nonpos he (sub_nonpos.mpr hd)
    linarith only [hprod]
  · have hw' := hcc.trans_lt hw
    rw [heightDenominator_liftedWeight hw] at hQ
    rw [heightDenominator_liftedWeight hw']
    have hN := (divide_neg_iff_of_positive_denominator (sub_pos.mpr hw)).mp hQ
    apply (divide_neg_iff_of_positive_denominator (sub_pos.mpr hw')).mpr
    have hmul := mul_le_mul_of_nonneg_right hcc
      (show 0 ≤ p a b * (d - 1) + 1 by
        exact add_nonneg (mul_nonneg hp.le (sub_nonneg.mpr (le_of_not_ge hd))) zero_le_one)
    linarith only [hN, hmul]

theorem heightDenominator_neg_at_zero_iff_comparison {a b d : ℝ}
    (hp : 0 < p a b) (hq : 0 < q a b d) (hS : 0 < constantParameter a b d) (hd : 1 < d) :
    heightDenominator d (liftedWeight a b (positiveRoot a b d) 0) < 0 ↔
      comparisonPolynomial a b d < 0 := by
  have hw := (positiveRoot_spec hp hq hS).1
  have harg : 0 < p a b * (d - 1) := mul_pos hp (sub_pos.mpr hd)
  rw [heightDenominator_liftedWeight hw, divide_neg_iff_of_positive_denominator (sub_pos.mpr hw)]
  simp only [zero_mul, add_zero, sub_neg]
  rw [← rootPolynomial_neg_iff_lt_positiveRoot hp hq hS harg, rootPolynomial_comparison]
  simpa only [mul_zero] using
    (mul_lt_mul_left (mul_pos hp (add_pos harg zero_lt_one))
      (b := comparisonPolynomial a b d) (c := 0))

private theorem constantParameter_pos_on_lower_interval {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a ≠ b) (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1)
    (hS : 0 < constantParameter a b x) : 0 < constantParameter a b y := by
  by_cases hab : 1 ≤ a * b
  · rw [constantParameter_eq]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _))
      (mul_pos (hx.trans_le hxy) (sub_pos.mpr (p_gt_four_of_product_ge_one ha hb hne hab)))
  · have hprod := sub_nonpos.mpr (le_of_not_ge hab)
    have hfact : x * constantParameter a b y - y * constantParameter a b x =
        (a * b - 1) * ((y - x) * (x * y - 1)) := by
      unfold constantParameter
      ring
    have hxy' : x * y ≤ 1 := by
      exact (mul_le_mul_of_nonneg_right (hxy.trans hy) (hx.trans_le hxy).le).trans
        (by simpa only [one_mul] using hy)
    have hnonneg := mul_nonneg_of_nonpos_of_nonpos hprod
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) (sub_nonpos.mpr hxy'))
    have hright := mul_pos (hx.trans_le hxy) hS
    have hpos : 0 < x * constantParameter a b y := by linarith only [hfact, hnonneg, hright]
    exact (mul_pos_iff_of_pos_left hx).mp hpos

/-- On the third-coefficient-zero slice, move the fourth coefficient
toward one. At every intermediate value the explicit positive root
gives a feasible fifth coefficient. -/
theorem liftedWeight_feasible_on_d_interval {a b d₀ d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a ≠ b) (hd₀ : 0 < d₀)
    (hS₀ : 0 < constantParameter a b d₀)
    (hQ₀ : heightDenominator d₀ (liftedWeight a b (positiveRoot a b d₀) 0) < 0)
    (hinterval : (d₀ ≤ d ∧ d ≤ 1) ∨ (1 ≤ d ∧ d ≤ d₀)) :
    let w := positiveRoot a b d
    let e := liftedWeight a b w 0
    0 < constantParameter a b d ∧ 0 < e ∧
      branchPolynomial a b 0 d e = 0 ∧ heightDenominator d e < 0 := by
  have hp := p_pos ha hb
  have hd : 0 < d := hinterval.elim (fun h => hd₀.trans_le h.1) (fun h => zero_lt_one.trans_le h.1)
  have hq := q_pos ha hb hd.le
  have hs : 0 < constantParameter a b d := by
    rcases hinterval with h | h
    · exact constantParameter_pos_on_lower_interval ha hb hne hd₀ h.1 h.2 hS₀
    · by_cases hd1 : d = 1
      · subst d
        by_cases hd₀1 : d₀ = 1
        · simpa only [hd₀1] using hS₀
        · have hD := lt_of_le_of_ne h.2 (Ne.symm hd₀1)
          have hK₀ := (heightDenominator_neg_at_zero_iff_comparison hp
            (q_pos ha hb hd₀.le) hS₀ hD).mp hQ₀
          have hK := (comparisonPolynomial_monotone ha hb (le_refl 1) h.2).trans_lt hK₀
          rw [comparisonPolynomial_one] at hK
          rw [constantParameter_eq]
          nlinarith only [hK]
      · have hD := lt_of_le_of_ne h.1 (Ne.symm hd1)
        have hK₀ := (heightDenominator_neg_at_zero_iff_comparison hp
          (q_pos ha hb hd₀.le) hS₀ (hD.trans_le h.2)).mp hQ₀
        have hK := (comparisonPolynomial_monotone ha hb h.1 h.2).trans_lt hK₀
        have harg := mul_pos hp (sub_pos.mpr hD)
        apply constantParameter_pos_of_rootPolynomial_nonpos ha hb hd hne harg
        rw [rootPolynomial_comparison]
        exact (mul_neg_of_pos_of_neg (mul_pos hp (add_pos harg zero_lt_one)) hK).le
  obtain ⟨hw, hAw⟩ := positiveRoot_spec hp hq hs
  have he := liftedWeight_pos hp (le_refl 0) hw
  refine ⟨hs, he, branchPolynomial_liftedWeight_eq_zero hp (le_refl 0) hw hAw, ?_⟩
  by_cases hd1 : d ≤ 1
  · unfold heightDenominator
    have hprod := mul_nonpos_of_nonneg_of_nonpos he.le (sub_nonpos.mpr hd1)
    linarith only [hprod]
  · have hD := lt_of_not_ge hd1
    have hdd₀ : d ≤ d₀ := hinterval.elim (fun h => (hd1 h.2).elim) And.right
    have hK₀ := (heightDenominator_neg_at_zero_iff_comparison hp
      (q_pos ha hb hd₀.le) hS₀ (hD.trans_le hdd₀)).mp hQ₀
    exact (heightDenominator_neg_at_zero_iff_comparison hp hq hs hD).mpr
      ((comparisonPolynomial_monotone ha hb hD.le hdd₀).trans_lt hK₀)

/-- Passing both scalar equations forces the first two weights to satisfy
the strict product condition at the endpoint. -/
theorem p_gt_four_of_admissible_start {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) (he : 0 ≤ e)
    (hne : a ≠ b) (hP : branchPolynomial a b c d e = 0)
    (hQ : heightDenominator d e < 0) : 4 < p a b := by
  have hep : 0 < e := by
    refine lt_of_le_of_ne he ?_
    intro hz
    change 0 = e at hz
    subst e
    exact (ne_of_gt (branchPolynomial_pos_at_zero ha hb hc hd.le)) hP
  let w := c + p a b * (c + 1) / e
  have hp := p_pos ha hb
  have hpw : c < w :=
    lt_add_of_pos_right _ (div_pos (mul_pos hp (by positivity)) hep)
  have hw := hc.trans_lt hpw
  have hAw : rootPolynomial a b d w = 0 := by
    rw [branchPolynomial_shift (ne_of_gt hep)] at hP
    exact (mul_eq_zero.mp hP).resolve_left (pow_ne_zero _ (ne_of_gt hep))
  have hS := constantParameter_pos_of_rootPolynomial_nonpos ha hb hd hne hw hAw.le
  have hroot := positive_root_eq hp (q_pos ha hb hd.le) hS hw hAw
  have heq : liftedWeight a b w c = e := by
    have hden : w - c = p a b * (c + 1) / e := by dsimp only [w]; ring
    unfold liftedWeight
    rw [hden]
    have hprod : p a b * (c + 1) ≠ 0 := ne_of_gt (mul_pos hp (by positivity))
    field_simp [hprod, ne_of_gt hep]
  have hc0 := heightDenominator_neg_on_c_interval hp (le_refl 0) hc hpw (heq.symm ▸ hQ)
  rw [hroot] at hc0
  have hi : (d ≤ 1 ∧ (1 : ℝ) ≤ 1) ∨ ((1 : ℝ) ≤ 1 ∧ 1 ≤ d) := by
    rcases le_total d 1 with h | h
    · exact Or.inl ⟨h, le_refl 1⟩
    · exact Or.inr ⟨le_refl 1, h⟩
  have h1 := (liftedWeight_feasible_on_d_interval (d := 1) ha hb hne hd hS hc0 hi).1
  rw [constantParameter_eq] at h1
  nlinarith only [h1]

/-- The positive root has continuous dependence on the fourth weight
where the leading quadratic coefficient is nonzero. -/
theorem continuousOn_positiveRoot (a b : ℝ) :
    ContinuousOn (positiveRoot a b) {d : ℝ | q a b d ≠ 0} := by
  let numerator (d : ℝ) :=
    p a b * linearParameter a b d +
      Real.sqrt ((p a b * linearParameter a b d) ^ 2 +
        4 * q a b d * p a b * constantParameter a b d)
  let denominator (d : ℝ) := 2 * q a b d
  have hn : Continuous numerator := by
    unfold numerator linearParameter constantParameter q p
    fun_prop
  have hd : Continuous denominator := by
    unfold denominator q p
    fun_prop
  exact hn.continuousOn.div hd.continuousOn
    (fun d hd => mul_ne_zero (by norm_num) hd)

/-- The lifted fifth weight is continuous as the third weight varies
strictly below a fixed positive root. -/
theorem continuousOn_liftedWeight (a b w : ℝ) :
    ContinuousOn (liftedWeight a b w) {c : ℝ | c < w} := by
  have hn : Continuous (fun c : ℝ => p a b * (c + 1)) := by fun_prop
  have hd : Continuous (fun c : ℝ => w - c) := by fun_prop
  exact hn.continuousOn.div hd.continuousOn
    (fun c hc => ne_of_gt (sub_pos.mpr hc))

end

end MOC.FourContact0710
