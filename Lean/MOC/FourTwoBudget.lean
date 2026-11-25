import MOC.MixedBound
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! The two-budget inequality for the order-four mixed facet and its
two minor donors, in the quaternion coordinates of historical facets
`f1`, `f9`, and `f22`. -/

namespace MOC

private theorem sqrt_pair_increment {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) :
    √(a * b) + √((c - a) * (d - b)) ≤ √(c * d) := by
  have hab := mul_nonneg ha hb
  have hcd := mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hbd)
  have hcross : 2 * (√(a * b) * √((c - a) * (d - b))) ≤
      a * (d - b) + b * (c - a) := by
    rw [← Real.sqrt_mul hab, show a * b * ((c - a) * (d - b)) =
      (a * (d - b)) * (b * (c - a)) by ring,
      Real.sqrt_mul (mul_nonneg ha (sub_nonneg.mpr hbd))]
    nlinarith only [sq_nonneg (√(a * (d - b)) - √(b * (c - a))),
      Real.sq_sqrt (mul_nonneg ha (sub_nonneg.mpr hbd)),
      Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hac))]
  apply Real.le_sqrt_of_sq_le
  rw [add_sq, Real.sq_sqrt hab, Real.sq_sqrt hcd]
  nlinarith only [hcross]

private theorem abs_pair_increment {a b c d : ℝ} (hac : a ^ 2 ≤ c ^ 2)
    (hbd : b ^ 2 ≤ d ^ 2) :
    |a * b| + √((c ^ 2 - a ^ 2) * (d ^ 2 - b ^ 2)) ≤ |c * d| := by
  simpa only [← mul_pow, Real.sqrt_sq_eq_abs] using
    sqrt_pair_increment (sq_nonneg a) (sq_nonneg b) hac hbd

private theorem pair_energy {d e k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l)
    (h : √k + √l ≤ |d - e|) :
    4 * min k l ≤ 2 * d ^ 2 + 2 * e ^ 2 := by
  have hmin : 0 ≤ min k l := le_min hk hl
  have hs : 2 * √(min k l) ≤ √k + √l := by
    have h₁ := Real.sqrt_le_sqrt (min_le_left k l)
    have h₂ := Real.sqrt_le_sqrt (min_le_right k l)
    linarith only [h₁, h₂]
  have hs' := (sq_le_sq₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg (min k l)))
    (abs_nonneg (d - e))).2 (hs.trans h)
  rw [mul_pow, Real.sq_sqrt hmin, sq_abs] at hs'
  nlinarith only [hs', sq_nonneg (d + e)]

private theorem paired_difference_energy (p q : Fin 4 → ℝ)
    (hn : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 =
      q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2)
    (v : Fin 4 → ℝ) (hv : ∀ i, v i = p i ^ 2 - q i ^ 2) :
    4 * min (v 0 * v 2) (v 1 * v 3) ≤
      2 * (|p 0 * p 2| - |p 1 * p 3|) ^ 2 + 2 * (|q 0 * q 2| - |q 1 * q 3|) ^ 2 := by
  let d := |p 0 * p 2| - |p 1 * p 3|
  let e := |q 0 * q 2| - |q 1 * q 3|
  let k := v 0 * v 2
  let l := v 1 * v 3
  change 4 * min k l ≤ 2 * d ^ 2 + 2 * e ^ 2
  by_cases hk : k ≤ 0
  · have hm := (min_le_left k l).trans hk
    nlinarith only [hm, sq_nonneg d, sq_nonneg e]
  by_cases hl : l ≤ 0
  · have hm := (min_le_right k l).trans hl
    nlinarith only [hm, sq_nonneg d, sq_nonneg e]
  have hk' : 0 < v 0 * v 2 := lt_of_not_ge hk
  have hl' : 0 < v 1 * v 3 := lt_of_not_ge hl
  have hsum : v 0 + v 1 + v 2 + v 3 = 0 := by simp only [hv]; linarith only [hn]
  apply pair_energy hk'.le hl'.le
  rcases mul_pos_iff.mp hk' with ⟨hv₀, hv₂⟩ | ⟨hv₀, hv₂⟩
  · have hh : v 1 < 0 ∧ v 3 < 0 := by
      rcases mul_pos_iff.mp hl' with hh | hh
      · exfalso
        linarith only [hsum, hv₀, hv₂, hh.1, hh.2]
      · exact hh
    have h₀ : √k + |q 0 * q 2| ≤ |p 0 * p 2| := by
      rw [add_comm]
      dsimp only [k]
      rw [hv 0, hv 2]
      have h₀' : q 0 ^ 2 ≤ p 0 ^ 2 := sub_nonneg.mp (hv 0 ▸ hv₀.le)
      have h₂' : q 2 ^ 2 ≤ p 2 ^ 2 := sub_nonneg.mp (hv 2 ▸ hv₂.le)
      exact abs_pair_increment h₀' h₂'
    have h₁ : √l + |p 1 * p 3| ≤ |q 1 * q 3| := by
      rw [add_comm]
      have heq : l = (q 1 ^ 2 - p 1 ^ 2) * (q 3 ^ 2 - p 3 ^ 2) := by
        dsimp only [l]; rw [hv 1, hv 3]; ring
      rw [heq]
      have h₁' : p 1 ^ 2 ≤ q 1 ^ 2 := sub_nonpos.mp (hv 1 ▸ hh.1.le)
      have h₃' : p 3 ^ 2 ≤ q 3 ^ 2 := sub_nonpos.mp (hv 3 ▸ hh.2.le)
      exact abs_pair_increment h₁' h₃'
    have hde : √k + √l ≤ d - e := by dsimp only [d, e]; linarith only [h₀, h₁]
    exact hde.trans (le_abs_self _)
  · have hh : 0 < v 1 ∧ 0 < v 3 := by
      rcases mul_pos_iff.mp hl' with hh | hh
      · exact hh
      · exfalso
        linarith only [hsum, hv₀, hv₂, hh.1, hh.2]
    have h₀ : √k + |p 0 * p 2| ≤ |q 0 * q 2| := by
      rw [add_comm]
      have heq : k = (q 0 ^ 2 - p 0 ^ 2) * (q 2 ^ 2 - p 2 ^ 2) := by
        dsimp only [k]; rw [hv 0, hv 2]; ring
      rw [heq]
      have h₀' : p 0 ^ 2 ≤ q 0 ^ 2 := sub_nonpos.mp (hv 0 ▸ hv₀.le)
      have h₂' : p 2 ^ 2 ≤ q 2 ^ 2 := sub_nonpos.mp (hv 2 ▸ hv₂.le)
      exact abs_pair_increment h₀' h₂'
    have h₁ : √l + |q 1 * q 3| ≤ |p 1 * p 3| := by
      rw [add_comm]
      dsimp only [l]
      rw [hv 1, hv 3]
      have h₁' : q 1 ^ 2 ≤ p 1 ^ 2 := sub_nonneg.mp (hv 1 ▸ hh.1.le)
      have h₃' : q 3 ^ 2 ≤ p 3 ^ 2 := sub_nonneg.mp (hv 3 ▸ hh.2.le)
      exact abs_pair_increment h₁' h₃'
    have hde : √k + √l ≤ -(d - e) := by dsimp only [d, e]; linarith only [h₀, h₁]
    exact hde.trans (neg_le_abs _)

/-- Equal quaternion norms give the scalar bound for the mixed facet.
The two signs in the product terms can be chosen independently. -/
theorem quaternion_two_budget_scalar (p q : Fin 4 → ℝ) (s t : ℝ)
    (hs : |s| ≤ 1) (ht : |t| ≤ 1)
    (hn : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 =
      q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2) :
    let v (i : Fin 4) := p i ^ 2 - q i ^ 2
    0 ≤ 2 * (p 0 ^ 2 * q 2 ^ 2 + p 1 ^ 2 * q 3 ^ 2 +
      p 2 ^ 2 * q 0 ^ 2 + p 3 ^ 2 * q 1 ^ 2) +
      4 * s * (p 0 * p 1 * p 2 * p 3) + 4 * t * (q 0 * q 1 * q 2 * q 3) +
      2 * |(v 2 + v 3) * (v 1 + v 2)| := by
  let v (i : Fin 4) := p i ^ 2 - q i ^ 2
  let k := v 0 * v 2
  let l := v 1 * v 3
  have henergy := paired_difference_energy p q hn v (fun _ => rfl)
  have hd : (v 2 + v 3) * (v 1 + v 2) = l - k := by
    have hsum : v 0 + v 1 + v 2 + v 3 = 0 := by dsimp only [v]; linarith only [hn]
    dsimp only [k, l]
    linear_combination v 2 * hsum
  have hm : k + l - |l - k| = 2 * min k l := by
    rcases le_total k l with h | h
    · rw [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  let P := (p 0 * p 2) * (p 1 * p 3)
  let Q := (q 0 * q 2) * (q 1 * q 3)
  have hP : -|P| ≤ s * P := by
    have hh := mul_le_mul_of_nonneg_right hs (abs_nonneg P)
    rw [one_mul, ← abs_mul] at hh
    linarith only [hh, neg_le_abs (s * P)]
  have hQ : -|Q| ≤ t * Q := by
    have hh := mul_le_mul_of_nonneg_right ht (abs_nonneg Q)
    rw [one_mul, ← abs_mul] at hh
    linarith only [hh, neg_le_abs (t * Q)]
  have hid : 2 * (p 0 ^ 2 * q 2 ^ 2 + p 1 ^ 2 * q 3 ^ 2 +
      p 2 ^ 2 * q 0 ^ 2 + p 3 ^ 2 * q 1 ^ 2) - 4 * |P| - 4 * |Q| =
      2 * (|p 0 * p 2| - |p 1 * p 3|) ^ 2 + 2 * (|q 0 * q 2| - |q 1 * q 3|) ^ 2 -
      2 * (k + l) := by
    dsimp only [P, Q, k, l, v]
    rw [abs_mul (p 0 * p 2), abs_mul (q 0 * q 2), sub_sq, sub_sq,
      sq_abs, sq_abs, sq_abs, sq_abs]
    ring
  change 0 ≤ _ + 4 * s * (p 0 * p 1 * p 2 * p 3) + 4 * t * (q 0 * q 1 * q 2 * q 3) +
    2 * |(v 2 + v 3) * (v 1 + v 2)|
  rw [hd, show p 0 * p 1 * p 2 * p 3 = P by dsimp only [P]; ring,
    show q 0 * q 1 * q 2 * q 3 = Q by dsimp only [Q]; ring]
  nlinarith only [henergy, hm, hP, hQ, hid]

/-- A scalar mixed bound and the capacity `c² ≤ ab` give the corresponding
weighted support inequality, including vanishing donors. -/
theorem two_budget_of_scalar {a b c X Y F : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcap : c ^ 2 ≤ a * b) (hscalar : 0 ≤ F + 2 * |X * Y|) :
    0 ≤ a * X ^ 2 + b * Y ^ 2 + c * F := by
  have hsq : (2 * c * |X * Y|) ^ 2 ≤ (a * X ^ 2 + b * Y ^ 2) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hcap (sq_nonneg (X * Y))
    rw [mul_pow, sq_abs]
    nlinarith only [hh, sq_nonneg (a * X ^ 2 - b * Y ^ 2)]
  have hsum := (sq_le_sq₀ (by positivity) (add_nonneg (mul_nonneg ha (sq_nonneg X))
    (mul_nonneg hb (sq_nonneg Y)))).1 hsq
  nlinarith only [hsum, mul_nonneg hc hscalar]

private theorem vector_zero {α : Type*} (a b c d : α) : ![a, b, c, d] 0 = a := rfl
private theorem vector_one {α : Type*} (a b c d : α) : ![a, b, c, d] 1 = b := rfl
private theorem vector_two {α : Type*} (a b c d : α) : ![a, b, c, d] 2 = c := rfl
private theorem vector_three {α : Type*} (a b c d : α) : ![a, b, c, d] 3 = d := rfl

/-- The `f1`, `f9`, and `f22` compensation on a quaternion rotation,
written directly in squared entries and squared minors. -/
theorem quaternionRotation_two_budget_nonneg {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ^ 2 ≤ a * b)
    (p q : Fin 4 → ℝ) (hp : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 1)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1) :
    let O := quaternionRotation p q
    let m (i j k l : Fin 4) := O i k * O j l - O i l * O j k
    0 ≤ a * (m 0 1 2 3) ^ 2 + b * (m 0 3 1 2) ^ 2 +
      c * (O 0 2 ^ 2 + O 1 3 ^ 2 + (m 1 3 1 2) ^ 2 - (m 1 2 1 3) ^ 2) := by
  let O := quaternionRotation p q
  let m (i j k l : Fin 4) := O i k * O j l - O i l * O j k
  let P := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2
  let Q := q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2
  change P = 1 at hp
  change Q = 1 at hq
  have hm₀ : m 0 1 2 3 = -(p 2 ^ 2 + p 3 ^ 2 - q 2 ^ 2 - q 3 ^ 2) := by
    calc
      _ = (q 2 ^ 2 + q 3 ^ 2) * P - (p 2 ^ 2 + p 3 ^ 2) * Q := by
        simp only [m, O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vector_zero, vector_one, vector_two, vector_three, P, Q]
        ring
      _ = _ := by rw [hp, hq]; ring
  have hm₁ : m 0 3 1 2 = -(p 1 ^ 2 + p 2 ^ 2 - q 1 ^ 2 - q 2 ^ 2) := by
    calc
      _ = (q 1 ^ 2 + q 2 ^ 2) * P - (p 1 ^ 2 + p 2 ^ 2) * Q := by
        simp only [m, O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vector_zero, vector_one, vector_two, vector_three, P, Q]
        ring
      _ = _ := by rw [hp, hq]; ring
  have hm₂ : m 1 3 1 2 = p 0 * p 1 - p 2 * p 3 - q 0 * q 1 - q 2 * q 3 := by
    calc
      _ = (p 0 * p 1 - p 2 * p 3) * Q - (q 0 * q 1 + q 2 * q 3) * P := by
        simp only [m, O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vector_zero, vector_one, vector_two, vector_three, P, Q]
        ring
      _ = _ := by rw [hp, hq]; ring
  have hm₃ : m 1 2 1 3 = -p 0 * p 1 - p 2 * p 3 + q 0 * q 1 - q 2 * q 3 := by
    calc
      _ = (-p 0 * p 1 - p 2 * p 3) * Q + (q 0 * q 1 - q 2 * q 3) * P := by
        simp only [m, O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vector_zero, vector_one, vector_two, vector_three, P, Q]
        ring
      _ = _ := by rw [hp, hq]; ring
  have hF : O 0 2 ^ 2 + O 1 3 ^ 2 + (m 1 3 1 2) ^ 2 - (m 1 2 1 3) ^ 2 =
      2 * (p 0 ^ 2 * q 2 ^ 2 + p 1 ^ 2 * q 3 ^ 2 +
        p 2 ^ 2 * q 0 ^ 2 + p 3 ^ 2 * q 1 ^ 2) +
        4 * (-1 : ℝ) * (p 0 * p 1 * p 2 * p 3) + 4 * 1 * (q 0 * q 1 * q 2 * q 3) := by
    rw [hm₂, hm₃]
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      vector_zero, vector_one, vector_two, vector_three]
    ring
  have h := quaternion_two_budget_scalar p q (-1) 1 (by norm_num) (by norm_num) (hp.trans hq.symm)
  dsimp only at h
  have hd₀ : m 0 1 2 3 = -((p 2 ^ 2 - q 2 ^ 2) + (p 3 ^ 2 - q 3 ^ 2)) := by rw [hm₀]; ring
  have hd₁ : m 0 3 1 2 = -((p 1 ^ 2 - q 1 ^ 2) + (p 2 ^ 2 - q 2 ^ 2)) := by rw [hm₁]; ring
  change 0 ≤ a * (m 0 1 2 3) ^ 2 + b * (m 0 3 1 2) ^ 2 +
    c * (O 0 2 ^ 2 + O 1 3 ^ 2 + (m 1 3 1 2) ^ 2 - (m 1 2 1 3) ^ 2)
  apply two_budget_of_scalar ha hb hc hcap
  rw [hF, hd₀, hd₁, neg_mul_neg]
  exact h

end MOC
