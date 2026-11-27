import MOC.FourTwoBudgetMinor

/-! A geometric-mean bound for two squared minors in order four. -/

open Matrix

namespace MOC

private theorem four_geometric_mean_minor_budget {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap : c ^ 2 ≤ a * b)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    0 ≤ a * m {0, 3} {0, 2} + b * m {0, 2} {0, 3} +
      c * (m {0} {0} + m {3} {2} + m {0, 2} {2, 3} - m {0, 1} {0, 3}) := by
  let r := fourPerm 2
  let s := fourPerm 8
  let V := Uᵀ.submatrix r s
  have htrans : IsUnitary Uᵀ := by
    have ht : (Uᵀ)ᴴ = (Uᴴ)ᵀ := by ext i j; rfl
    constructor
    · rw [ht, ← Matrix.transpose_mul, hU.2, Matrix.transpose_one]
    · rw [ht, ← Matrix.transpose_mul, hU.1, Matrix.transpose_one]
  have hV : IsUnitary V := unitary_reindex r s htrans
  have hv (i j : Fin 4) : V i j = U (s j) (r i) := rfl
  have hsingle (i j : Fin 4) : subsetMinorSq V {i} {j} = subsetMinorSq U {s j} {r i} := by
    rw [subsetMinorSq_singleton V hV, subsetMinorSq_singleton U hU, hv]
  have hpair (i k j l : Fin 4) (hi : i ≠ k) (hj : j ≠ l) :
      subsetMinorSq V {i, k} {j, l} = subsetMinorSq U {s j, s l} {r i, r k} := by
    rw [subsetMinorSq_pair V hV hi hj, subsetMinorSq_pair U hU
      (fun h => hj (s.injective h)) (fun h => hi (r.injective h))]
    simp only [hv, mul_comm]
  have hr₀ : r 0 = 0 := by decide +kernel
  have hr₁ : r 1 = 2 := by decide +kernel
  have hr₂ : r 2 = 1 := by decide +kernel
  have hr₃ : r 3 = 3 := by decide +kernel
  have hs₁ : s 1 = 2 := by decide +kernel
  have hs₂ : s 2 = 0 := by decide +kernel
  have hs₃ : s 3 = 3 := by decide +kernel
  have hcompl : subsetMinorSq U {2, 3} {1, 2} = subsetMinorSq U {0, 1} {0, 3} := by
    have h := subsetMinorSq_compl U hU {0, 1} {0, 3}
    rwa [show ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} by decide +kernel,
      show ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} by decide +kernel] at h
  have h := four_two_budget_minor_nonneg ha hb hc hcap V hV
  dsimp only at h
  rw [hsingle 0 2, hsingle 1 3,
    hpair 0 1 2 3 (by decide) (by decide), hpair 0 3 1 2 (by decide) (by decide),
    hpair 1 3 1 2 (by decide) (by decide), hpair 1 2 1 3 (by decide) (by decide)] at h
  simpa only [hr₀, hr₁, hr₂, hr₃, hs₁, hs₂, hs₃,
    Finset.pair_comm (2 : Fin 4) 0, Finset.pair_comm (2 : Fin 4) 1, hcompl] using h

private theorem le_twice_sqrt_product_of_budget {x y gap : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hbudget : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → c ^ 2 ≤ a * b →
      c * gap ≤ a * x + b * y) :
    gap ≤ 2 * Real.sqrt (x * y) := by
  by_cases hzero : x * y = 0
  · have zero_side (v : ℝ) (hv : 0 ≤ v) (h : ∀ t : ℝ, 0 < t → gap ≤ t * v) : gap ≤ 0 := by
      by_contra! hgap
      have hd : 0 < v + 1 := by linarith only [hv]
      let t := gap / (v + 1)
      have ht : 0 < t := div_pos hgap hd
      have hlt : t * v < gap := by
        dsimp only [t]
        rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
        nlinarith only [hgap]
      exact (not_lt_of_ge (h t ht)) hlt
    rw [hzero, Real.sqrt_zero, mul_zero]
    rcases mul_eq_zero.mp hzero with hz | hz
    · apply zero_side y hy
      intro t ht
      have hcap : (1 : ℝ) ^ 2 ≤ t⁻¹ * t := by rw [inv_mul_cancel₀ ht.ne', one_pow]
      simpa only [hz, mul_zero, zero_add, one_mul] using
        hbudget t⁻¹ t 1 (inv_nonneg.mpr ht.le) ht.le zero_le_one hcap
    · apply zero_side x hx
      intro t ht
      have hcap : (1 : ℝ) ^ 2 ≤ t * t⁻¹ := by rw [mul_inv_cancel₀ ht.ne', one_pow]
      simpa only [hz, mul_zero, add_zero, one_mul] using
        hbudget t t⁻¹ 1 ht.le (inv_nonneg.mpr ht.le) zero_le_one hcap
  · let s := Real.sqrt (x * y)
    have hs : 0 < s := Real.sqrt_pos.2 (lt_of_le_of_ne (mul_nonneg hx hy) (Ne.symm hzero))
    have hsq : s ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx hy)
    have hcap : s ^ 2 ≤ y * x := (hsq.trans (mul_comm x y)).le
    apply (mul_le_mul_left hs).mp
    calc
      s * gap ≤ y * x + x * y := hbudget y x s hy hx hs.le hcap
      _ = s * (2 * s) := by rw [mul_comm y x, ← hsq]; ring

/-- The difference between one squared two-minor and three squared minors
is at most twice the geometric mean of the two indicated squared two-minors. -/
theorem four_minor_geometric_mean (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    m {0, 1} {0, 3} - m {0} {0} - m {3} {2} - m {0, 2} {2, 3} ≤
      2 * Real.sqrt (m {0, 3} {0, 2} * m {0, 2} {0, 3}) := by
  dsimp only
  apply le_twice_sqrt_product_of_budget (subsetMinorSq_nonneg U _ _) (subsetMinorSq_nonneg U _ _)
  intro a b c ha hb hc hcap
  have h := four_geometric_mean_minor_budget ha hb hc hcap U hU
  dsimp only at h
  nlinarith only [h]

end MOC
