import MOC.PhaseDiskSextic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact scalar support tests for a stationary degree-two phase and for
two independent degree-one phases. -/

open Filter
open scoped Topology

namespace MOC

private theorem rankTwoProjectedPhase_loss (a b d x y : ℝ)
    (hc : x ^ 2 + y ^ 2 = 1) :
    a + d - (a * x + b * y + d * (2 * x ^ 2 - 1) - b * x * y) =
      ((a + 4 * d) * y ^ 2 - 2 * b * y * (1 - x) + a * (1 - x) ^ 2) / 2 := by
  linear_combination -((a + 4 * d) / 2) * hc

/-- For a stationary degree-two phase, support at the initial point is
equivalent to positive semidefiniteness of its two-by-two quadratic form.
Here `a`, `b`, and `d` are the coefficients of the first cosine, first
sine, and second cosine. Stationarity fixes the second sine coefficient
to `-b/2`. -/
theorem rankTwoProjectedPhase_support_iff (a b d : ℝ) :
    (∀ x y : ℝ, x ^ 2 + y ^ 2 = 1 →
      a * x + b * y + d * (2 * x ^ 2 - 1) - b * x * y ≤ a + d) ↔
    ∀ u v : ℝ, 0 ≤ (a + 4 * d) * u ^ 2 - 2 * b * u * v + a * v ^ 2 := by
  constructor
  · intro h u
    have hne (v : ℝ) (hv : v ≠ 0) :
        0 ≤ (a + 4 * d) * u ^ 2 - 2 * b * u * v + a * v ^ 2 := by
      let D : ℝ := u ^ 2 + v ^ 2
      have hD : 0 < D := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hv)
      let x : ℝ := 1 - 2 * v ^ 2 / D
      let y : ℝ := 2 * u * v / D
      have hc : x ^ 2 + y ^ 2 = 1 := by
        dsimp only [x, y]
        field_simp [hD.ne'] <;> dsimp only [D] <;> ring
      have hscale :
          (a + 4 * d) * y ^ 2 - 2 * b * y * (1 - x) + a * (1 - x) ^ 2 =
            (2 * v / D) ^ 2 * ((a + 4 * d) * u ^ 2 - 2 * b * u * v + a * v ^ 2) := by
        dsimp only [x, y]
        field_simp [hD.ne'] <;> ring
      have hq : 0 ≤ (a + 4 * d) * y ^ 2 - 2 * b * y * (1 - x) + a * (1 - x) ^ 2 := by
        linarith only [h x y hc, rankTwoProjectedPhase_loss a b d x y hc]
      rw [hscale] at hq
      have hr : 2 * v / D ≠ 0 :=
        div_ne_zero (mul_ne_zero (by norm_num) hv) hD.ne'
      exact (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero hr)).mp hq
    intro v
    by_cases hv : v = 0
    · subst v
      let q (s : ℝ) := (a + 4 * d) * u ^ 2 - 2 * b * u * s + a * s ^ 2
      have hq : Continuous q := by unfold q; fun_prop
      change 0 ≤ q 0
      refine le_of_tendsto_of_tendsto (b := 𝓝[≠] (0 : ℝ))
        tendsto_const_nhds (hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hne s hs
    · exact hne v hv
  · intro h x y hc
    have hq := h y (1 - x)
    linarith only [rankTwoProjectedPhase_loss a b d x y hc, hq]

/-- A nonzero cubic term in a Hessian-null stationary degree-two phase
gives a strict support ascent on the phase circle. -/
theorem rankTwoProjectedPhase_escape_of_null (a b d : ℝ)
    (ha : a + 4 * d = 0) (hb : b ≠ 0) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧
      a + d < a * x + b * y + d * (2 * x ^ 2 - 1) - b * x * y := by
  by_contra! h
  let u := (a + 1) / (2 * b)
  have hq := (rankTwoProjectedPhase_support_iff a b d).mp h u 1
  have hu : 2 * b * u = a + 1 := by
    dsimp only [u]
    field_simp [hb] <;> ring
  simp only [ha, zero_mul, mul_one, one_pow, zero_sub] at hq
  linarith only [hq, hu]

private theorem phase_linear_support_iff (a b c : ℝ) :
    (∀ x y : ℝ, x ^ 2 + y ^ 2 = 1 → a * x + b * y ≤ c) ↔
      0 ≤ c ∧ a ^ 2 + b ^ 2 ≤ c ^ 2 := by
  constructor
  · intro h
    have hc : 0 ≤ c := by
      have hp := h 1 0 (by norm_num)
      have hn := h (-1) 0 (by norm_num)
      norm_num at hp hn
      linarith only [hp, hn]
    let r := Real.sqrt (a ^ 2 + b ^ 2)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hs : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
    refine ⟨hc, ?_⟩
    rw [← hs]
    by_cases hz : r = 0
    · rw [hz]
      positivity
    have hxy : (a / r) ^ 2 + (b / r) ^ 2 = 1 := by
      field_simp [hz] <;> nlinarith only [hs]
    have hsum : a * (a / r) + b * (b / r) = r := by
      field_simp [hz] <;> nlinarith only [hs]
    have hrc := h (a / r) (b / r) hxy
    rw [hsum] at hrc
    exact pow_le_pow_left₀ hr hrc 2
  · rintro ⟨hc, hs⟩ x y hxy
    have hsq : (a * x + b * y) ^ 2 ≤ a ^ 2 + b ^ 2 := by
      have hi : (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 =
          (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by ring
      rw [hxy, mul_one] at hi
      linarith only [hi, sq_nonneg (a * y - b * x)]
    by_contra! h
    have hp : 0 < a * x + b * y + c := by linarith only [h, hc]
    nlinarith only [hsq, hs, mul_pos (sub_pos.mpr h) hp]

/-- Support on two independent phase circles is equivalent to a squared
bound in the second phase. The real functions `C`, `A`, and `B` are
the constant, cosine, and sine coefficients of the first phase. -/
theorem independentPhaseSupport_iff (C A B : ℝ → ℝ → ℝ) (H : ℝ) :
    (∀ x y u v : ℝ, x ^ 2 + y ^ 2 = 1 → u ^ 2 + v ^ 2 = 1 →
      C u v + A u v * x + B u v * y ≤ H) ↔
    ∀ u v : ℝ, u ^ 2 + v ^ 2 = 1 →
      0 ≤ H - C u v ∧ A u v ^ 2 + B u v ^ 2 ≤ (H - C u v) ^ 2 := by
  constructor
  · intro h u v huv
    apply (phase_linear_support_iff (A u v) (B u v) (H - C u v)).mp
    intro x y hxy
    linarith only [h x y u v hxy huv]
  · intro h x y u v hxy huv
    have hi := (phase_linear_support_iff (A u v) (B u v) (H - C u v)).mpr
      (h u v huv) x y hxy
    linarith only [hi]

end MOC
