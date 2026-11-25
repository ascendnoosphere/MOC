import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The real part of a nonzero leading pole term cannot stay on the
support side through a phase interval wider than a half turn. -/

namespace MOC

private theorem phase_sector_bound (u v d : ℝ) (hne : u ≠ 0 ∨ v ≠ 0)
    (h : ∀ t ∈ Set.Ioo (-d) d, 0 ≤ u * Real.cos t + v * Real.sin t) :
    d ≤ Real.pi / 2 ∧ (d = Real.pi / 2 → 0 ≤ u ∧ v = 0) := by
  have hclosed (hd : 0 < d) :
      ∀ t ∈ Set.Icc (-d) d, 0 ≤ u * Real.cos t + v * Real.sin t := by
    have hc : IsClosed {t : ℝ | 0 ≤ u * Real.cos t + v * Real.sin t} :=
      isClosed_le continuous_const
        ((continuous_const.mul Real.continuous_cos).add (continuous_const.mul Real.continuous_sin))
    have hs := closure_minimal h hc
    rw [closure_Ioo (by linarith : -d ≠ d)] at hs
    exact hs
  have hedge (hd : Real.pi / 2 ≤ d) : 0 ≤ u ∧ v = 0 := by
    have hp : 0 < Real.pi / 2 := by positivity
    have hdc := hclosed (hp.trans_le hd)
    have hu := hdc 0 ⟨by linarith, by linarith⟩
    have hv₁ := hdc (Real.pi / 2) ⟨by linarith, hd⟩
    have hv₂ := hdc (-(Real.pi / 2)) ⟨by linarith, by linarith⟩
    simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero] at hu
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_add] at hv₁
    simp only [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two,
      mul_zero, mul_neg, mul_one, zero_add] at hv₂
    exact ⟨hu, by linarith⟩
  refine ⟨?_, fun hd => hedge hd.ge⟩
  by_contra! hd
  obtain ⟨hu, hv⟩ := hedge hd.le
  have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm (hne.resolve_right (fun h => h hv)))
  let t := min d Real.pi
  have hp := Real.pi_pos
  have ht : Real.pi / 2 < t := lt_min hd (by linarith)
  have hcos : Real.cos t < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt ht ((min_le_right _ _).trans_lt (by linarith))
  have hn := hclosed (by linarith : 0 < d) t ⟨by linarith, min_le_left _ _⟩
  rw [hv, zero_mul, add_zero] at hn
  exact (not_le_of_gt (mul_neg_of_pos_of_neg hupos hcos)) hn

/-- On a right-half-plane branch of a pole of order `m`, a nonzero
support-side pole term has order at most `m`. At equal order its ratio to
the reference pole is nonnegative real. -/
theorem contact_pole_order_bound (m q : ℕ) (hm : 0 < m) (hq : 0 < q)
    (u v : ℝ) (hne : u ≠ 0 ∨ v ≠ 0)
    (h : ∀ t ∈ Set.Ioo (- (Real.pi / (2 * m))) (Real.pi / (2 * m)),
      0 ≤ u * Real.cos ((q : ℝ) * t) + v * Real.sin ((q : ℝ) * t)) :
    q ≤ m ∧ (q = m → 0 ≤ u ∧ v = 0) := by
  let a : ℝ := Real.pi / (2 * m)
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have ha : 0 < a := by dsimp [a]; positivity
  have hma : (m : ℝ) * a = Real.pi / 2 := by
    dsimp only [a]
    field_simp [hm'.ne'] <;> ring
  have hphase (t : ℝ) (ht : t ∈ Set.Ioo (-((q : ℝ) * a)) ((q : ℝ) * a)) :
      0 ≤ u * Real.cos t + v * Real.sin t := by
    have hlo : -a < t / (q : ℝ) := (lt_div_iff₀ hq').mpr (by
      simpa only [neg_mul, mul_comm a] using ht.1)
    have hhi : t / (q : ℝ) < a := (div_lt_iff₀ hq').mpr (by
      simpa only [mul_comm a] using ht.2)
    have he := h (t / (q : ℝ)) ⟨hlo, hhi⟩
    simpa only [mul_div_cancel₀ _ hq'.ne'] using he
  obtain ⟨hbound, heq⟩ := phase_sector_bound u v ((q : ℝ) * a) hne hphase
  have hle : (q : ℝ) ≤ (m : ℝ) := (mul_le_mul_right ha).mp (hbound.trans_eq hma.symm)
  refine ⟨by exact_mod_cast hle, ?_⟩
  intro hqm
  apply heq
  rw [hqm]
  exact hma

end MOC
