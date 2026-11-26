import MOC.Support
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators

namespace MOC

noncomputable section

/-- An indexed finite hull is exactly the set of means of probability weights. -/
theorem mem_complex_convexHull_iff_finite_probability {J : Type*} [Fintype J]
    (v : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range v) ↔ ∃ w : J → ℝ, (∀ j, 0 ≤ w j) ∧
      (∑ j, w j) = 1 ∧ (∑ j, w j • v j) = z := by
  classical
  constructor
  · intro hz
    rw [convexHull_range_eq_exists_affineCombination, Set.mem_setOf_eq] at hz
    obtain ⟨s, w, hw, hs, hsum⟩ := hz
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hsum
    let w' (i : J) := if i ∈ s then w i else 0
    refine ⟨w', fun i => by by_cases hi : i ∈ s <;> simp [w', hi, hw], ?_, ?_⟩
    · simpa only [w', Fintype.sum_ite_mem] using hs
    · simpa only [w', ite_smul, zero_smul, Fintype.sum_ite_mem] using hsum
  · rintro ⟨w, hw, hs, hsum⟩
    exact mem_convexHull_of_exists_fintype w v hw hs (fun j => Set.mem_range_self j) hsum

/-- The centered log-sum-exp of finitely many complex vertices in a real direction. -/
def spectralLogSumExp {J : Type*} [Fintype J]
    (v : J → ℂ) (z : ℂ) (L : ℂ →L[ℝ] ℝ) : ℝ :=
  Real.log (∑ j, Real.exp (L (v j - z)))

/-- A point of the finite hull has nonnegative centered log-sum-exp in every direction. -/
theorem spectralLogSumExp_nonneg {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (hz : z ∈ convexHull ℝ (Set.range v))
    (L : ℂ →L[ℝ] ℝ) : 0 ≤ spectralLogSumExp v z L := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j => L (v j))
    (Finset.univ_nonempty : (Finset.univ : Finset J).Nonempty)
  have hle : L z ≤ L (v j) := by
    apply convexHull_min _ (convex_halfSpace_le L.isLinear _) hz
    rintro _ ⟨i, rfl⟩
    exact hj i (Finset.mem_univ i)
  have he : 1 ≤ Real.exp (L (v j - z)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by rw [map_sub]; exact sub_nonneg.mpr hle)
  have hs : Real.exp (L (v j - z)) ≤ ∑ i, Real.exp (L (v i - z)) :=
    Finset.single_le_sum (fun i _ => (Real.exp_pos (L (v i - z))).le) (Finset.mem_univ j)
  exact Real.log_nonneg (he.trans hs)

/-- Separation gives a linear upper bound tending to negative infinity along a ray. -/
theorem spectralLogSumExp_le_of_not_mem {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) (hz : z ∉ convexHull ℝ (Set.range v)) :
    ∃ (L : ℂ →L[ℝ] ℝ) (ε : ℝ), 0 < ε ∧
      ∀ r : ℝ, 0 ≤ r →
        spectralLogSumExp v z (r • L) ≤ Real.log (Fintype.card J : ℝ) - r * ε := by
  classical
  obtain ⟨L, y, hv, hzy⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (Set.range v)) (Set.finite_range v).isClosed_convexHull hz
  have hε : 0 < L z - y := sub_pos.mpr hzy
  refine ⟨L, L z - y, hε, ?_⟩
  intro r hr
  have hvertex (j : J) : L (v j) ≤ y :=
    (hv (v j) (subset_convexHull ℝ _ ⟨j, rfl⟩)).le
  have hterm (j : J) : Real.exp ((r • L) (v j - z)) ≤ Real.exp (-r * (L z - y)) := by
    apply Real.exp_le_exp.mpr
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub, neg_mul]
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right (hvertex j) (L z)) hr).trans_eq
      (by ring)
  have hpos : 0 < ∑ j, Real.exp ((r • L) (v j - z)) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hsum : (∑ j, Real.exp ((r • L) (v j - z))) ≤
      (Fintype.card J : ℝ) * Real.exp (-r * (L z - y)) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j))
  have hcard : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold spectralLogSumExp
  calc
    _ ≤ Real.log ((Fintype.card J : ℝ) * Real.exp (-r * (L z - y))) :=
      Real.log_le_log hpos hsum
    _ = _ := by rw [Real.log_mul hcard (Real.exp_ne_zero _), Real.log_exp]; ring

/-- Membership, nonnegative log-sum-exp, and boundedness below are equivalent. -/
theorem mem_convexHull_iff_spectralLogSumExp {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range v) ↔ ∀ L : ℂ →L[ℝ] ℝ, 0 ≤ spectralLogSumExp v z L := by
  constructor
  · intro hz L
    exact spectralLogSumExp_nonneg v z hz L
  · intro h
    by_contra hn
    obtain ⟨L, ε, hε, hbound⟩ := spectralLogSumExp_le_of_not_mem v z hn
    let c := Real.log (Fintype.card J : ℝ)
    let r := (|c| + 1) / ε
    have hr : 0 ≤ r := div_nonneg (by positivity) hε.le
    have he : r * ε = |c| + 1 := div_mul_cancel₀ _ hε.ne'
    have hh : spectralLogSumExp v z (r • L) ≤ c - r * ε := hbound r hr
    rw [he] at hh
    linarith only [h (r • L), hh, le_abs_self c]

theorem mem_convexHull_iff_bddBelow_spectralLogSumExp {J : Type*} [Fintype J] [Nonempty J]
    (v : J → ℂ) (z : ℂ) :
    z ∈ convexHull ℝ (Set.range v) ↔ BddBelow (Set.range (spectralLogSumExp v z)) := by
  constructor
  · intro hz
    refine ⟨0, ?_⟩
    rintro _ ⟨L, rfl⟩
    exact spectralLogSumExp_nonneg v z hz L
  · rintro ⟨b, hb⟩
    by_contra hn
    obtain ⟨L, ε, hε, hbound⟩ := spectralLogSumExp_le_of_not_mem v z hn
    let c := Real.log (Fintype.card J : ℝ)
    let r := (|c - b| + 1) / ε
    have hr : 0 ≤ r := div_nonneg (by positivity) hε.le
    have he : r * ε = |c - b| + 1 := div_mul_cancel₀ _ hε.ne'
    have hlow : b ≤ spectralLogSumExp v z (r • L) := hb ⟨r • L, rfl⟩
    have hhigh : spectralLogSumExp v z (r • L) ≤ c - r * ε := hbound r hr
    rw [he] at hhigh
    linarith only [hlow, hhigh, le_abs_self (c - b)]

end

end MOC
