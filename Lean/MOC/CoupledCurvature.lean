import MOC.SpectralStationarity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Mixed curvature of a finite support envelope along an orbit direction. -/

open BigOperators Filter
open scoped Topology

namespace MOC

/-- At a local maximum of a finite minimum, any second-order comparison
along a common tangent gives a nonpositive coefficient on an active branch. -/
theorem exists_active_nonpositive_curvature {J : Type*} [Finite J]
    (f : J → ℝ → ℝ) (q : J → ℝ) (g : ℝ)
    (hbase : ∀ j, g ≤ f j 0) (hcont : ∀ j, ContinuousAt (f j) 0)
    (hlimit : ∀ j, f j 0 = g →
      Tendsto (fun t => (f j t - g) / t ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (q j)))
    (hmax : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∃ j, f j t ≤ g) :
    ∃ j, f j 0 = g ∧ q j ≤ 0 := by
  by_contra hnone
  have hstrict (j : J) : ∀ᶠ t in 𝓝[≠] (0 : ℝ), g < f j t := by
    by_cases hj : f j 0 = g
    · have hq : 0 < q j := lt_of_not_ge fun h => hnone ⟨j, hj, h⟩
      filter_upwards [hlimit j hj (Ioi_mem_nhds hq), self_mem_nhdsWithin] with t ht ht0
      change t ≠ 0 at ht0
      change 0 < (f j t - g) / t ^ 2 at ht
      exact sub_pos.mp ((div_pos_iff_of_pos_right (sq_pos_of_ne_zero ht0)).mp ht)
    · have hp : g < f j 0 := lt_of_le_of_ne (hbase j) (fun he => hj he.symm)
      exact ((hcont j).eventually_mem (Ioi_mem_nhds hp)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, j, hj⟩ := ((Filter.eventually_all.mpr hstrict).and hmax).exists
  exact (not_lt_of_ge hj) (ht j)

/-- Eliminating a strictly concave orbit direction adds the square of the mixed
coefficient divided by the magnitude of the orbit curvature. -/
theorem exists_curvature_le_after_orbit_variation {J : Type*}
    (q : J → ℝ) (b h : ℝ) (hh : h < 0)
    (hbound : ∀ s : ℝ, ∃ j, q j + 2 * s * b + s ^ 2 * h ≤ 0) :
    ∃ j, q j + b ^ 2 / (-h) ≤ 0 := by
  obtain ⟨j, hj⟩ := hbound (b / (-h))
  have he : 2 * (b / (-h)) * b + (b / (-h)) ^ 2 * h = b ^ 2 / (-h) := by
    field_simp [hh.ne] <;> ring
  exact ⟨j, by simpa only [add_assoc, he] using hj⟩

private theorem mixed_eq_zero_of_null_curvature {J : Type*} [Fintype J]
    (q : J → ℝ) (b : ℝ)
    (hbound : ∀ s : ℝ, ∃ j, q j + 2 * s * b ≤ 0) : b = 0 := by
  classical
  obtain ⟨i, _⟩ := hbound 0
  obtain ⟨j, _, hmin⟩ := Finset.exists_min_image Finset.univ q ⟨i, Finset.mem_univ i⟩
  by_contra hb
  obtain ⟨k, hk⟩ := hbound ((1 - q j) / (2 * b))
  have he : 2 * ((1 - q j) / (2 * b)) * b = 1 - q j := by
    field_simp [hb] <;> ring
  rw [he] at hk
  linarith only [hk, hmin k (Finset.mem_univ k)]

/-- At a null orbit mode, the mixed derivative on the spectral and support
direction tangent space lies in the span of the active gradient differences. -/
theorem mixed_covector_mem_active_difference_span
    {V J : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [Fintype J]
    (L : J → Module.Dual ℝ V) (b : Module.Dual ℝ V) (j₀ : J)
    (w : J → ℝ) (hw : ∑ j, w j = 1) (hstationary : ∑ j, w j • L j = 0)
    (q : J → V → ℝ)
    (hbound : ∀ v, (∀ j, L j v = 0) → ∀ s : ℝ, ∃ j, q j v + 2 * s * b v ≤ 0) :
    b ∈ Submodule.span ℝ (Set.range fun j => L j - L j₀) := by
  let W : Submodule ℝ (Module.Dual ℝ V) := Submodule.span ℝ (Set.range fun j => L j - L j₀)
  change b ∈ W
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), Submodule.mem_dualAnnihilator]
  intro v hv
  have hv' : ∀ φ ∈ Set.range (fun j => L j - L j₀), φ v = 0 := by
    change v ∈ (W.dualCoannihilator : Set V) at hv
    simpa only [W, Submodule.coe_dualCoannihilator_span, Set.mem_setOf_eq] using hv
  have hconstant (j : J) : L j v = L j₀ v := by
    have h := hv' (L j - L j₀) ⟨j, rfl⟩
    exact sub_eq_zero.mp (by simpa only [LinearMap.sub_apply] using h)
  have hzero : L j₀ v = 0 := by
    have h := congrArg (fun φ : Module.Dual ℝ V => φ v) hstationary
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
      hconstant, ← Finset.sum_mul, hw, one_mul] at h
    exact h
  exact mixed_eq_zero_of_null_curvature (fun j => q j v) (b v)
    (hbound v fun j => (hconstant j).trans hzero)

/-- Four quadratic branches with a strictly concave orbit variable and a
nonzero mixed derivative. -/
noncomputable def coupledQuadraticContact (j : Bool × Bool) (x y u : ℝ) : ℝ :=
  let d := if j.1 then x ^ 2 - y ^ 2 else 2 * x * y
  1 - (u - 2 * x) ^ 2 + (x ^ 2 + y ^ 2) / 2 + if j.2 then d else -d

/-- The smallest branch has a global maximum of one at the origin. -/
theorem coupledQuadraticContact_min_le (x y u : ℝ) :
    ∃ j, coupledQuadraticContact j x y u ≤ 1 := by
  by_contra! hn
  let d := x ^ 2 - y ^ 2
  let e := 2 * x * y
  let s := x ^ 2 + y ^ 2
  have hD₁ : 0 < s / 2 + d := by
    have h := hn (true, true)
    simp [coupledQuadraticContact] at h
    dsimp only [s, d]
    linarith only [h, sq_nonneg (u - 2 * x)]
  have hD₂ : 0 < s / 2 - d := by
    have h := hn (true, false)
    simp [coupledQuadraticContact] at h
    dsimp only [s, d]
    linarith only [h, sq_nonneg (u - 2 * x)]
  have hE₁ : 0 < s / 2 + e := by
    have h := hn (false, true)
    simp [coupledQuadraticContact] at h
    dsimp only [s, e]
    linarith only [h, sq_nonneg (u - 2 * x)]
  have hE₂ : 0 < s / 2 - e := by
    have h := hn (false, false)
    simp [coupledQuadraticContact] at h
    dsimp only [s, e]
    linarith only [h, sq_nonneg (u - 2 * x)]
  have hD : |d| < s / 2 := abs_lt.mpr ⟨by linarith only [hD₁], by linarith only [hD₂]⟩
  have hE : |e| < s / 2 := abs_lt.mpr ⟨by linarith only [hE₁], by linarith only [hE₂]⟩
  have hs : 0 ≤ s / 2 := (abs_nonneg d).trans hD.le
  have hDD : d ^ 2 < (s / 2) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg d) hs).mpr hD
  have hEE : e ^ 2 < (s / 2) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg e) hs).mpr hE
  have hid : d ^ 2 + e ^ 2 = s ^ 2 := by dsimp only [d, e, s]; ring
  have hsum : (s / 2) ^ 2 + (s / 2) ^ 2 ≤ s ^ 2 := by
    calc
      _ = s ^ 2 / 2 := by ring
      _ ≤ _ := half_le_self_iff.mpr (sq_nonneg s)
  exact (ne_of_lt ((add_lt_add hDD hEE).trans_le hsum)) hid

theorem coupledQuadraticContact_orbit_axis (j : Bool × Bool) (u : ℝ) :
    coupledQuadraticContact j 0 0 u = 1 - u ^ 2 := by
  rcases j with ⟨j, k⟩
  cases j <;> cases k <;> norm_num [coupledQuadraticContact]

theorem coupledQuadraticContact_mixed (j : Bool × Bool) (x y u : ℝ) :
    coupledQuadraticContact j x y u - coupledQuadraticContact j x y 0 -
      (coupledQuadraticContact j 0 0 u - 1) = 4 * x * u := by
  rw [coupledQuadraticContact_orbit_axis]
  unfold coupledQuadraticContact
  ring

/-- Every fixed law has a positive quadratic direction after the orbit variable
is optimized. The conclusion holds even for signed weights totaling one. -/
theorem coupledQuadraticContact_no_common_curvature_weights (w : Bool × Bool → ℝ)
    (hw : ∑ j, w j = 1) :
    ∃ x y : ℝ, 1 < ∑ j, w j * coupledQuadraticContact j x y (2 * x) := by
  by_contra! hn
  have htrace (j : Bool × Bool) :
      coupledQuadraticContact j 1 0 (2 * 1) + coupledQuadraticContact j 0 1 (2 * 0) = 3 := by
    rcases j with ⟨j, k⟩
    cases j <;> cases k <;> norm_num [coupledQuadraticContact]
  have he :
      (∑ j, w j * coupledQuadraticContact j 1 0 (2 * 1)) +
        (∑ j, w j * coupledQuadraticContact j 0 1 (2 * 0)) = 3 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add, htrace, ← Finset.sum_mul, hw, one_mul]
  linarith only [he, hn 1 0, hn 0 1]

end MOC
