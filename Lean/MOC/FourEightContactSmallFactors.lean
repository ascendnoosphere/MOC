import MOC.FourSupportConeClassification
import MOC.RealMatchingSquares
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Nonlinear capacity certificates for two order-four eight-contact families.
The factor signs are hypotheses. The proofs express the support gap
through nonnegative mixed weights and squared minor terms. -/

open BigOperators

namespace MOC
namespace FourEightContactSmallFactors

noncomputable section

/-- The mixed-sign determinant factor for ordinary rays 13, 17, 18, 27, and 30. -/
def firstFactor (a b c d e : ℝ) : ℝ :=
  (a + 1) * (c + 1) * (e + 1) * (a + b + 1) -
    d * ((a * c - 1) * ((e + 1) * (a + 1)) -
      (((e + 1) * (a + 1)) * c * (c + 1) +
        b * ((e + 1) * (a - c)^2 + (a + 1) * (c + 1))))

/-- The mixed-sign determinant factor for ordinary rays 7, 13, 20, 27, and 31. -/
def secondFactor (a b c d e : ℝ) : ℝ :=
  ((a + 1) * (b + 1)) * (a + c + 1) * (b + d + 1) -
    e * ((a * b - 1) * ((a + 1) * (b + 1) + b * c + a * d) -
      (c * (a^2 * b + a^2 + a + 1) + d * (a * b^2 + b^2 + b + 1) +
        c * d * (a - b)^2))

private theorem positive_factors_of_bound {v p h k r : ℝ}
    (hv : 0 ≤ v) (hh : 0 < h) (hk : 0 ≤ k) (hr : 0 < r)
    (hbound : r ≤ v * (p * h - k)) :
    0 < v ∧ 0 < p ∧ 0 < p * h - k := by
  have hproduct : 0 < v * (p * h - k) := lt_of_lt_of_le hr hbound
  have hv' : 0 < v := lt_of_le_of_ne hv (fun he => by
    rw [← he, zero_mul] at hproduct
    exact (lt_irrefl (0 : ℝ)) hproduct)
  have hs : 0 < p * h - k := by
    by_contra! hn
    exact (not_le_of_gt hproduct) (mul_nonpos_of_nonneg_of_nonpos hv hn)
  have hp : 0 < p := by
    by_contra! hn
    have hph := mul_nonpos_of_nonpos_of_nonneg hn hh.le
    linarith only [hs, hk, hph]
  exact ⟨hv', hp, hs⟩

/-- A nonpositive first factor forces the capacity for its square decomposition. -/
theorem first_capacity {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hz : firstFactor a b c d e ≤ 0) :
    0 < a * c - 1 ∧ 0 < d ∧ a ≤ d * (a * c - 1) := by
  let p := a * c - 1
  let h := (e + 1) * (a + 1)
  let k := h * c * (c + 1) + b * ((e + 1) * (a - c)^2 + (a + 1) * (c + 1))
  let r := (a + 1) * (c + 1) * (e + 1) * (a + b + 1)
  have hh : 0 < h := by dsimp [h]; positivity
  have hk : 0 ≤ k := by dsimp [k, h]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hn : r - d * (p * h - k) ≤ 0 := hz
  have hbound : r ≤ d * (p * h - k) := sub_nonpos.mp hn
  obtain ⟨hd', hp, hs⟩ := positive_factors_of_bound hd hh hk hr hbound
  have hrem : r - a * h = (a + 1) * (e + 1) * (a * c + b * c + b + c + 1) := by
    dsimp [r, h]
    ring
  have hrem' : 0 ≤ r - a * h := by rw [hrem]; positivity
  have hnum : 0 ≤ (p * h - k) * (d * p - a) := calc
    0 ≤ p * (r - a * h) + a * k :=
      add_nonneg (mul_nonneg hp.le hrem') (mul_nonneg ha hk)
    _ ≤ p * (d * (p * h - k) - a * h) + a * k :=
      add_le_add_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hbound _) hp.le) _
    _ = (p * h - k) * (d * p - a) := by ring
  exact ⟨hp, hd', sub_nonneg.mp (nonneg_of_mul_nonneg_right hnum hs)⟩

/-- A nonpositive second factor forces the four-feature Gram capacity. -/
theorem second_capacity {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hz : secondFactor a b c d e ≤ 0) :
    0 < a * b - 1 ∧ (a + 1) * (b + 1) ≤ e * (a * b - 1) := by
  let p := a * b - 1
  let s := (a + 1) * (b + 1)
  let h := s + b * c + a * d
  let k := c * (a^2 * b + a^2 + a + 1) + d * (a * b^2 + b^2 + b + 1) +
    c * d * (a - b)^2
  let r := s * (a + c + 1) * (b + d + 1)
  have hh : 0 < h := by dsimp [h, s]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hr : 0 < r := by dsimp [r, s]; positivity
  have hn : r - e * (p * h - k) ≤ 0 := hz
  have hbound : r ≤ e * (p * h - k) := sub_nonpos.mp hn
  obtain ⟨_, hp, hs⟩ := positive_factors_of_bound he hh hk hr hbound
  have hrem : p * r - s * (p * h - k) =
      s * (s * (a * c + b * d) + c * d * ((a - b)^2 + p)) := by
    dsimp [r, s, p, h, k]
    ring
  have hnum : 0 ≤ (p * h - k) * (e * p - s) := calc
    0 ≤ s * (s * (a * c + b * d) + c * d * ((a - b)^2 + p)) := by
      dsimp [s]
      positivity
    _ = p * r - s * (p * h - k) := hrem.symm
    _ ≤ p * (e * (p * h - k)) - s * (p * h - k) :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left hbound hp.le) _
    _ = (p * h - k) * (e * p - s) := by ring
  exact ⟨hp, sub_nonneg.mp (nonneg_of_mul_nonneg_right hnum hs)⟩

private abbrev ray (i : Fin 34) := ordinaryCostRay i

private def mixed : Fin 24 → ℝ := fun p => (mixedCostSeedInt p : ℝ)

private theorem mixed_ray_eq (p : Fin 24) : mixedCostRay 0 p = mixed p := by
  have h : ∀ p : Fin 24, mixedCostRayInt 0 p = mixedCostSeedInt p := by decide +kernel
  exact congrArg (fun x : ℤ => (x : ℝ)) (h p)

private theorem ray_mem (i : Fin 34) : ray i ∈ realMatchingFunctionSpace := by
  change ordinaryCostRay i ∈ Set.range
    (fourMatchingEvaluation : (Fin 14 → ℝ) → (Fin 24 → ℝ))
  rw [four_matching_space_eq_ordinary_span]
  exact Submodule.subset_span ⟨i, rfl⟩

private theorem mixed_mem : mixed ∈ realMatchingFunctionSpace := by
  have heq : mixed = ray 10 + ray 7 + ray 17 - ray 25 := by
    funext p
    simp [mixed, mixedCostSeedInt, ray, ordinaryCostRay, Pi.add_apply, Pi.sub_apply]
  rw [heq]
  exact realMatchingFunctionSpace.sub_mem (realMatchingFunctionSpace.add_mem
    (realMatchingFunctionSpace.add_mem (ray_mem 10) (ray_mem 7)) (ray_mem 17)) (ray_mem 25)

private theorem ray_sq (i : Fin 34) (p : Fin 24) : ray i p ^ 2 = ray i p := by
  have h : ∀ i : Fin 34, ∀ p : Fin 24,
      ordinaryCostRayInt i p ^ 2 = ordinaryCostRayInt i p := by decide +kernel
  change (ordinaryCostRayInt i p : ℝ)^2 = (ordinaryCostRayInt i p : ℝ)
  exact_mod_cast h i p

private theorem weighted_squares {n : ℕ} (w : Fin n → ℝ) (f : Fin n → Fin 24 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, f i ∈ realMatchingFunctionSpace) :
    IsRealMatchingSOS (fun p => ∑ i, w i * f i p ^ 2) := by
  have hx (i : Fin n) : ∃ x : Fin 14 → ℝ, fourMatchingEvaluation x = f i := hf i
  choose x hxe using hx
  refine ⟨n, fun i => Real.sqrt (w i) • x i, fun p => ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  have he : fourMatchingEvaluation (Real.sqrt (w i) • x i) p =
      Real.sqrt (w i) * fourMatchingEvaluation (x i) p := by
    fin_cases p <;> simp [fourMatchingEvaluation, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [he, hxe i, mul_pow, Real.sq_sqrt (hw i)]

private theorem first_cross (p : Fin 24) :
    mixed p^2 - mixed p = 2 * (ray 13 p * ray 18 p - ray 18 p * ray 27 p) := by
  have h : ∀ p : Fin 24, mixedCostSeedInt p ^ 2 - mixedCostSeedInt p =
      2 * (ordinaryCostRayInt 13 p * ordinaryCostRayInt 18 p -
        ordinaryCostRayInt 18 p * ordinaryCostRayInt 27 p) := by decide +kernel
  unfold mixed ray ordinaryCostRay
  exact_mod_cast h p

private theorem second_cross (p : Fin 24) :
    mixed p^2 - mixed p = 2 * (mixed p * ray 31 p + ray 7 p * ray 13 p -
      ray 7 p * ray 31 p - ray 13 p * ray 31 p) := by
  have h : ∀ p : Fin 24, mixedCostSeedInt p ^ 2 - mixedCostSeedInt p =
      2 * (mixedCostSeedInt p * ordinaryCostRayInt 31 p +
        ordinaryCostRayInt 7 p * ordinaryCostRayInt 13 p -
        ordinaryCostRayInt 7 p * ordinaryCostRayInt 31 p -
        ordinaryCostRayInt 13 p * ordinaryCostRayInt 31 p) := by decide +kernel
  unfold mixed ray ordinaryCostRay
  exact_mod_cast h p

/-- A nonpositive first factor gives a matching sum of squares for nonnegative budgets. -/
theorem first_matching_sos {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hz : firstFactor a b c d e ≤ 0) :
    IsRealMatchingSOS (fun p => mixedCostRay 0 p + a * ordinaryCostRay 13 p +
      b * ordinaryCostRay 17 p + c * ordinaryCostRay 18 p +
        d * ordinaryCostRay 27 p + e * ordinaryCostRay 30 p) := by
  obtain ⟨hp, hd', hcap⟩ := first_capacity ha hb hc hd he hz
  have ha' : 0 < a := lt_of_le_of_ne ha fun h => by
    rw [← h, zero_mul] at hp
    norm_num at hp
  have had : 0 < a * d := mul_pos ha' hd'
  have hweight : 0 ≤ c - 1/a - 1/d := by
    have heq : (c - 1/a - 1/d) * (a*d) = d * (a*c - 1) - a := by
      field_simp [ha'.ne', hd'.ne'] <;> ring
    exact nonneg_of_mul_nonneg_left (heq.symm ▸ sub_nonneg.mpr hcap) had
  let w : Fin 6 → ℝ := ![1, a, d, c - 1/a - 1/d, b, e]
  let f : Fin 6 → Fin 24 → ℝ := ![mixed, ray 13 - a⁻¹ • ray 18, ray 27 + d⁻¹ • ray 18,
    ray 18, ray 17, ray 30]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · norm_num [w]
    · exact ha
    · exact hd
    · exact hweight
    · exact hb
    · exact he
  have hf : ∀ i, f i ∈ realMatchingFunctionSpace := by
    intro i
    fin_cases i
    · exact mixed_mem
    · exact realMatchingFunctionSpace.sub_mem (ray_mem 13) (realMatchingFunctionSpace.smul_mem _ (ray_mem 18))
    · exact realMatchingFunctionSpace.add_mem (ray_mem 27) (realMatchingFunctionSpace.smul_mem _ (ray_mem 18))
    · exact ray_mem 18
    · exact ray_mem 17
    · exact ray_mem 30
  suffices (fun p => mixed p + a * ray 13 p + b * ray 17 p + c * ray 18 p +
      d * ray 27 p + e * ray 30 p) = (fun p => ∑ i, w i * f i p ^ 2) by
    simp only [mixed_ray_eq, this]
    exact weighted_squares w f hw hf
  funext p
  calc
    _ = mixed p^2 + a * ray 13 p^2 + b * ray 17 p^2 + c * ray 18 p^2 +
        d * ray 27 p^2 + e * ray 30 p^2 -
          2 * (ray 13 p * ray 18 p - ray 18 p * ray 27 p) := by
      simp only [ray_sq]
      linarith only [first_cross p]
    _ = _ := by
      simp [w, f, Fin.sum_univ_succ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [ha'.ne', hd'.ne'] <;> ring

/-- A nonpositive second factor gives a matching sum of squares for nonnegative budgets. -/
theorem second_matching_sos {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hz : secondFactor a b c d e ≤ 0) :
    IsRealMatchingSOS (fun p => mixedCostRay 0 p + a * ordinaryCostRay 7 p +
      b * ordinaryCostRay 13 p + c * ordinaryCostRay 20 p +
        d * ordinaryCostRay 27 p + e * ordinaryCostRay 31 p) := by
  obtain ⟨hp, hcap⟩ := second_capacity ha hb hc hd he hz
  have ha' : 0 < a := lt_of_le_of_ne ha fun h => by
    rw [← h, zero_mul] at hp
    norm_num at hp
  have hb' : 0 ≤ b - 1/a := sub_nonneg.mpr ((div_le_iff₀ ha').2 (by
    rw [mul_comm b a]
    linarith only [hp]))
  have he' : 0 ≤ e - (a+1)*(b+1)/(a*b-1) :=
    sub_nonneg.mpr ((div_le_iff₀ hp).2 hcap)
  let w : Fin 6 → ℝ := ![1, a, b - 1/a, e - (a+1)*(b+1)/(a*b-1), c, d]
  let f : Fin 6 → Fin 24 → ℝ := ![mixed - ray 31, ray 7 + a⁻¹ • (ray 31 - ray 13),
    ray 13 + ((a+1)/(a*b-1)) • ray 31, ray 31, ray 20, ray 27]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · norm_num [w]
    · exact ha
    · exact hb'
    · exact he'
    · exact hc
    · exact hd
  have hf : ∀ i, f i ∈ realMatchingFunctionSpace := by
    intro i
    fin_cases i
    · exact realMatchingFunctionSpace.sub_mem mixed_mem (ray_mem 31)
    · exact realMatchingFunctionSpace.add_mem (ray_mem 7) (realMatchingFunctionSpace.smul_mem _
        (realMatchingFunctionSpace.sub_mem (ray_mem 31) (ray_mem 13)))
    · exact realMatchingFunctionSpace.add_mem (ray_mem 13) (realMatchingFunctionSpace.smul_mem _ (ray_mem 31))
    · exact ray_mem 31
    · exact ray_mem 20
    · exact ray_mem 27
  suffices (fun p => mixed p + a * ray 7 p + b * ray 13 p + c * ray 20 p +
      d * ray 27 p + e * ray 31 p) = (fun p => ∑ i, w i * f i p ^ 2) by
    simp only [mixed_ray_eq, this]
    exact weighted_squares w f hw hf
  funext p
  calc
    _ = mixed p^2 + a * ray 7 p^2 + b * ray 13 p^2 + c * ray 20 p^2 +
        d * ray 27 p^2 + e * ray 31 p^2 -
        2 * (mixed p * ray 31 p + ray 7 p * ray 13 p -
          ray 7 p * ray 31 p - ray 13 p * ray 31 p) := by
      simp only [ray_sq]
      linarith only [second_cross p]
    _ = _ := by
      simp [w, f, Fin.sum_univ_succ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [ha'.ne', hp.ne'] <;> ring

end
end FourEightContactSmallFactors
end MOC
