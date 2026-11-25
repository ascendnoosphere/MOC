import MOC.FourSupportConeClassification
import MOC.RealMatchingSquares
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Positivity

/-! A nonnegative added coefficient preserves the matching-square bound.
The pair factor gives one seven-contact capacity in explicit form. -/

open BigOperators

namespace MOC

private theorem evaluation_smul (a : ℝ) (v : Fin 14 → ℝ) (p : Fin 24) :
    fourMatchingEvaluation (a • v) p = a * fourMatchingEvaluation v p := by
  fin_cases p <;> simp [fourMatchingEvaluation, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem ordinary_mem (r : Fin 34) :
    ordinaryCostRay r ∈ realMatchingFunctionSpace := by
  change ordinaryCostRay r ∈ Set.range
    (fourMatchingEvaluation : (Fin 14 → ℝ) → (Fin 24 → ℝ))
  rw [four_matching_space_eq_ordinary_span]
  exact Submodule.subset_span ⟨r, rfl⟩

private theorem ordinary_sq (r : Fin 34) (p : Fin 24) :
    ordinaryCostRay r p ^ 2 = ordinaryCostRay r p := by
  unfold ordinaryCostRay
  rw [ordinaryCostRayInt_indicator]
  split <;> norm_num

/-- Adding a nonnegative ordinary ray preserves a matching sum of squares. -/
theorem realMatchingSOS_add_ordinaryCostRay {g : Fin 24 → ℝ}
    (h : IsRealMatchingSOS g) (r : Fin 34) (a : ℝ) (ha : 0 ≤ a) :
    IsRealMatchingSOS (fun p => g p + a * ordinaryCostRay r p) := by
  obtain ⟨n, v, hv⟩ := h
  have hmem : ∃ x : Fin 14 → ℝ, fourMatchingEvaluation x = ordinaryCostRay r :=
    ordinary_mem r
  obtain ⟨x, hx⟩ := hmem
  refine ⟨n + 1, Fin.cons (Real.sqrt a • x) v, fun p => ?_⟩
  rw [Fin.sum_univ_succ, hv p]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [evaluation_smul, hx, mul_pow, Real.sq_sqrt ha, ordinary_sq, add_comm]

/-- If an added ray only increases a determinant factor, a nonpositive
factor value implies the base factor is nonpositive. -/
theorem baseFactor_nonpos_of_affine_extension {base slope extra : ℝ}
    (hslope : 0 ≤ slope) (hextra : 0 ≤ extra) (h : base + extra * slope ≤ 0) :
    base ≤ 0 :=
  (le_add_of_nonneg_right (mul_nonneg hextra hslope)).trans h

/-- The normalized mixed determinant factor for the ordinary indices
7, 17, 18, 23, 27, 30, with budgets in that order. -/
def fourSevenContactPairFactor (a b c d e f : ℝ) : ℝ :=
  let u := 1 - c*d
  a*(c+1)*(d+1)*(b*e+b*f+b+e*f+e+f+1) +
    (b+1)*(c+1)*(d+1)*u +
    (b+1)*e*(d+1)*(c^2+c+u) +
    (b+1)*f*(c+1)*(d^2+d+u) +
    e*f*(b*(c-d)^2+c^2+c+d^2+d+u)

/-- A nonpositive seven-contact factor forces a budget product of at least one
on the ordinary rays with indices 18 and 23. -/
theorem fourSevenContactPairFactor_capacity {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hz : fourSevenContactPairFactor a b c d e f ≤ 0) :
    1 ≤ c*d := by
  by_contra! h
  have hu : 0 < 1 - c*d := sub_pos.mpr h
  have hpos : 0 < fourSevenContactPairFactor a b c d e f := by
    unfold fourSevenContactPairFactor
    positivity
  exact hpos.not_ge hz

private def seed : Fin 24 → ℝ := fun p => mixedCostSeedInt p

private theorem mixed_ray_eq (p : Fin 24) : mixedCostRay 0 p = seed p := by
  have h : ∀ p : Fin 24, mixedCostRayInt 0 p = mixedCostSeedInt p := by decide +kernel
  exact_mod_cast h p

private theorem seed_mem : seed ∈ realMatchingFunctionSpace := by
  change seed ∈ Set.range (fourMatchingEvaluation : (Fin 14 → ℝ) → (Fin 24 → ℝ))
  rw [four_matching_space_eq_ordinary_span]
  have he : seed = ordinaryCostRay 10 + ordinaryCostRay 7 + ordinaryCostRay 17 -
      ordinaryCostRay 25 := by
    funext p
    simp [seed, mixedCostSeedInt, ordinaryCostRay, Pi.add_apply, Pi.sub_apply]
  rw [he]
  let W := Submodule.span ℝ (Set.range ordinaryCostRay)
  have hm (r : Fin 34) : ordinaryCostRay r ∈ W := Submodule.subset_span ⟨r, rfl⟩
  exact W.sub_mem (W.add_mem (W.add_mem (hm 10) (hm 7)) (hm 17)) (hm 25)

private theorem pair_correction (p : Fin 24) :
    seed p ^ 2 - seed p = 2 * ordinaryCostRay 18 p * ordinaryCostRay 23 p := by
  have h : ∀ p : Fin 24, mixedCostSeedInt p ^ 2 - mixedCostSeedInt p =
      2 * ordinaryCostRayInt 18 p * ordinaryCostRayInt 23 p := by decide +kernel
  unfold seed ordinaryCostRay
  exact_mod_cast h p

/-- The two compensated rays yield an explicit matching sum of squares. -/
theorem realMatchingSOS_of_pair_capacity {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcap : 1 ≤ c*d) :
    IsRealMatchingSOS (fun p => mixedCostRay 0 p + c * ordinaryCostRay 18 p +
      d * ordinaryCostRay 23 p) := by
  have hc' : 0 < c := by
    by_contra! hn
    have hz : c = 0 := le_antisymm hn hc
    simp [hz] at hcap
  have hd' : 0 ≤ d - c⁻¹ := by
    apply sub_nonneg.mpr
    rw [← one_div]
    exact (div_le_iff₀ hc').2 (by simpa [mul_comm] using hcap)
  let w : Fin 3 → ℝ := ![1, c, d - c⁻¹]
  let f : Fin 3 → Fin 24 → ℝ :=
    ![seed, ordinaryCostRay 18 - c⁻¹ • ordinaryCostRay 23, ordinaryCostRay 23]
  have hw (i : Fin 3) : 0 ≤ w i := by
    fin_cases i <;> simp [w, hc, hd']
  have hf (i : Fin 3) : f i ∈ realMatchingFunctionSpace := by
    fin_cases i
    · exact seed_mem
    · exact realMatchingFunctionSpace.sub_mem (ordinary_mem 18)
        (realMatchingFunctionSpace.smul_mem _ (ordinary_mem 23))
    · exact ordinary_mem 23
  have hcoords (i : Fin 3) : ∃ x : Fin 14 → ℝ, fourMatchingEvaluation x = f i := hf i
  choose v hv using hcoords
  refine ⟨3, fun i => Real.sqrt (w i) • v i, fun p => ?_⟩
  have hs (i : Fin 3) : fourMatchingEvaluation (Real.sqrt (w i) • v i) p ^ 2 =
      w i * f i p ^ 2 := by
    rw [evaluation_smul, hv, mul_pow, Real.sq_sqrt (hw i)]
  simp_rw [hs]
  simp [Fin.sum_univ_three, w, f, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mixed_ray_eq]
  have hi : c * c⁻¹ = 1 := mul_inv_cancel₀ hc'.ne'
  have hi2 : c * (c⁻¹)^2 = c⁻¹ := by
    rw [pow_two, ← mul_assoc, hi, one_mul]
  calc
    _ = seed p ^ 2 + c * ordinaryCostRay 18 p ^ 2 +
        d * ordinaryCostRay 23 p ^ 2 - 2 * ordinaryCostRay 18 p * ordinaryCostRay 23 p := by
      rw [ordinary_sq, ordinary_sq]
      linarith only [pair_correction p]
    _ = _ := by
      have hcancel :
          c * (ordinaryCostRay 18 p - c⁻¹ * ordinaryCostRay 23 p)^2 =
            c * ordinaryCostRay 18 p ^ 2 -
              2 * (c*c⁻¹) * ordinaryCostRay 18 p * ordinaryCostRay 23 p +
              (c*(c⁻¹)^2) * ordinaryCostRay 23 p ^ 2 := by ring
      rw [hcancel, hi, hi2]
      ring

end MOC
