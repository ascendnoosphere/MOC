import MOC.FourSupportConeClassification
import MOC.FourKleinMatchingChart
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! A matching square certificate for ordinary rays that share ray 23. -/

open BigOperators

namespace MOC

noncomputable section

private def mixedSeed (p : Fin 24) : ℝ := mixedCostSeedInt p

private def pointFive (p : Fin 24) : ℤ := if p = 5 then 1 else 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem ordinary_square (r : Fin 34) (p : Fin 24) :
    ordinaryCostRay r p ^ 2 = ordinaryCostRay r p := by
  have h : ∀ i : Fin 34, ∀ j : Fin 24,
      ordinaryCostRayInt i j ^ 2 = ordinaryCostRayInt i j := by decide +kernel
  unfold ordinaryCostRay
  exact_mod_cast h r p

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem sharing_table :
    ∀ p : Fin 24,
      mixedCostSeedInt p ^ 2 - mixedCostSeedInt p = 2 * pointFive p ∧
      ordinaryCostRayInt 23 p * (ordinaryCostRayInt 7 p - ordinaryCostRayInt 31 p) =
        pointFive p ∧
      ordinaryCostRayInt 23 p * (ordinaryCostRayInt 13 p - ordinaryCostRayInt 31 p) =
        pointFive p ∧
      ordinaryCostRayInt 23 p * ordinaryCostRayInt 18 p = pointFive p ∧
      ordinaryCostRayInt 23 p * ordinaryCostRayInt 28 p = pointFive p := by
  decide +kernel

private theorem ordinary_mem (r : Fin 34) :
    ordinaryCostRay r ∈ realMatchingFunctionSpace := by
  change ordinaryCostRay r ∈ Set.range (fourMatchingEvaluation : (Fin 14 → ℝ) → (Fin 24 → ℝ))
  rw [four_matching_space_eq_ordinary_span]
  exact Submodule.subset_span ⟨r, rfl⟩

private theorem mixed_mem : mixedSeed ∈ realMatchingFunctionSpace := by
  have heq : mixedSeed =
      ordinaryCostRay 10 + ordinaryCostRay 7 + ordinaryCostRay 17 - ordinaryCostRay 25 := by
    funext p
    simp only [mixedSeed, mixedCostSeedInt, ordinaryCostRay, Pi.add_apply, Pi.sub_apply,
      Int.cast_add, Int.cast_sub]
  rw [heq]
  exact realMatchingFunctionSpace.sub_mem
    (realMatchingFunctionSpace.add_mem
      (realMatchingFunctionSpace.add_mem (ordinary_mem 10) (ordinary_mem 7))
      (ordinary_mem 17))
    (ordinary_mem 25)

private theorem weighted_squares {n : ℕ} (w : Fin n → ℝ) (f : Fin n → Fin 24 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, f i ∈ realMatchingFunctionSpace) :
    IsRealMatchingSOS (fun p => ∑ i, w i * f i p ^ 2) := by
  have hx (i : Fin n) : ∃ x : Fin 14 → ℝ, kleinMatchingEvaluationLinear x = f i := hf i
  choose x he using hx
  refine ⟨n, fun i => Real.sqrt (w i) • x i, fun p => ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  have hi : (kleinMatchingEvaluationLinear (Real.sqrt (w i) • x i)) p =
      Real.sqrt (w i) * f i p := by
    rw [map_smul, he i, Pi.smul_apply, smul_eq_mul]
  change w i * f i p ^ 2 = (kleinMatchingEvaluationLinear (Real.sqrt (w i) • x i) p) ^ 2
  rw [hi, mul_pow, Real.sq_sqrt (hw i)]

/-- Let `a,b,c,d,e` be the coefficients of ordinary rays 7, 13, 31, 18,
and 28. The combined capacity suffices for a sum of matching squares when
the coefficient `v` of ray 23 is at least its reciprocal. -/
theorem fourSharedRecipient_matching_sos (a b c d e v : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hab : 0 < a + b)
    (hv : 1 / ((a + b) * c / (a + b + c) + d + e) ≤ v) :
    IsRealMatchingSOS (fun p =>
      (mixedCostSeedInt p : ℝ) + a * ordinaryCostRay 7 p + b * ordinaryCostRay 13 p +
        c * ordinaryCostRay 31 p + d * ordinaryCostRay 18 p + e * ordinaryCostRay 28 p +
        v * ordinaryCostRay 23 p) := by
  let k := (a + b) * c / (a + b + c)
  let u := k + d + e
  have hsum : 0 < a + b + c := add_pos hab hc
  have hk : 0 < k := div_pos (mul_pos hab hc) hsum
  have hu : 0 < u := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hk hd) he
  let q := c / ((a + b + c) * u)
  let t := (a + b) / ((a + b + c) * u)
  let z := 1 / u
  have hsplit : q + t = z := by
    dsimp only [q, t, z]
    field_simp [hsum.ne', hu.ne'] <;> ring
  have hbalance : a * q + b * q = c * t := by
    dsimp only [q, t]
    ring
  have htotal : a * q + b * q + d * z + e * z = 1 := by
    calc
      a * q + b * q + d * z + e * z = (k + d + e) / u := by
        dsimp only [q, z, k]
        field_simp [hsum.ne', hu.ne'] <;> ring
      _ = 1 := div_self hu.ne'
  have hweight : a * q ^ 2 + b * q ^ 2 + c * t ^ 2 + d * z ^ 2 + e * z ^ 2 = z := by
    calc
      _ = (a * q + b * q) * q + (c * t) * t + (d * z + e * z) * z := by ring
      _ = z := by
        rw [← hbalance]
        linear_combination (a * q + b * q) * hsplit + z * htotal
  let r := ordinaryCostRay
  let w : Fin 7 → ℝ := ![1, a, b, c, d, e, v - z]
  let f : Fin 7 → Fin 24 → ℝ :=
    ![mixedSeed, r 7 - q • r 23, r 13 - q • r 23, r 31 + t • r 23,
      r 18 - z • r 23, r 28 - z • r 23, r 23]
  have hw (i : Fin 7) : 0 ≤ w i := by
    fin_cases i
    · exact zero_le_one
    · exact ha
    · exact hb
    · exact hc.le
    · exact hd
    · exact he
    · exact sub_nonneg.mpr hv
  have hmem (i : Fin 7) : f i ∈ realMatchingFunctionSpace := by
    let V := realMatchingFunctionSpace
    fin_cases i
    · exact mixed_mem
    · exact V.sub_mem (ordinary_mem 7) (V.smul_mem q (ordinary_mem 23))
    · exact V.sub_mem (ordinary_mem 13) (V.smul_mem q (ordinary_mem 23))
    · exact V.add_mem (ordinary_mem 31) (V.smul_mem t (ordinary_mem 23))
    · exact V.sub_mem (ordinary_mem 18) (V.smul_mem z (ordinary_mem 23))
    · exact V.sub_mem (ordinary_mem 28) (V.smul_mem z (ordinary_mem 23))
    · exact ordinary_mem 23
  have hid (p : Fin 24) :
      mixedSeed p + a * r 7 p + b * r 13 p + c * r 31 p + d * r 18 p + e * r 28 p +
        v * r 23 p = ∑ i, w i * f i p ^ 2 := by
    let δ : ℝ := pointFive p
    have hm : mixedSeed p ^ 2 - mixedSeed p = 2 * δ := by
      dsimp only [mixedSeed, δ]
      exact_mod_cast (sharing_table p).1
    have h7 : r 23 p * (r 7 p - r 31 p) = δ := by
      dsimp only [r, ordinaryCostRay, δ]
      exact_mod_cast (sharing_table p).2.1
    have h13 : r 23 p * (r 13 p - r 31 p) = δ := by
      dsimp only [r, ordinaryCostRay, δ]
      exact_mod_cast (sharing_table p).2.2.1
    have h18 : r 23 p * r 18 p = δ := by
      dsimp only [r, ordinaryCostRay, δ]
      exact_mod_cast (sharing_table p).2.2.2.1
    have h28 : r 23 p * r 28 p = δ := by
      dsimp only [r, ordinaryCostRay, δ]
      exact_mod_cast (sharing_table p).2.2.2.2
    have hcross :
        r 23 p * (a * q * r 7 p + b * q * r 13 p - c * t * r 31 p +
          d * z * r 18 p + e * z * r 28 p) = δ := by
      rw [← hbalance]
      linear_combination a * q * h7 + b * q * h13 + d * z * h18 + e * z * h28 +
        δ * htotal
    simp [w, f, Fin.sum_univ_succ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -hm - a * ordinary_square 7 p - b * ordinary_square 13 p -
      c * ordinary_square 31 p - d * ordinary_square 18 p - e * ordinary_square 28 p -
      v * ordinary_square 23 p - (r 23 p) ^ 2 * hweight + 2 * hcross
  change IsRealMatchingSOS (fun p =>
    mixedSeed p + a * r 7 p + b * r 13 p + c * r 31 p + d * r 18 p + e * r 28 p + v * r 23 p)
  rw [funext hid]
  exact weighted_squares w f hw hmem

end

end MOC
