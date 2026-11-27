import MOC.CyclicSwitchEvents
import Mathlib.Data.Rat.BigOperators

/-! Nonnegative switch costs and cancellation of the degree-three Walsh
coefficients do not imply the four-switch capacity bound. -/

open BigOperators

namespace MOC

private def switchCount (x : Fin 4 → Bool) : ℕ :=
  ∑ i, if x i then 1 else 0

private def rationalDeficit (x : Fin 4 → Bool) : ℚ :=
  if switchCount x = 3 then 1 else if switchCount x = 4 then 2 else 0

private def rationalSpin (b : Bool) : ℚ := if b then -1 else 1

private def rationalParity (x : Fin 4 → Bool) : ℚ := ∏ i, rationalSpin (x i)

private def rationalCapacityWeight (x : Fin 4 → Bool) : ℚ :=
  ∏ i, if x i then (1 / 2 : ℚ) else 2

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
private theorem rationalCapacityCertificate :
    (∀ x, 0 ≤ rationalDeficit x) ∧ rationalDeficit (fun _ => false) = 0 ∧
    (∀ i : Fin 4, (∑ x, rationalDeficit x * rationalParity x * rationalSpin (x i)) = 0) ∧
    (∑ x, rationalDeficit x * rationalCapacityWeight x) = 9 / 8 ∧
    (∑ x, rationalDeficit x * rationalParity x) = -2 := by
  decide +kernel

private theorem rationalSpin_cast (b : Bool) :
    (rationalSpin b : ℝ) = switchSign b := by
  cases b <;> norm_num [rationalSpin, switchSign]

private theorem rationalParity_cast (x : Fin 4 → Bool) :
    (rationalParity x : ℝ) = switchParity x := by
  unfold rationalParity switchParity
  rw [Rat.cast_prod]
  simp only [rationalSpin_cast]

private theorem rationalCapacityWeight_cast (x : Fin 4 → Bool) :
    (rationalCapacityWeight x : ℝ) = ∏ i, if x i then (1 / 2 : ℝ) else 2 := by
  unfold rationalCapacityWeight
  rw [Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases h : x i <;> norm_num [h]

/-- An abstract deficit on four switches satisfies all degree-three
cancellations. Its capacity evaluation at probability ratio four is `9/8`,
and its top Walsh sum is `-2`. The deficit is one at each word with three
true entries and two at the word with four true entries. -/
theorem cyclic_support_capacity_walsh_obstruction :
    ∃ δ : (Fin 4 → Bool) → ℝ,
      (∀ x, 0 ≤ δ x) ∧ δ (fun _ => false) = 0 ∧
      (∀ i : Fin 4, (∑ x, δ x * switchParity x * switchSign (x i)) = 0) ∧
      (∑ x, δ x * (∏ i, if x i then (1 / 2 : ℝ) else 2)) = 9 / 8 ∧
      (∑ x, δ x * switchParity x) = -2 := by
  obtain ⟨hnonneg, hzero, hcancel, hcapacity, hparity⟩ := rationalCapacityCertificate
  refine ⟨fun x => (rationalDeficit x : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change (0 : ℝ) ≤ (rationalDeficit x : ℝ)
    exact_mod_cast hnonneg x
  · change (rationalDeficit (fun _ => false) : ℝ) = 0
    exact_mod_cast hzero
  · intro i
    simpa only [Rat.cast_sum, Rat.cast_mul, rationalParity_cast, rationalSpin_cast,
      Rat.cast_zero] using congrArg (fun q : ℚ => (q : ℝ)) (hcancel i)
  · simpa only [Rat.cast_sum, Rat.cast_mul, rationalCapacityWeight_cast, Rat.cast_div,
      Rat.cast_ofNat] using congrArg (fun q : ℚ => (q : ℝ)) hcapacity
  · simpa only [Rat.cast_sum, Rat.cast_mul, rationalParity_cast, Rat.cast_neg,
      Rat.cast_ofNat] using congrArg (fun q : ℚ => (q : ℝ)) hparity

/-- Nonnegativity, a vanishing deficit at one word, and every degree-three
Walsh cancellation do not suffice for the abstract capacity comparison.
This statement does not require the deficits to come from spectral data. -/
theorem not_cyclic_support_capacity_bound_from_degree_three_walsh :
    ¬ ∀ δ : (Fin 4 → Bool) → ℝ, (∀ x, 0 ≤ δ x) → δ (fun _ => false) = 0 →
        (∀ i : Fin 4, (∑ x, δ x * switchParity x * switchSign (x i)) = 0) →
        |∑ x, δ x * switchParity x| ≤
          ∑ x, δ x * (∏ i, if x i then (1 / 2 : ℝ) else 2) := by
  intro h
  obtain ⟨δ, hnonneg, hzero, hcancel, hcapacity, hparity⟩ :=
    cyclic_support_capacity_walsh_obstruction
  have hbound := h δ hnonneg hzero hcancel
  rw [hcapacity, hparity, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hbound
  norm_num at hbound

end MOC
