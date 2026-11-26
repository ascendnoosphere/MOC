import MOC.FourMatchingRelations
import MOC.FourMatchingCompensation
import MOC.FourMatchingPhysicalPositivity
import Mathlib.Tactic.Positivity

/-! Matching squares and unitary support for canonical mixed gaps of normalized
height between zero and one half. -/

open BigOperators

namespace MOC

noncomputable section

/-- The thirteen ordinary rays in the canonical mixed profile, in increasing
order. The argument of `fourCanonicalZeroHeightProfile` uses this order. -/
def fourCanonicalZeroHeightRay (j : Fin 13) : Fin 34 :=
  ![0, 7, 10, 13, 17, 18, 20, 22, 23, 27, 28, 30, 31] j

/-- The mixed coefficient is one. The supplied coefficients are the budgets
of the ordinary rays. -/
def fourCanonicalZeroHeightProfile (c : Fin 13 → ℝ) (p : Fin 24) : ℝ :=
  mixedCostRay 0 p + ∑ j, c j * ordinaryCostRay (fourCanonicalZeroHeightRay j) p

private def zeroHeightLift (c : Fin 13 → ℝ) : Fin 14 → ℝ :=
  ![c 11 + c 12 + c 8 + 1, -c 10 + c 7 - c 8 + c 9, c 1 - c 11, c 10 - c 9,
    c 0 - c 12, c 4 - c 5 + c 6 - c 8, -c 4 - c 6 - c 7 + c 8 - c 9 - 1,
    -c 1 - c 2 - c 6 - 1, -c 12 + c 2, c 2 + c 6 + c 9 + 1, c 5 - c 6,
    -c 2 - c 3 - c 9 - 1, -c 11 + c 3, c 11]

private def seedValues (p : Fin 24) : ℤ :=
  ![1, 0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0] p

private def activeOrdinaryRays (p : Fin 24) : Finset (Fin 13) :=
  ![{0, 2, 8, 11}, {0}, {0, 4, 7, 11}, {0, 3, 4, 10}, {0, 1, 5, 7},
    {0, 1, 2, 3, 5, 8, 10}, {2}, {12}, {7}, {10}, {1, 6, 7, 12},
    {1, 2, 6, 10}, {4}, {3, 4, 9, 12}, {8}, {9}, {1, 3, 8, 12}, {1},
    {5}, {2, 3, 5, 9}, {6}, {2, 6, 9, 11}, {3}, {11}] p

private theorem seedValues_eq (p : Fin 24) : mixedCostRayInt 0 p = seedValues p :=
  (by decide +kernel : ∀ p : Fin 24, mixedCostRayInt 0 p = seedValues p) p

private theorem activeOrdinaryRays_indicator (p : Fin 24) (j : Fin 13) :
    ordinaryCostRayInt (fourCanonicalZeroHeightRay j) p =
      if j ∈ activeOrdinaryRays p then 1 else 0 :=
  (by decide +kernel : ∀ p : Fin 24, ∀ j : Fin 13,
    ordinaryCostRayInt (fourCanonicalZeroHeightRay j) p =
      if j ∈ activeOrdinaryRays p then 1 else 0) p j

private theorem profile_eq_active_sum (c : Fin 13 → ℝ) (p : Fin 24) :
    fourCanonicalZeroHeightProfile c p = (seedValues p : ℝ) + ∑ j ∈ activeOrdinaryRays p, c j := by
  classical
  unfold fourCanonicalZeroHeightProfile mixedCostRay ordinaryCostRay
  rw [seedValues_eq]
  simp only [activeOrdinaryRays_indicator, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

private def affineProfile (c : Fin 13 → ℝ) : Fin 24 → ℝ :=
  ![1 + c 0 + c 2 + c 8 + c 11,
    c 0,
    1 + c 0 + c 4 + c 7 + c 11,
    1 + c 0 + c 3 + c 4 + c 10,
    1 + c 0 + c 1 + c 5 + c 7,
    2 + c 0 + c 1 + c 2 + c 3 + c 5 + c 8 + c 10,
    c 2,
    c 12,
    c 7,
    c 10,
    1 + c 1 + c 6 + c 7 + c 12,
    1 + c 1 + c 2 + c 6 + c 10,
    c 4,
    1 + c 3 + c 4 + c 9 + c 12,
    c 8,
    c 9,
    1 + c 1 + c 3 + c 8 + c 12,
    c 1,
    c 5,
    1 + c 2 + c 3 + c 5 + c 9,
    c 6,
    1 + c 2 + c 6 + c 9 + c 11,
    c 3,
    c 11]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1400000 in
private theorem lift_eq_affineProfile (c : Fin 13 → ℝ) (p : Fin 24) :
    fourMatchingEvaluation (zeroHeightLift c) p = affineProfile c p := by
  fin_cases p
  · change 2 * (c 11 + c 12 + c 8 + 1) + (-c 10 + c 7 - c 8 + c 9) + (c 1 - c 11) + (c 10 - c 9) +
      (c 0 - c 12) + (c 4 - c 5 + c 6 - c 8) + (-c 4 - c 6 - c 7 + c 8 - c 9 - 1) +
      (-c 1 - c 2 - c 6 - 1) + (-c 12 + c 2) + 2 * (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) +
      (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) + (c 11) = 1 + c 0 + c 2 + c 8 + c 11
    ring
  · change (c 11 + c 12 + c 8 + 1) + (-c 10 + c 7 - c 8 + c 9) + (c 1 - c 11) + (c 10 - c 9) +
      (c 0 - c 12) + (c 4 - c 5 + c 6 - c 8) + (-c 4 - c 6 - c 7 + c 8 - c 9 - 1) +
      (-c 1 - c 2 - c 6 - 1) + 2 * (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) + (-c 2 - c 3 - c 9 - 1) +
      (-c 11 + c 3) + (c 11) = c 0
    ring
  · change 2 * (c 11 + c 12 + c 8 + 1) + (-c 10 + c 7 - c 8 + c 9) + (c 1 - c 11) + (c 10 - c 9) +
      (c 0 - c 12) + (c 4 - c 5 + c 6 - c 8) + (-c 1 - c 2 - c 6 - 1) + (-c 12 + c 2) + (c 2 + c 6 +
      c 9 + 1) + (c 5 - c 6) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) + (c 11) = 1 + c 0 + c 4 + c 7 + c 11
    ring
  · change (c 11 + c 12 + c 8 + 1) + (c 1 - c 11) + (c 10 - c 9) + (c 0 - c 12) + (c 4 - c 5 +
      c 6 - c 8) + (-c 1 - c 2 - c 6 - 1) + (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) + (-c 11 + c 3) +
      (c 11) = 1 + c 0 + c 3 + c 4 + c 10
    ring
  · change (c 11 + c 12 + c 8 + 1) + (-c 10 + c 7 - c 8 + c 9) + (c 1 - c 11) + (c 10 - c 9) +
      (c 0 - c 12) + (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) +
      (c 11) = 1 + c 0 + c 1 + c 5 + c 7
    ring
  · change (c 11 + c 12 + c 8 + 1) + (c 1 - c 11) + (c 10 - c 9) + (c 0 - c 12) + (c 2 + c 6 + c 9 + 1) +
      (c 5 - c 6) + (-c 11 + c 3) + (c 11) = 2 + c 0 + c 1 + c 2 + c 3 + c 5 + c 8 + c 10
    ring
  · change (c 11 + c 12 + c 8 + 1) + (-c 10 + c 7 - c 8 + c 9) + (c 1 - c 11) + (c 10 - c 9) +
      (c 4 - c 5 + c 6 - c 8) + (-c 4 - c 6 - c 7 + c 8 - c 9 - 1) + (-c 1 - c 2 - c 6 - 1) + (-c 12 +
      c 2) + 2 * (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) + (c 11) = c 2
    ring
  · change (c 11 + c 12 + c 8 + 1) + (-c 10 + c 7 - c 8 + c 9) + (c 1 - c 11) + (c 10 - c 9) +
      (c 4 - c 5 + c 6 - c 8) + (-c 4 - c 6 - c 7 + c 8 - c 9 - 1) + (-c 1 - c 2 - c 6 - 1) + 2 * (c 2 +
      c 6 + c 9 + 1) + (c 5 - c 6) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) + (c 11) = c 12
    ring
  · change (c 11 + c 12 + c 8 + 1) + (-c 10 + c 7 - c 8 + c 9) + (c 1 - c 11) + (c 10 - c 9) +
      (-c 1 - c 2 - c 6 - 1) + (-c 12 + c 2) + (c 2 + c 6 + c 9 + 1) + (-c 2 - c 3 - c 9 - 1) + (-c 11 +
      c 3) + (c 11) = c 7
    ring
  · change (c 1 - c 11) + (c 10 - c 9) + (-c 1 - c 2 - c 6 - 1) + (c 2 + c 6 + c 9 + 1) + (c 11) = c 10
    ring
  · change (c 11 + c 12 + c 8 + 1) + (-c 10 + c 7 - c 8 + c 9) + (c 1 - c 11) + (c 10 - c 9) + (c 2 +
      c 6 + c 9 + 1) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) + (c 11) = 1 + c 1 + c 6 + c 7 + c 12
    ring
  · change (c 1 - c 11) + (c 10 - c 9) + (c 2 + c 6 + c 9 + 1) + (c 11) = 1 + c 1 + c 2 + c 6 + c 10
    ring
  · change (c 11 + c 12 + c 8 + 1) + (c 1 - c 11) + (c 4 - c 5 + c 6 - c 8) + (-c 1 - c 2 - c 6 - 1) +
      (-c 12 + c 2) + (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) +
      (c 11) = c 4
    ring
  · change (c 11 + c 12 + c 8 + 1) + (c 1 - c 11) + (c 4 - c 5 + c 6 - c 8) + (-c 1 - c 2 - c 6 - 1) +
      (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) + (-c 11 + c 3) + (c 11) = 1 + c 3 + c 4 + c 9 + c 12
    ring
  · change (c 11 + c 12 + c 8 + 1) + (c 1 - c 11) + (-c 1 - c 2 - c 6 - 1) + (-c 12 + c 2) + (c 2 + c 6 +
      c 9 + 1) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) + (c 11) = c 8
    ring
  · change (c 1 - c 11) + (-c 1 - c 2 - c 6 - 1) + (c 2 + c 6 + c 9 + 1) + (c 11) = c 9
    ring
  · change (c 11 + c 12 + c 8 + 1) + (c 1 - c 11) + (-c 11 + c 3) + (c 11) = 1 + c 1 + c 3 + c 8 + c 12
    ring
  · change (c 1 - c 11) + (c 11) = c 1
    ring
  · change (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) + (c 11) = c 5
    ring
  · change (c 2 + c 6 + c 9 + 1) + (c 5 - c 6) + (-c 11 + c 3) + (c 11) = 1 + c 2 + c 3 + c 5 + c 9
    ring
  · change (c 2 + c 6 + c 9 + 1) + (-c 2 - c 3 - c 9 - 1) + (-c 11 + c 3) + (c 11) = c 6
    ring
  · change (c 2 + c 6 + c 9 + 1) + (c 11) = 1 + c 2 + c 6 + c 9 + c 11
    ring
  · change (-c 11 + c 3) + (c 11) = c 3
    ring
  · change (c 11) = c 11
    ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
private theorem profile_eq_affineProfile (c : Fin 13 → ℝ) (p : Fin 24) :
    fourCanonicalZeroHeightProfile c p = affineProfile c p := by
  rw [profile_eq_active_sum]
  fin_cases p
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({0, 2, 8, 11} : Finset (Fin 13)), c j) =
      1 + c 0 + c 2 + c 8 + c 11
    rw [Finset.sum_insert (by decide : 0 ∉ ({2, 8, 11} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 2 ∉ ({8, 11} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 8 ∉ ({11} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({0} : Finset (Fin 13)), c j) =
      c 0
    norm_num [Finset.sum_insert] <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({0, 4, 7, 11} : Finset (Fin 13)), c j) =
      1 + c 0 + c 4 + c 7 + c 11
    rw [Finset.sum_insert (by decide : 0 ∉ ({4, 7, 11} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 4 ∉ ({7, 11} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 7 ∉ ({11} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({0, 3, 4, 10} : Finset (Fin 13)), c j) =
      1 + c 0 + c 3 + c 4 + c 10
    rw [Finset.sum_insert (by decide : 0 ∉ ({3, 4, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 3 ∉ ({4, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 4 ∉ ({10} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({0, 1, 5, 7} : Finset (Fin 13)), c j) =
      1 + c 0 + c 1 + c 5 + c 7
    rw [Finset.sum_insert (by decide : 0 ∉ ({1, 5, 7} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 1 ∉ ({5, 7} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 5 ∉ ({7} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((2 : ℤ) : ℝ) + (∑ j ∈ ({0, 1, 2, 3, 5, 8, 10} : Finset (Fin 13)), c j) =
      2 + c 0 + c 1 + c 2 + c 3 + c 5 + c 8 + c 10
    rw [Finset.sum_insert (by decide : 0 ∉ ({1, 2, 3, 5, 8, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 1 ∉ ({2, 3, 5, 8, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 2 ∉ ({3, 5, 8, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 3 ∉ ({5, 8, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 5 ∉ ({8, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 8 ∉ ({10} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({2} : Finset (Fin 13)), c j) =
      c 2
    norm_num [Finset.sum_insert] <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({12} : Finset (Fin 13)), c j) =
      c 12
    norm_num [Finset.sum_insert] <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({7} : Finset (Fin 13)), c j) =
      c 7
    norm_num [Finset.sum_insert] <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({10} : Finset (Fin 13)), c j) =
      c 10
    norm_num [Finset.sum_insert] <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({1, 6, 7, 12} : Finset (Fin 13)), c j) =
      1 + c 1 + c 6 + c 7 + c 12
    rw [Finset.sum_insert (by decide : 1 ∉ ({6, 7, 12} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 6 ∉ ({7, 12} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 7 ∉ ({12} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({1, 2, 6, 10} : Finset (Fin 13)), c j) =
      1 + c 1 + c 2 + c 6 + c 10
    rw [Finset.sum_insert (by decide : 1 ∉ ({2, 6, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 2 ∉ ({6, 10} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 6 ∉ ({10} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({4} : Finset (Fin 13)), c j) =
      c 4
    norm_num [Finset.sum_insert] <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({3, 4, 9, 12} : Finset (Fin 13)), c j) =
      1 + c 3 + c 4 + c 9 + c 12
    rw [Finset.sum_insert (by decide : 3 ∉ ({4, 9, 12} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 4 ∉ ({9, 12} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 9 ∉ ({12} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({8} : Finset (Fin 13)), c j) =
      c 8
    norm_num [Finset.sum_insert] <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({9} : Finset (Fin 13)), c j) =
      c 9
    norm_num [Finset.sum_insert] <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({1, 3, 8, 12} : Finset (Fin 13)), c j) =
      1 + c 1 + c 3 + c 8 + c 12
    rw [Finset.sum_insert (by decide : 1 ∉ ({3, 8, 12} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 3 ∉ ({8, 12} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 8 ∉ ({12} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({1} : Finset (Fin 13)), c j) =
      c 1
    norm_num [Finset.sum_insert] <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({5} : Finset (Fin 13)), c j) =
      c 5
    norm_num [Finset.sum_insert] <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({2, 3, 5, 9} : Finset (Fin 13)), c j) =
      1 + c 2 + c 3 + c 5 + c 9
    rw [Finset.sum_insert (by decide : 2 ∉ ({3, 5, 9} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 3 ∉ ({5, 9} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 5 ∉ ({9} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({6} : Finset (Fin 13)), c j) =
      c 6
    norm_num [Finset.sum_insert] <;> ring
  · change ((1 : ℤ) : ℝ) + (∑ j ∈ ({2, 6, 9, 11} : Finset (Fin 13)), c j) =
      1 + c 2 + c 6 + c 9 + c 11
    rw [Finset.sum_insert (by decide : 2 ∉ ({6, 9, 11} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 6 ∉ ({9, 11} : Finset (Fin 13))),
      Finset.sum_insert (by decide : 9 ∉ ({11} : Finset (Fin 13)))]
    norm_num <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({3} : Finset (Fin 13)), c j) =
      c 3
    norm_num [Finset.sum_insert] <;> ring
  · change ((0 : ℤ) : ℝ) + (∑ j ∈ ({11} : Finset (Fin 13)), c j) =
      c 11
    norm_num [Finset.sum_insert] <;> ring

private theorem zeroHeightLift_eval (c : Fin 13 → ℝ) (p : Fin 24) :
    fourMatchingEvaluation (zeroHeightLift c) p = fourCanonicalZeroHeightProfile c p :=
  (lift_eq_affineProfile c p).trans (profile_eq_affineProfile c p).symm

private def compensation (center x y : ℝ) : ℝ :=
  center * x * y - (x * y + x + y)

private def canonicalCubicRemainder (c : Fin 13 → ℝ) : ℝ :=
  c 9 * c 12 + c 9 * c 11 + c 9 * c 11 * c 12 + c 7 * c 12 +
  c 7 * c 11 + c 7 * c 11 * c 12 + c 7 * c 9 * c 12 + c 7 * c 9 * c 11 +
  c 6 * c 12 + c 6 * c 11 + c 6 * c 11 * c 12 + c 6 * c 9 +
  c 6 * c 9 * c 11 + c 6 * c 7 + c 6 * c 7 * c 12 + c 6 * c 7 * c 9 +
  c 5 * c 8 * c 10 + c 4 * c 12 + c 4 * c 11 + c 4 * c 11 * c 12 +
  c 4 * c 9 + c 4 * c 9 * c 12 + c 4 * c 7 + c 4 * c 7 * c 11 +
  c 4 * c 7 * c 9 + c 4 * c 6 * c 12 + c 4 * c 6 * c 11 + c 4 * c 6 * c 9 +
  c 4 * c 6 * c 7 + c 3 + c 3 * c 11 + c 3 * c 7 +
  c 3 * c 7 * c 11 + c 3 * c 6 + c 3 * c 6 * c 11 + c 3 * c 6 * c 7 +
  c 2 + c 2 * c 12 + c 2 * c 7 + c 2 * c 7 * c 12 +
  c 2 * c 4 + c 2 * c 4 * c 12 + c 2 * c 4 * c 7 + c 2 * c 3 +
  c 2 * c 3 * c 7 + c 1 + c 1 * c 11 + c 1 * c 9 +
  c 1 * c 9 * c 11 + c 1 * c 4 + c 1 * c 4 * c 11 + c 1 * c 4 * c 9 +
  c 1 * c 3 + c 1 * c 3 * c 11 + c 1 * c 2 + c 1 * c 2 * c 4 +
  c 1 * c 2 * c 3 + c 0 + c 0 * c 12 + c 0 * c 9 +
  c 0 * c 9 * c 12 + c 0 * c 6 + c 0 * c 6 * c 12 + c 0 * c 6 * c 9 +
  c 0 * c 3 + c 0 * c 3 * c 6 + c 0 * c 2 + c 0 * c 2 * c 12 +
  c 0 * c 2 * c 3 + c 0 * c 1 + c 0 * c 1 * c 9 + c 0 * c 1 * c 3 +
  c 0 * c 1 * c 2

private theorem zeroHeightLift_cubic (c : Fin 13 → ℝ) :
    fourMatchingCubic (zeroHeightLift c) =
      compensation (c 10) (c 4) (c 6) + compensation (c 8) (c 11) (c 12) +
        compensation (c 5) (c 7) (c 9) - 1 - canonicalCubicRemainder c := by
  simp only [fourMatchingCubic, zeroHeightLift, Matrix.cons_val, compensation,
    canonicalCubicRemainder]
  ring

private theorem canonicalCubicRemainder_nonneg (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j) :
    0 ≤ canonicalCubicRemainder c := by
  have h₀ := hc 0
  have h₁ := hc 1
  have h₂ := hc 2
  have h₃ := hc 3
  have h₄ := hc 4
  have h₅ := hc 5
  have h₆ := hc 6
  have h₇ := hc 7
  have h₈ := hc 8
  have h₉ := hc 9
  have h₁₀ := hc 10
  have h₁₁ := hc 11
  have h₁₂ := hc 12
  unfold canonicalCubicRemainder
  positivity

private theorem positive_compensation {center x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : 0 < compensation center x y) :
    0 < x ∧ 0 < y ∧ x * y + x + y < center * x * y := by
  have hxne : x ≠ 0 := by
    intro he
    simp only [compensation, he, mul_zero, zero_mul, zero_add, zero_sub] at h
    linarith only [h, hy]
  have hyne : y ≠ 0 := by
    intro he
    simp only [compensation, he, mul_zero, add_zero, zero_add, zero_sub] at h
    linarith only [h, hx]
  exact ⟨lt_of_le_of_ne hx hxne.symm, lt_of_le_of_ne hy hyne.symm, sub_pos.mp h⟩

/-- A canonical mixed profile realized by the real parts of matching products
supplies one of three strict compensation budgets. For each budget, the
conclusion lists the two leaf coefficients and the inequality on the
coefficient of the ordinary ray shared by the leaves. -/
theorem fourCanonicalZeroHeight_compensation (a b : Fin 4 → ℂ) (η : ℂ)
    (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hvalues : ∀ p : Fin 24, (η * matchingProduct a b (fourPerm p).symm).re =
      fourCanonicalZeroHeightProfile c p) :
    (0 < c 4 ∧ 0 < c 6 ∧ c 4 * c 6 + c 4 + c 6 < c 10 * c 4 * c 6) ∨
    (0 < c 11 ∧ 0 < c 12 ∧ c 11 * c 12 + c 11 + c 12 < c 8 * c 11 * c 12) ∨
    (0 < c 7 ∧ 0 < c 9 ∧ c 7 * c 9 + c 7 + c 9 < c 5 * c 7 * c 9) := by
  have h := fourMatchingCubic_zero_of_evaluation_eq_spectral a b η (zeroHeightLift c)
    (fun p => (zeroHeightLift_eval c p).trans (hvalues p).symm)
  rw [zeroHeightLift_cubic] at h
  have hr := canonicalCubicRemainder_nonneg c hc
  by_cases first : 0 < compensation (c 10) (c 4) (c 6)
  · exact Or.inl (positive_compensation (hc _) (hc _) first)
  by_cases second : 0 < compensation (c 8) (c 11) (c 12)
  · exact Or.inr (Or.inl (positive_compensation (hc _) (hc _) second))
  have third : 0 < compensation (c 5) (c 7) (c 9) := by
    linarith only [h, hr, le_of_not_gt first, le_of_not_gt second]
  exact Or.inr (Or.inr (positive_compensation (hc _) (hc _) third))

private def compensationRays (t : Fin 3) : Fin 3 → Fin 13 :=
  ![![10, 4, 6], ![8, 11, 12], ![5, 7, 9]] t

private abbrev canonicalOrdinaryRay (j : Fin 13) : Fin 24 → ℝ :=
  ordinaryCostRay (fourCanonicalZeroHeightRay j)

private theorem seed_square_compensation (t : Fin 3) (p : Fin 24) :
    (mixedCostRay 0 p)^2 - mixedCostRay 0 p =
      canonicalOrdinaryRay (compensationRays t 0) p *
        (mixedCostRay 0 p - canonicalOrdinaryRay (compensationRays t 1) p -
          canonicalOrdinaryRay (compensationRays t 2) p) := by
  have h : ∀ t : Fin 3, ∀ p : Fin 24,
      (mixedCostRayInt 0 p)^2 - mixedCostRayInt 0 p =
        ordinaryCostRayInt (fourCanonicalZeroHeightRay (compensationRays t 0)) p *
          (mixedCostRayInt 0 p -
            ordinaryCostRayInt (fourCanonicalZeroHeightRay (compensationRays t 1)) p -
            ordinaryCostRayInt (fourCanonicalZeroHeightRay (compensationRays t 2)) p) := by
    decide +kernel
  unfold canonicalOrdinaryRay mixedCostRay ordinaryCostRay
  exact_mod_cast h t p

/-- The canonical spectral profile lies in the real matching space. -/
theorem fourCanonicalZeroHeightProfile_mem (c : Fin 13 → ℝ) :
    fourCanonicalZeroHeightProfile c ∈ realMatchingFunctionSpace :=
  ⟨zeroHeightLift c, funext (zeroHeightLift_eval c)⟩

private theorem seed_mem : mixedCostRay 0 ∈ realMatchingFunctionSpace := by
  have he : fourCanonicalZeroHeightProfile (0 : Fin 13 → ℝ) = mixedCostRay 0 := by
    funext p
    simp only [fourCanonicalZeroHeightProfile, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero]
  rw [← he]
  exact fourCanonicalZeroHeightProfile_mem _

private theorem reciprocal_budget {b x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : x * y + x + y < b * x * y) : (1 + 1 / x + 1 / y) / 4 ≤ b := by
  have hb : 1 + 1 / x + 1 / y ≤ b := by
    apply le_of_mul_le_mul_right _ (mul_pos hx hy)
    have he : (1 + 1 / x + 1 / y) * (x * y) = x * y + x + y := by
      field_simp [hx.ne', hy.ne'] <;> ring
    rw [he, ← mul_assoc]
    exact h.le
  linarith only [hb, show 0 < 1 + 1 / x + 1 / y by positivity]

private theorem canonicalProfile_sos_of_three (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (i j k : Fin 13) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hg : IsRealMatchingSOS (fun p => mixedCostRay 0 p + c i * canonicalOrdinaryRay i p +
      c j * canonicalOrdinaryRay j p + c k * canonicalOrdinaryRay k p)) :
    IsRealMatchingSOS (fourCanonicalZeroHeightProfile c) := by
  let g (p : Fin 24) : ℝ := mixedCostRay 0 p + c i * canonicalOrdinaryRay i p +
    c j * canonicalOrdinaryRay j p + c k * canonicalOrdinaryRay k p
  let s : Finset (Fin 13) := {i, j, k}
  have hsplit : fourCanonicalZeroHeightProfile c =
      fun p => g p + ∑ a ∈ Finset.univ \ s, c a * canonicalOrdinaryRay a p := by
    funext p
    have hfull := Finset.sum_sdiff (Finset.subset_univ s)
      (f := fun a => c a * canonicalOrdinaryRay a p)
    have hsmall : (∑ a ∈ s, c a * canonicalOrdinaryRay a p) =
        c i * canonicalOrdinaryRay i p + c j * canonicalOrdinaryRay j p +
          c k * canonicalOrdinaryRay k p := by
      simp [s, Finset.sum_insert, hij, hik, hjk, add_assoc]
    rw [fourCanonicalZeroHeightProfile, ← hfull, hsmall]
    unfold g
    ring
  have hadd (s' : Finset (Fin 13)) :
      IsRealMatchingSOS (fun p => g p + ∑ a ∈ s', c a * canonicalOrdinaryRay a p) := by
    induction s' using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, add_zero] using hg
    | insert a s' ha ih =>
      simpa only [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using
        realMatchingSOS_add_ordinaryCostRay ih (fourCanonicalZeroHeightRay a) (c a) (hc a)
  rw [hsplit]
  exact hadd _

private theorem compensatedProfile_sos (t : Fin 3) (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hx : 0 < c (compensationRays t 1)) (hy : 0 < c (compensationRays t 2))
    (hb : (1 + 1 / c (compensationRays t 1) + 1 / c (compensationRays t 2)) / 4 ≤
      c (compensationRays t 0)) : IsRealMatchingSOS (fourCanonicalZeroHeightProfile c) := by
  let i := compensationRays t 0
  let j := compensationRays t 1
  let k := compensationRays t 2
  let d : Fin 3 → ℝ := ![1, c j, c k]
  let e : Fin 3 → ℝ := ![1 / 2, -1 / 2, -1 / 2]
  let f : Fin 3 → Fin 24 → ℝ := ![mixedCostRay 0, canonicalOrdinaryRay j, canonicalOrdinaryRay k]
  have hd (a : Fin 3) : 0 < d a := by
    fin_cases a
    · exact zero_lt_one
    · exact hx
    · exact hy
  have hf (a : Fin 3) : f a ∈ realMatchingFunctionSpace := by
    fin_cases a
    · exact seed_mem
    · exact ordinaryCostRay_mem_realMatchingFunctionSpace _
    · exact ordinaryCostRay_mem_realMatchingFunctionSpace _
  have hbudget : (∑ a, (e a)^2 / d a) ≤ c i := by
    calc
      _ = (1 + 1 / c j + 1 / c k) / 4 := by
        rw [Fin.sum_univ_three]
        change (1 / 2 : ℝ)^2 / 1 + (-1 / 2)^2 / c j + (-1 / 2)^2 / c k = _
        norm_num
        ring
      _ ≤ _ := hb
  let g (p : Fin 24) : ℝ := mixedCostRay 0 p + c i * canonicalOrdinaryRay i p +
    c j * canonicalOrdinaryRay j p + c k * canonicalOrdinaryRay k p
  have hg : IsRealMatchingSOS g := by
    have heq (p : Fin 24) :
        c i * (canonicalOrdinaryRay i p)^2 + (∑ a, d a * (f a p)^2) -
          2 * canonicalOrdinaryRay i p * (∑ a, e a * f a p) = g p := by
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      change c i * (canonicalOrdinaryRay i p)^2 +
        (1 * (mixedCostRay 0 p)^2 + c j * (canonicalOrdinaryRay j p)^2 +
          c k * (canonicalOrdinaryRay k p)^2) - 2 * canonicalOrdinaryRay i p *
        ((1 / 2) * mixedCostRay 0 p + (-1 / 2) * canonicalOrdinaryRay j p +
          (-1 / 2) * canonicalOrdinaryRay k p) = g p
      simp only [ordinaryCostRay_sq, one_mul, g]
      linear_combination seed_square_compensation t p
    have hs := fourMatchingSOS_of_star (c i) (canonicalOrdinaryRay i) d e f
      (ordinaryCostRay_mem_realMatchingFunctionSpace _) hf hd hbudget
    simpa only [heq] using hs
  have hij : i ≠ j := (by decide +kernel : ∀ t : Fin 3,
    compensationRays t 0 ≠ compensationRays t 1) t
  have hik : i ≠ k := (by decide +kernel : ∀ t : Fin 3,
    compensationRays t 0 ≠ compensationRays t 2) t
  have hjk : j ≠ k := (by decide +kernel : ∀ t : Fin 3,
    compensationRays t 1 ≠ compensationRays t 2) t
  exact canonicalProfile_sos_of_three c hc i j k hij hik hjk hg

/-- Every canonical mixed profile realized by real parts of matching products
at zero support height is a matching sum of squares. -/
theorem fourCanonicalZeroHeight_sos (a b : Fin 4 → ℂ) (η : ℂ)
    (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hvalues : ∀ p : Fin 24, (η * matchingProduct a b (fourPerm p).symm).re =
      fourCanonicalZeroHeightProfile c p) :
    IsRealMatchingSOS (fourCanonicalZeroHeightProfile c) := by
  rcases fourCanonicalZeroHeight_compensation a b η c hc hvalues with h | h | h
  · exact compensatedProfile_sos 0 c hc h.1 h.2.1 (reciprocal_budget h.1 h.2.1 h.2.2)
  · exact compensatedProfile_sos 1 c hc h.1 h.2.1 (reciprocal_budget h.1 h.2.1 h.2.2)
  · exact compensatedProfile_sos 2 c hc h.1 h.2.1 (reciprocal_budget h.1 h.2.1 h.2.2)

private def canonicalHeightSlope (c : Fin 13 → ℝ) : ℝ :=
  zeroHeightLift c 0 * zeroHeightLift c 6 - zeroHeightLift c 1 * zeroHeightLift c 5

private def heightLift (c : Fin 13 → ℝ) (height : ℝ) (i : Fin 14) : ℝ :=
  zeroHeightLift c i - if i = 13 then height else 0

set_option maxHeartbeats 3000000 in
private theorem heightLift_eval (c : Fin 13 → ℝ) (height : ℝ) (p : Fin 24) :
    fourMatchingEvaluation (heightLift c height) p = fourCanonicalZeroHeightProfile c p - height := by
  have h (m : Fin 14 → ℝ) (p : Fin 24) :
      fourMatchingEvaluation (fun i => m i - if i = 13 then height else 0) p =
        fourMatchingEvaluation m p - height := by
    fin_cases p <;>
      simp (disch := decide) only [fourMatchingEvaluation, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Matrix.cons_val, if_pos, if_neg, sub_zero, add_sub_assoc]
  rw [← zeroHeightLift_eval]
  exact h (zeroHeightLift c) p

set_option maxHeartbeats 3000000 in
private theorem heightLift_cubic (c : Fin 13 → ℝ) (height : ℝ) :
    fourMatchingCubic (heightLift c height) =
      fourMatchingCubic (zeroHeightLift c) - height * canonicalHeightSlope c := by
  have h (m : Fin 14 → ℝ) :
      fourMatchingCubic (fun i => m i - if i = 13 then height else 0) =
        fourMatchingCubic m - height * (m 0 * m 6 - m 1 * m 5) := by
    simp (disch := decide) only [fourMatchingCubic, if_pos, if_neg, sub_zero]
    ring
  exact h (zeroHeightLift c)

private def triadLeafSum (c : Fin 13 → ℝ) : ℝ :=
  c 4 * c 6 + c 4 + c 6 + (c 11 * c 12 + c 11 + c 12) + (c 7 * c 9 + c 7 + c 9)

private def centerProduct (c : Fin 13 → ℝ) : ℝ := c 5 * c 8 * c 10

private def centerPairSum (c : Fin 13 → ℝ) : ℝ := c 5 * c 8 + c 5 * c 10 + c 8 * c 10

private def canonicalHeightRemainder (c : Fin 13 → ℝ) : ℝ :=
  2 * c 0 * c 1 * c 2 + 2 * c 0 * c 1 * c 3 + 2 * c 0 * c 1 * c 9 + 2 * c 0 * c 1 +
  2 * c 0 * c 2 * c 3 + 2 * c 0 * c 2 * c 12 + 2 * c 0 * c 2 + 2 * c 0 * c 3 * c 6 +
  2 * c 0 * c 3 + 2 * c 0 * c 6 * c 9 + 2 * c 0 * c 6 * c 12 + 2 * c 0 * c 6 +
  2 * c 0 * c 9 * c 12 + 2 * c 0 * c 9 + 2 * c 0 * c 12 + 2 * c 0 + 2 * c 1 * c 2 * c 3 +
  2 * c 1 * c 2 * c 4 + 2 * c 1 * c 2 + 2 * c 1 * c 3 * c 11 + 2 * c 1 * c 3 +
  2 * c 1 * c 4 * c 9 + 2 * c 1 * c 4 * c 11 + 2 * c 1 * c 4 + 2 * c 1 * c 9 * c 11 +
  2 * c 1 * c 9 + 2 * c 1 * c 11 + 2 * c 1 + 2 * c 2 * c 3 * c 7 + 2 * c 2 * c 3 +
  2 * c 2 * c 4 * c 7 + 2 * c 2 * c 4 * c 12 + 2 * c 2 * c 4 + 2 * c 2 * c 7 * c 12 +
  2 * c 2 * c 7 + 2 * c 2 * c 12 + 2 * c 2 + 2 * c 3 * c 6 * c 7 + 2 * c 3 * c 6 * c 11 +
  2 * c 3 * c 6 + 2 * c 3 * c 7 * c 11 + 2 * c 3 * c 7 + 2 * c 3 * c 11 + 2 * c 3 +
  2 * c 4 * c 6 * c 7 + 2 * c 4 * c 6 * c 9 + 2 * c 4 * c 6 * c 11 + 2 * c 4 * c 6 * c 12 +
  (3/2) * c 4 * c 6 + 2 * c 4 * c 7 * c 9 + 2 * c 4 * c 7 * c 11 + c 4 * c 7 +
  2 * c 4 * c 9 * c 12 + c 4 * c 9 + c 4 * c 10 + 2 * c 4 * c 11 * c 12 + c 4 * c 11 +
  c 4 * c 12 + (1/2) * c 4 + c 5 * c 7 + c 5 * c 9 + 2 * c 6 * c 7 * c 9 +
  2 * c 6 * c 7 * c 12 + c 6 * c 7 + 2 * c 6 * c 9 * c 11 + c 6 * c 9 + c 6 * c 10 +
  2 * c 6 * c 11 * c 12 + c 6 * c 11 + c 6 * c 12 + (1/2) * c 6 + 2 * c 7 * c 9 * c 11 +
  2 * c 7 * c 9 * c 12 + (3/2) * c 7 * c 9 + 2 * c 7 * c 11 * c 12 + c 7 * c 11 + c 7 * c 12 +
  (1/2) * c 7 + c 8 * c 11 + c 8 * c 12 + 2 * c 9 * c 11 * c 12 + c 9 * c 11 + c 9 * c 12 +
  (1/2) * c 9 + (3/2) * c 11 * c 12 + (1/2) * c 11 + (1/2) * c 12

private theorem canonicalHeightRemainder_eq (c : Fin 13 → ℝ) :
    canonicalHeightRemainder c =
      2 * (canonicalCubicRemainder c - centerProduct c) + 3 / 2 * triadLeafSum c +
        canonicalHeightSlope c + 1 + centerPairSum c := by
  simp only [canonicalHeightRemainder, canonicalCubicRemainder, centerProduct, triadLeafSum,
    canonicalHeightSlope, zeroHeightLift, centerPairSum, Matrix.cons_val]
  ring

private theorem canonicalHeightRemainder_nonneg (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j) :
    0 ≤ canonicalHeightRemainder c := by
  have h₀ := hc 0
  have h₁ := hc 1
  have h₂ := hc 2
  have h₃ := hc 3
  have h₄ := hc 4
  have h₅ := hc 5
  have h₆ := hc 6
  have h₇ := hc 7
  have h₈ := hc 8
  have h₉ := hc 9
  have h₁₀ := hc 10
  have h₁₁ := hc 11
  have h₁₂ := hc 12
  unfold canonicalHeightRemainder
  positivity

private theorem three_center_budget_sum_strict (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hP : p * (q + r) < 1) (hQ : q * (p + r) < 1) (hR : r * (p + q) < 1) :
    p * q + p * r + q * r < 1 + 2 * (p * q * r) := by
  by_cases hp' : 1 / 2 ≤ p
  · nlinarith only [hP, mul_le_mul_of_nonneg_left hp' (mul_nonneg hq hr)]
  by_cases hq' : 1 / 2 ≤ q
  · nlinarith only [hQ, mul_le_mul_of_nonneg_left hq' (mul_nonneg hp hr)]
  by_cases hr' : 1 / 2 ≤ r
  · nlinarith only [hR, mul_le_mul_of_nonneg_left hr' (mul_nonneg hp hq)]
  have hpq := mul_le_mul (le_of_not_ge hp') (le_of_not_ge hq') hq (by norm_num)
  have hpr := mul_le_mul (le_of_not_ge hp') (le_of_not_ge hr') hr (by norm_num)
  have hqr := mul_le_mul (le_of_not_ge hq') (le_of_not_ge hr') hr (by norm_num)
  linarith only [hpq, hpr, hqr, mul_nonneg (mul_nonneg hp hq) hr]

private theorem leaf_product_bound (t : Fin 3) (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (h : ¬ IsRealMatchingSOS (fourCanonicalZeroHeightProfile c)) :
    c (compensationRays t 0) * c (compensationRays t 1) * c (compensationRays t 2) ≤
      (c (compensationRays t 1) * c (compensationRays t 2) +
        c (compensationRays t 1) + c (compensationRays t 2)) / 4 := by
  let b := c (compensationRays t 0)
  let x := c (compensationRays t 1)
  let y := c (compensationRays t 2)
  change b*x*y ≤ (x*y+x+y)/4
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · by_contra! hbad
      apply h
      apply compensatedProfile_sos t c hc hx hy
      change (1 + 1 / x + 1 / y) / 4 ≤ b
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      apply le_of_mul_le_mul_right _ (mul_pos hx hy)
      have he : (1 + 1 / x + 1 / y) * (x * y) = x * y + x + y := by
        field_simp [hx.ne', hy.ne'] <;> ring
      rw [he]
      linarith only [hbad]
    · have hy0 : y = 0 := le_antisymm (le_of_not_gt hy) (hc _)
      simpa only [hy0, mul_zero, zero_add, add_zero] using
        div_nonneg (show 0 ≤ x from hc _) (by norm_num : (0 : ℝ) ≤ 4)
  · have hx0 : x = 0 := le_antisymm (le_of_not_gt hx) (hc _)
    simpa only [hx0, mul_zero, zero_mul, zero_add] using
      div_nonneg (show 0 ≤ y from hc _) (by norm_num : (0 : ℝ) ≤ 4)

private def centerRays (t : Fin 3) : Fin 3 → Fin 13 :=
  ![![5, 8, 10], ![8, 5, 10], ![10, 5, 8]] t

private theorem center_pair_identity (t : Fin 3) (j : Fin 2) (p : Fin 24) :
    2 * canonicalOrdinaryRay (centerRays t 0) p * canonicalOrdinaryRay (centerRays t j.succ) p =
      (mixedCostRay 0 p)^2 - mixedCostRay 0 p := by
  have h : ∀ (t : Fin 3) (j : Fin 2) (p : Fin 24),
      2 * ordinaryCostRayInt (fourCanonicalZeroHeightRay (centerRays t 0)) p *
        ordinaryCostRayInt (fourCanonicalZeroHeightRay (centerRays t j.succ)) p =
          (mixedCostRayInt 0 p)^2 - mixedCostRayInt 0 p := by decide +kernel
  unfold canonicalOrdinaryRay ordinaryCostRay mixedCostRay
  exact_mod_cast h t j p

private theorem centralProfile_sos (t : Fin 3) (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (h : 1 ≤ c (centerRays t 0) * (c (centerRays t 1) + c (centerRays t 2))) :
    IsRealMatchingSOS (fourCanonicalZeroHeightProfile c) := by
  let i := centerRays t 0
  let j := centerRays t 1
  let k := centerRays t 2
  let s := c j + c k
  have hs : 0 < s := by
    apply lt_of_le_of_ne (add_nonneg (hc j) (hc k))
    intro he
    change 0 = s at he
    have h' : 1 ≤ c i * s := h
    rw [← he, mul_zero] at h'
    norm_num at h'
  have hb : 0 ≤ c i - 1 / s := sub_nonneg.mpr ((div_le_iff₀ hs).2 h)
  let x : Fin 24 → ℝ := canonicalOrdinaryRay i
  let y : Fin 24 → ℝ := canonicalOrdinaryRay j
  let z : Fin 24 → ℝ := canonicalOrdinaryRay k
  let d : Fin 4 → ℝ := ![c i - 1 / s, 1, c j, c k]
  let f : Fin 4 → Fin 24 → ℝ :=
    ![x, mixedCostRay 0, y - (1 / s) • x, z - (1 / s) • x]
  have hd (a : Fin 4) : 0 ≤ d a := by
    fin_cases a
    · exact hb
    · exact zero_le_one
    · exact hc j
    · exact hc k
  have hx : x ∈ realMatchingFunctionSpace := ordinaryCostRay_mem_realMatchingFunctionSpace _
  have hf (a : Fin 4) : f a ∈ realMatchingFunctionSpace := by
    fin_cases a
    · exact hx
    · exact seed_mem
    · exact realMatchingFunctionSpace.sub_mem (ordinaryCostRay_mem_realMatchingFunctionSpace _)
        (realMatchingFunctionSpace.smul_mem _ hx)
    · exact realMatchingFunctionSpace.sub_mem (ordinaryCostRay_mem_realMatchingFunctionSpace _)
        (realMatchingFunctionSpace.smul_mem _ hx)
  have he (p : Fin 24) :
      (∑ a, d a * (f a p)^2) = mixedCostRay 0 p + c i * x p + c j * y p + c k * z p := by
    rw [Fin.sum_univ_four]
    change (c i - 1 / s) * (x p)^2 + 1 * (mixedCostRay 0 p)^2 +
      c j * (y p - (1 / s) * x p)^2 + c k * (z p - (1 / s) * x p)^2 = _
    have hx2 : (x p)^2 = x p := ordinaryCostRay_sq _ _
    have hy2 : (y p)^2 = y p := ordinaryCostRay_sq _ _
    have hz2 : (z p)^2 = z p := ordinaryCostRay_sq _ _
    rw [one_mul]
    have h₁ : 2 * x p * y p = (mixedCostRay 0 p)^2 - mixedCostRay 0 p :=
      center_pair_identity t 0 p
    have h₂ : 2 * x p * z p = (mixedCostRay 0 p)^2 - mixedCostRay 0 p :=
      center_pair_identity t 1 p
    have hsum : c j + c k = s := rfl
    have hcombine : c j * (2 * x p * y p) + c k * (2 * x p * z p) =
        s * ((mixedCostRay 0 p)^2 - mixedCostRay 0 p) := by
      rw [h₁, h₂, ← hsum]
      ring
    calc
      _ = mixedCostRay 0 p + c i * x p + c j * y p + c k * z p +
          ((mixedCostRay 0 p)^2 - mixedCostRay 0 p) -
          (1 / s) * (c j * (2 * x p * y p) + c k * (2 * x p * z p)) +
          x p * (-1 / s + (c j + c k) * (1 / s)^2) := by
        rw [sub_sq, sub_sq, mul_pow, hx2, hy2, hz2]
        ring
      _ = _ := by
        rw [hcombine, hsum]
        field_simp [hs.ne']
        ring
  have hij : i ≠ j := (by decide +kernel : ∀ t : Fin 3, centerRays t 0 ≠ centerRays t 1) t
  have hik : i ≠ k := (by decide +kernel : ∀ t : Fin 3, centerRays t 0 ≠ centerRays t 2) t
  have hjk : j ≠ k := (by decide +kernel : ∀ t : Fin 3, centerRays t 1 ≠ centerRays t 2) t
  apply canonicalProfile_sos_of_three c hc i j k hij hik hjk
  simpa only [he] using isRealMatchingSOS_weighted d f hd hf

/-- A canonical mixed spectral gap of normalized support height between
zero and one half is a sum of real matching squares. -/
theorem fourCanonicalHeight_le_half_sos (a b : Fin 4 → ℂ) (η : ℂ)
    (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j) (height : ℝ)
    (hheight : 0 ≤ height) (hhalf : height ≤ 1 / 2)
    (hvalues : ∀ p : Fin 24, fourCanonicalZeroHeightProfile c p =
      height - (η * matchingProduct a b (fourPerm p).symm).re) :
    IsRealMatchingSOS (fourCanonicalZeroHeightProfile c) := by
  have hd := fourMatchingCubic_zero_of_evaluation_eq_spectral a b (-η) (heightLift c height)
    (fun p => by rw [heightLift_eval, hvalues, neg_mul, Complex.neg_re]; ring)
  rw [heightLift_cubic] at hd
  by_contra hn
  have f₁ := leaf_product_bound 0 c hc hn
  have f₂ := leaf_product_bound 1 c hc hn
  have f₃ := leaf_product_bound 2 c hc hn
  change c 10 * c 4 * c 6 ≤ (c 4 * c 6 + c 4 + c 6) / 4 at f₁
  change c 8 * c 11 * c 12 ≤ (c 11 * c 12 + c 11 + c 12) / 4 at f₂
  change c 5 * c 7 * c 9 ≤ (c 7 * c 9 + c 7 + c 9) / 4 at f₃
  have hF : fourMatchingCubic (zeroHeightLift c) ≤
      -1 - canonicalCubicRemainder c - 3 / 4 * triadLeafSum c := by
    rw [zeroHeightLift_cubic]
    unfold compensation triadLeafSum
    linarith only [f₁, f₂, f₃]
  have hn₁ : c 5 * (c 8 + c 10) < 1 := lt_of_not_ge fun h => hn (centralProfile_sos 0 c hc h)
  have hn₂ : c 8 * (c 5 + c 10) < 1 := lt_of_not_ge fun h => hn (centralProfile_sos 1 c hc h)
  have hn₃ : c 10 * (c 5 + c 8) < 1 := lt_of_not_ge fun h => hn (centralProfile_sos 2 c hc h)
  have hcenters : centerPairSum c < 1 + 2 * centerProduct c :=
    three_center_budget_sum_strict _ _ _ (hc 5) (hc 8) (hc 10) hn₁ hn₂ hn₃
  have hR : 0 ≤ triadLeafSum c := by
    have h₀ := hc 4
    have h₁ := hc 6
    have h₂ := hc 11
    have h₃ := hc 12
    have h₄ := hc 7
    have h₅ := hc 9
    unfold triadLeafSum
    positivity
  have hFneg : fourMatchingCubic (zeroHeightLift c) < 0 := by
    linarith only [hF, hR, canonicalCubicRemainder_nonneg c hc]
  have hFQ : 2 * fourMatchingCubic (zeroHeightLift c) - canonicalHeightSlope c < 0 := by
    linarith only [hF, hcenters, canonicalHeightRemainder_eq c, canonicalHeightRemainder_nonneg c hc]
  by_cases hh : height = 0
  · rw [hh, zero_mul, sub_zero] at hd
    exact hFneg.ne hd
  have h₀ := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 - 2 * height by linarith) hFneg.le
  have h₁ := mul_neg_of_pos_of_neg (lt_of_le_of_ne hheight (Ne.symm hh)) hFQ
  nlinarith only [h₀, h₁, hd]

/-- A canonical mixed spectral gap of normalized height between zero and
one half bounds the determinant projection at every unitary mixer. -/
theorem fourCanonicalHeight_le_half_support (a b : Fin 4 → ℂ) (η : ℂ)
    (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j) (height : ℝ)
    (hheight : 0 ≤ height) (hhalf : height ≤ 1 / 2)
    (hvalues : ∀ p : Fin 24, fourCanonicalZeroHeightProfile c p =
      height - (η * matchingProduct a b (fourPerm p).symm).re)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    (η * determinantValue a b U).re ≤ height := by
  have he : fourCanonicalZeroHeightProfile c =
      fun p => height - (η * matchingProduct a b (fourPerm p).symm).re := funext hvalues
  apply four_support_of_spectral_matchingSOS a b η height U hU
  · rw [← he]
    exact fourCanonicalZeroHeightProfile_mem c
  · rw [← he]
    exact fourCanonicalHeight_le_half_sos a b η c hc height hheight hhalf hvalues

/-- A canonical mixed spectral gap at zero height bounds the determinant
projection at every unitary mixer. -/
theorem fourCanonicalZeroHeight_support (a b : Fin 4 → ℂ) (η : ℂ)
    (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hvalues : ∀ p : Fin 24, fourCanonicalZeroHeightProfile c p =
      -(η * matchingProduct a b (fourPerm p).symm).re)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    (η * determinantValue a b U).re ≤ 0 :=
  fourCanonicalHeight_le_half_support a b η c hc 0 le_rfl (by norm_num)
    (fun p => by rw [zero_sub]; exact hvalues p) U hU

end

end MOC
