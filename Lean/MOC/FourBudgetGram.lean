import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The four-coefficient Gram certificate used in Zheng's contact cases T4
and T5. The Gram form is an arrowhead after adding and subtracting its
first two coordinates. The quaternion identity requires only equal norms. -/

open BigOperators

namespace MOC

private def budgetForm (a b c d x y z w : ℝ) : ℝ :=
  (a + d) * (x + y) ^ 2 + (b + d) * (x - y) ^ 2 + c * z ^ 2 + d * w ^ 2 +
    4 * d * y * w + 2 * d * z * w

private theorem budgetForm_nonneg {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcapacity : d ^ 2 * (a + b + c + d) ≤ a * b * (c - d))
    (x y z w : ℝ) : 0 ≤ budgetForm a b c d x y z w := by
  rcases eq_or_lt_of_le hd with hzero | hpos
  · simp only [budgetForm, ← hzero, add_zero, zero_mul, mul_zero]
    positivity
  have hA : 0 < a + d := add_pos_of_nonneg_of_pos ha hpos
  have hB : 0 < b + d := add_pos_of_nonneg_of_pos hb hpos
  have hcd : d < c := by
    by_contra! hle
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hb)
      (sub_nonpos.mpr hle)))
      ((mul_pos (pow_pos hpos 2) (by linarith only [ha, hb, hc, hpos])).trans_le hcapacity)
  have hC : 0 < c := hpos.trans hcd
  let rem := d - d ^ 2 / (a + d) - d ^ 2 / (b + d) - d ^ 2 / c
  have hrem : 0 ≤ rem := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (mul_pos hA hB) hC)).mp
    have he : (a + d) * (b + d) * c * rem =
        d * (a * b * (c - d) - d ^ 2 * (a + b + c + d)) := by
      dsimp only [rem]
      field_simp [hA.ne', hB.ne', hC.ne']
      <;> ring
    rw [he]
    exact mul_nonneg hd (sub_nonneg.mpr hcapacity)
  have hsq : budgetForm a b c d x y z w =
      (a + d) * (x + y + d / (a + d) * w) ^ 2 +
      (b + d) * (x - y - d / (b + d) * w) ^ 2 +
      c * (z + d / c * w) ^ 2 + rem * w ^ 2 := by
    dsimp only [budgetForm, rem]
    field_simp [hA.ne', hB.ne', hC.ne']
    <;> ring
  rw [hsq]
  positivity

private def pairA (p q : Fin 4 → ℝ) : ℝ := p 0 * q 3 + p 3 * q 0
private def pairB (p q : Fin 4 → ℝ) : ℝ := p 1 * q 2 - p 2 * q 1
private def pairD (p q : Fin 4 → ℝ) : ℝ := p 0 ^ 2 + p 2 ^ 2 - q 0 ^ 2 - q 2 ^ 2
private def pairE (p q : Fin 4 → ℝ) : ℝ := p 1 ^ 2 - p 2 ^ 2 - q 0 ^ 2 + q 3 ^ 2
private def pairG (p q : Fin 4 → ℝ) : ℝ := p 0 ^ 2 - p 3 ^ 2 - q 1 ^ 2 + q 2 ^ 2

private def quaternionSq (p : Fin 4 → ℝ) : ℝ :=
  p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2

private def budgetCost (a b c d : ℝ) (p q : Fin 4 → ℝ) : ℝ :=
  let A := pairA p q
  let B := pairB p q
  a * (A - B) ^ 2 + b * (A + B) ^ 2 + c * pairD p q ^ 2 +
    d * (2 * (A ^ 2 + B ^ 2) - pairE p q * pairG p q)

private def signedLeft (p : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![p, ![-p 1, p 0, -p 3, p 2], ![-p 2, p 3, p 0, -p 1], ![-p 3, -p 2, p 1, p 0]]

private def signedRight (q : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![q, ![q 1, -q 0, -q 3, q 2], ![q 2, q 3, -q 0, -q 1], ![q 3, -q 2, q 1, -q 0]]

private def signedBudgetForm (a b c d : ℝ) (p q : Fin 4 → ℝ) : ℝ :=
  budgetForm a b c d (-p 0 * pairB p q) (p 0 * pairA p q) (-q 3 * pairD p q)
      (-q 3 * pairG p q) +
    budgetForm a b c d (q 0 * pairB p q) (-q 0 * pairA p q) (-p 3 * pairD p q)
      (-p 3 * pairE p q)

private theorem vector_zero {α : Type*} (a b c d : α) : ![a, b, c, d] 0 = a := rfl
private theorem vector_one {α : Type*} (a b c d : α) : ![a, b, c, d] 1 = b := rfl
private theorem vector_two {α : Type*} (a b c d : α) : ![a, b, c, d] 2 = c := rfl
private theorem vector_three {α : Type*} (a b c d : α) : ![a, b, c, d] 3 = d := rfl

set_option maxHeartbeats 3000000 in
private theorem budgetCost_gram_identity (a b c d : ℝ) (p q : Fin 4 → ℝ) :
    (quaternionSq p + quaternionSq q) * budgetCost a b c d p q =
      (∑ j, signedBudgetForm a b c d (signedLeft p j) (signedRight q j)) +
      c * (p 0 ^ 2 + p 2 ^ 2 + q 0 ^ 2 + q 2 ^ 2) *
        (2 * pairD p q - (quaternionSq p - quaternionSq q)) *
        (quaternionSq p - quaternionSq q) := by
  simp only [Fin.sum_univ_four, signedBudgetForm, budgetForm, budgetCost, signedLeft,
    signedRight, pairA, pairB, pairD, pairE, pairG, quaternionSq,
    vector_zero, vector_one, vector_two, vector_three]
  ring

/-- The four-coefficient inequality on real unit quaternion coordinates.
It is independent of the algebraic conditions on the spectral source. -/
theorem quaternion_four_budget_nonneg {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcapacity : d ^ 2 * (a + b + c + d) ≤ a * b * (c - d))
    (p q : Fin 4 → ℝ) (hp : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 1)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1) :
    let A := p 0 * q 3 + p 3 * q 0
    let B := p 1 * q 2 - p 2 * q 1
    let D := p 0 ^ 2 + p 2 ^ 2 - q 0 ^ 2 - q 2 ^ 2
    let E := p 1 ^ 2 - p 2 ^ 2 - q 0 ^ 2 + q 3 ^ 2
    let G := p 0 ^ 2 - p 3 ^ 2 - q 1 ^ 2 + q 2 ^ 2
    0 ≤ a * (A - B) ^ 2 + b * (A + B) ^ 2 + c * D ^ 2 +
      d * (2 * (A ^ 2 + B ^ 2) - E * G) := by
  change 0 ≤ budgetCost a b c d p q
  change quaternionSq p = 1 at hp
  change quaternionSq q = 1 at hq
  have hid := budgetCost_gram_identity a b c d p q
  rw [hp, hq] at hid
  simp only [sub_self, mul_zero, add_zero] at hid
  have hnonneg : 0 ≤ ∑ j, signedBudgetForm a b c d (signedLeft p j) (signedRight q j) := by
    apply Finset.sum_nonneg
    intro j _
    exact add_nonneg (budgetForm_nonneg ha hb hc hd hcapacity _ _ _ _)
      (budgetForm_nonneg ha hb hc hd hcapacity _ _ _ _)
  linarith only [hid, hnonneg]

end MOC
