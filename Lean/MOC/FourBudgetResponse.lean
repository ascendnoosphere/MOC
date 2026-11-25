import MOC.FourBudgetGram
import MOC.MixedBound

/-! The squared-entry and squared-minor response of the four-coefficient
certificate on a quaternion rotation. -/

open Matrix

namespace MOC

private theorem vector_zero {α : Type*} (a b c d : α) : ![a, b, c, d] 0 = a := rfl
private theorem vector_one {α : Type*} (a b c d : α) : ![a, b, c, d] 1 = b := rfl
private theorem vector_two {α : Type*} (a b c d : α) : ![a, b, c, d] 2 = c := rfl
private theorem vector_three {α : Type*} (a b c d : α) : ![a, b, c, d] 3 = d := rfl

/-- The four-budget inequality on the two entries and three signed minors
of the order-four quaternion rotation. These are the T5 ray coordinates. -/
theorem quaternionRotation_four_budget_nonneg {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcapacity : d ^ 2 * (a + b + c + d) ≤ a * b * (c - d))
    (p q : Fin 4 → ℝ) (hp : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 = 1)
    (hq : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1) :
    let O := quaternionRotation p q
    let v := O 0 1 * O 2 3 - O 0 3 * O 2 1
    let s := O 0 0 * O 2 2 - O 0 2 * O 2 0
    let t := O 0 2 * O 1 3 - O 0 3 * O 1 2
    0 ≤ a * O 0 3 ^ 2 + b * O 3 0 ^ 2 + c * v ^ 2 +
      d * (O 0 3 ^ 2 + O 3 0 ^ 2 + s ^ 2 - t ^ 2) := by
  let O := quaternionRotation p q
  let A := p 0 * q 3 + p 3 * q 0
  let B := p 1 * q 2 - p 2 * q 1
  let D := p 0 ^ 2 + p 2 ^ 2 - q 0 ^ 2 - q 2 ^ 2
  let E := p 1 ^ 2 - p 2 ^ 2 - q 0 ^ 2 + q 3 ^ 2
  let G := p 0 ^ 2 - p 3 ^ 2 - q 1 ^ 2 + q 2 ^ 2
  have hentry₀ : O 0 3 = -(A - B) := by
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      vector_zero, vector_one, vector_two, vector_three, A, B]
    ring
  have hentry₁ : O 3 0 = A + B := by
    simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
      vector_zero, vector_one, vector_two, vector_three, A, B]
    ring
  have hp₁ : p 1 ^ 2 + p 3 ^ 2 = 1 - (p 0 ^ 2 + p 2 ^ 2) := by linarith only [hp]
  have hq₁ : q 1 ^ 2 + q 3 ^ 2 = 1 - (q 0 ^ 2 + q 2 ^ 2) := by linarith only [hq]
  have hminor₀ : O 0 1 * O 2 3 - O 0 3 * O 2 1 = -D := by
    calc
      _ = (p 1 ^ 2 + p 3 ^ 2) * (q 0 ^ 2 + q 2 ^ 2) -
          (p 0 ^ 2 + p 2 ^ 2) * (q 1 ^ 2 + q 3 ^ 2) := by
        simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vector_zero, vector_one, vector_two, vector_three]
        ring
      _ = _ := by rw [hp₁, hq₁]; dsimp only [D]; ring
  have hminor₁ : O 0 0 * O 2 2 - O 0 2 * O 2 0 = (G - E) / 2 := by
    calc
      _ = (p 0 ^ 2 + p 2 ^ 2) * (q 0 ^ 2 + q 2 ^ 2) -
          (p 1 ^ 2 + p 3 ^ 2) * (q 1 ^ 2 + q 3 ^ 2) := by
        simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vector_zero, vector_one, vector_two, vector_three]
        ring
      _ = p 0 ^ 2 + p 2 ^ 2 + q 0 ^ 2 + q 2 ^ 2 - 1 := by rw [hp₁, hq₁]; ring
      _ = _ := by dsimp only [E, G]; linarith only [hp, hq]
  have hminor₂ : O 0 2 * O 1 3 - O 0 3 * O 1 2 = (E + G) / 2 := by
    have hp₂ : p 0 ^ 2 + p 1 ^ 2 = 1 - (p 2 ^ 2 + p 3 ^ 2) := by linarith only [hp]
    have hq₂ : q 0 ^ 2 + q 1 ^ 2 = 1 - (q 2 ^ 2 + q 3 ^ 2) := by linarith only [hq]
    calc
      _ = (p 0 ^ 2 + p 1 ^ 2) * (q 2 ^ 2 + q 3 ^ 2) -
          (p 2 ^ 2 + p 3 ^ 2) * (q 0 ^ 2 + q 1 ^ 2) := by
        simp only [O, quaternionRotation, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply,
          vector_zero, vector_one, vector_two, vector_three]
        ring
      _ = q 2 ^ 2 + q 3 ^ 2 - (p 2 ^ 2 + p 3 ^ 2) := by rw [hp₂, hq₂]; ring
      _ = _ := by dsimp only [E, G]; linarith only [hp, hq]
  have h := quaternion_four_budget_nonneg ha hb hc hd hcapacity p q hp hq
  change 0 ≤ a * (A - B) ^ 2 + b * (A + B) ^ 2 + c * D ^ 2 +
    d * (2 * (A ^ 2 + B ^ 2) - E * G) at h
  change 0 ≤ a * O 0 3 ^ 2 + b * O 3 0 ^ 2 +
    c * (O 0 1 * O 2 3 - O 0 3 * O 2 1) ^ 2 + d *
      (O 0 3 ^ 2 + O 3 0 ^ 2 + (O 0 0 * O 2 2 - O 0 2 * O 2 0) ^ 2 -
        (O 0 2 * O 1 3 - O 0 3 * O 1 2) ^ 2)
  rw [hminor₀, hminor₁, hminor₂, hentry₀, hentry₁]
  convert h using 1 <;> ring

end MOC
