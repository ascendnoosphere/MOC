import MOC.ContactCensus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The T18 ratios in the chart with the first right label at infinity. -/

namespace MOC

noncomputable section

/-- For `A = (x, 1, b, z)` and `C = (∞, 0, v, w)`, the pole column
contributes the constant factor one. -/
def fourT18PoleProduct (x b z v w : ℂ) (i : Fin 24) : ℂ :=
  let A : Fin 4 → ℂ := ![x, 1, b, z]
  let σ := (fourPerm i).symm
  A (σ 1) * (A (σ 2) - v) * (A (σ 3) - w)

set_option maxHeartbeats 2000000 in
/-- These identities come from the original matching products. Solving for
the quotient `(z-v)/(z-w)` avoids introducing a pole from the formula for `w`. -/
theorem fourT18_exact_pole_ratios (x b z v w h k l : ℂ)
    (hB : b = 1 + k * (v - 1)) (hZ : z * (v + h - 1) = h * v)
    (hW : (z - v) / (z - w) = (l * (k - 1) * (v + h - 1) + v) / (b + h * (k - 1)))
    (hl : l = (b - w) * (z - v) / ((b - v) * (z - w)))
    (hh : h ≠ 0) (hv : v ≠ 0) (hv1 : v ≠ 1) (hq : k - 1 ≠ 0)
    (ht : v + h - 1 ≠ 0) (hD : b + h * (k - 1) ≠ 0)
    (hbv : b ≠ v) (hzv : z ≠ v) (hzw : z ≠ w) :
    let F := fourT18PoleProduct x b z v w
    let R (i : Fin 24) := F i / F 0
    let q := k - 1
    let D := b + h * q
    let W := (l * q * (v + h - 1) + v) / D
    let e := 1 + h * q
    let L := 1 + h * l * q
    let P := x + h * q
    let A := R 18 - R 2
    let B := R 2 - R 4 + R 10 - R 12 + R 13 + R 18
    R 2 = 1 - k * v / q ∧
    R 5 = h + h * (h - 1) * q * (l - 1) / D ∧
    R 9 = l * x + l * x * (h - 1) / v ∧
    R 10 = (-x / (h * q)) * R 5 ∧
    R 13 = (-h * l * q) * R 14 ∧
    R 14 = -1 / q + (x - 1) / (q * (v - 1)) ∧
    A = b * (l + (x - b) * W / (b - v)) + b / q ∧
    B = l * x + (x - b) * W / (b - v) - b * (x - 1) / (b - v) + R 13 ∧
    e * A = P * R 5 + L * R 14 + (l * x * e + x / q - h * q * (1 + h * l) - 1) ∧
    e * B = -P / (h * q) * R 5 - h * q * L * R 14 + ((x - 1) * (e * (l - 1) - h) + h * (l - 1)) := by
  let F := fourT18PoleProduct x b z v w
  let R (i : Fin 24) := F i / F 0
  let q := k - 1
  let D := b + h * q
  let W := (l * q * (v + h - 1) + v) / D
  let T (y : ℂ) := l + (y - b) * W / (b - v)
  let e := 1 + h * q
  let L := 1 + h * l * q
  let P := x + h * q
  let A := R 18 - R 2
  let B := R 2 - R 4 + R 10 - R 12 + R 13 + R 18
  change R 2 = _ ∧ R 5 = _ ∧ R 9 = _ ∧ R 10 = _ ∧ R 13 = _ ∧ R 14 = _ ∧ A = _ ∧
    B = _ ∧ e * A = _ ∧ e * B = _
  have h0 : F 0 = (b - v) * (z - w) := by
    change 1 * (b - v) * (z - w) = _
    ring
  have h2 : F 2 = b * (1 - v) * (z - w) := rfl
  have h4 : F 4 = b * (z - v) * (1 - w) := rfl
  have h5 : F 5 = z * (b - v) * (1 - w) := rfl
  have h9 : F 9 = x * (1 - v) * (b - w) := rfl
  have h10 : F 10 = x * (z - v) * (1 - w) := rfl
  have h12 : F 12 = b * (x - v) * (z - w) := rfl
  have h13 : F 13 = z * (x - v) * (b - w) := rfl
  have h14 : F 14 = 1 * (x - v) * (z - w) := rfl
  have h18 : F 18 = b * (z - v) * (x - w) := rfl
  have hBv : b - v = q * (v - 1) := by rw [hB]; dsimp only [q]; ring
  have hB1 : 1 - b = -k * (v - 1) := by rw [hB]; ring
  have hZ1 : z * (1 - v) = h * (z - v) := by
    linear_combination -hZ
  have hZv : (z - v) * (v + h - 1) = v * (1 - v) := by
    linear_combination hZ
  have hW' : (z - v) / (z - w) = W := hW
  have hl' : (b - w) * (z - v) = l * ((b - v) * (z - w)) :=
    ((eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hbv) (sub_ne_zero.mpr hzw))).mp hl).symm
  have hT (y : ℂ) : ((z - v) * (y - w)) / ((b - v) * (z - w)) = T y := by
    dsimp only [T]
    rw [← hW']
    calc
      _ = ((b - w) * (z - v)) / ((b - v) * (z - w)) +
          ((y - b) * (z - v)) / ((b - v) * (z - w)) := by ring
      _ = _ := by
        rw [hl', mul_div_cancel_right₀ _ (mul_ne_zero (sub_ne_zero.mpr hbv) (sub_ne_zero.mpr hzw))]
        field_simp [sub_ne_zero.mpr hbv, sub_ne_zero.mpr hzw] <;> ring
  have hT1 : T 1 = l - k * W / q := by
    dsimp only [T]
    rw [hB1, hBv]
    field_simp [hq, sub_ne_zero.mpr hv1] <;> ring
  have hR2 : R 2 = -b / q := by
    dsimp only [R]
    rw [h2, h0, hBv]
    field_simp [hq, sub_ne_zero.mpr hv1, sub_ne_zero.mpr hzw] <;> ring
  have hR4 : R 4 = b * T 1 := by dsimp only [R]; rw [h4, h0, mul_assoc, mul_div_assoc, hT]
  have hR10 : R 10 = x * T 1 := by dsimp only [R]; rw [h10, h0, mul_assoc, mul_div_assoc, hT]
  have hR18 : R 18 = b * T x := by dsimp only [R]; rw [h18, h0, mul_assoc, mul_div_assoc, hT]
  have hR5' : R 5 = -h * q * T 1 := by
    dsimp only [R]
    rw [h5, h0, ← hT]
    have hf : z * (b - v) = -h * q * (z - v) := by
      rw [hBv]
      linear_combination -q * hZ1
    rw [hf]
    ring
  have hR5 : R 5 = h + h * (h - 1) * q * (l - 1) / D := by
    rw [hR5', hT1]
    dsimp only [W]
    field_simp [hD, hq]
    dsimp only [D]
    rw [hB]
    dsimp only [q]
    ring
  have hR9 : R 9 = l * x + l * x * (h - 1) / v := by
    have ht1 : x * (1 - v) * (b - w) * (z - v) =
        (l * x * (1 - v)) * ((b - v) * (z - w)) := by
      linear_combination (x * (1 - v)) * hl'
    have hj : (x * (1 - v) * (b - w)) / ((b - v) * (z - w)) =
        (l * x * (1 - v)) / (z - v) :=
      (div_eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hbv) (sub_ne_zero.mpr hzw))
        (sub_ne_zero.mpr hzv)).mpr ht1
    dsimp only [R]
    rw [h9, h0, hj]
    field_simp [sub_ne_zero.mpr hzv, hv]
    linear_combination -(l * x) * hZv
  have hR12 : R 12 = b * (x - v) / (b - v) := by
    dsimp only [R]
    rw [h12, h0]
    field_simp [sub_ne_zero.mpr hbv, sub_ne_zero.mpr hzw] <;> ring
  have hR14 : R 14 = (x - v) / (b - v) := by
    dsimp only [R]
    rw [h14, h0]
    field_simp [sub_ne_zero.mpr hbv, sub_ne_zero.mpr hzw] <;> ring
  have hR13 : R 13 = (-h * l * q) * R 14 := by
    have hvq : z * (b - v) = -h * q * (z - v) := by
      rw [hBv]
      linear_combination -q * hZ1
    have heq : z * (b - w) = -h * q * l * (z - w) := by
      apply (mul_right_cancel₀ (sub_ne_zero.mpr hbv))
      linear_combination (b - w) * hvq + (-h * q) * hl'
    dsimp only [R]
    rw [h13, h14, h0]
    rw [show z * (x - v) * (b - w) = (z * (b - w)) * (x - v) by ring, heq]
    ring
  have hR14' : R 14 = -1 / q + (x - 1) / (q * (v - 1)) := by
    rw [hR14, hBv]
    field_simp [hq, sub_ne_zero.mpr hv1] <;> ring
  have hA : A = b * T x + b / q := by dsimp only [A]; rw [hR18, hR2]; ring
  have hB' : B = l * x + (x - b) * W / (b - v) - b * (x - 1) / (b - v) + R 13 := by
    dsimp only [B]
    rw [hR2, hR4, hR10, hR12, hR18]
    dsimp only [T]
    rw [hBv]
    field_simp [hq, sub_ne_zero.mpr hv1] <;> ring
  refine ⟨?_, hR5, hR9, ?_, hR13, hR14', hA, hB', ?_, ?_⟩
  · rw [hR2, hB]
    dsimp only [q]
    field_simp [hq] <;> ring
  · rw [hR10, hR5']
    field_simp [hh, hq] <;> ring
  · rw [hA, hR5, hR14']
    dsimp only [T, W, e, L, P]
    rw [hBv]
    field_simp [hq, sub_ne_zero.mpr hv1, hD]
    dsimp only [D]
    rw [hB]
    dsimp only [q]
    ring
  · rw [hB', hR13, hR5, hR14']
    dsimp only [W, e, L, P]
    rw [hBv]
    field_simp [hh, hq, sub_ne_zero.mpr hv1, hD]
    dsimp only [D]
    rw [hB]
    dsimp only [q]
    ring

end

end MOC
