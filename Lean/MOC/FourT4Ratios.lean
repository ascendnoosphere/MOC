import MOC.FourT4Chart
import MOC.FourT4Capacity

/-! The exact matching-ratio identities used in the positive T4 capacity
argument. All denominators are controlled by the distinct pole chart. -/

namespace MOC

private def t4RatioIndices : Fin 9 → Fin 24 := ![0, 2, 6, 9, 10, 13, 14, 16, 19]

private theorem t4RatioProductValues (z x w v t : ℂ) (i : Fin 9) :
    fourT4PoleProduct z x w v t (t4RatioIndices i) =
      (![v * (z - w) * (x - t * v), (v - 1) * (z - w) * (x - t * v),
        w * (z - v) * (x - t * v), (z - v) * (x - w) * (t * v - 1),
        t * v * (z - v) * (1 - w), -w * (x - v) * (t * v - 1),
        v * (t * v - x) * (w - 1), t * v * (x - v) * (1 - w),
        w * (x - v) * (z - t * v)] : Fin 9 → ℂ) i := by
  have h : ∀ k : Fin 9,
      let σ := (fourPerm (t4RatioIndices k)).symm
      σ 0 = (![0, 0, 1, 3, 2, 1, 2, 2, 1] : Fin 9 → Fin 4) k ∧
      σ 1 = (![1, 2, 0, 0, 0, 3, 1, 3, 3] : Fin 9 → Fin 4) k ∧
      σ 3 = (![3, 3, 3, 2, 1, 2, 3, 1, 0] : Fin 9 → Fin 4) k := by
    decide +kernel
  obtain ⟨h₀, h₁, h₃⟩ := h i
  dsimp only [fourT4PoleProduct]
  rw [h₀, h₁, h₃]
  fin_cases i <;> simp [Matrix.cons_val] <;> ring_nf <;> simp

set_option maxHeartbeats 1500000 in
/-- The algebraic T4 source equations and the quadratic ratios at indices
19 and `2 - 13` are exact identities of the original projective products. -/
theorem fourT4_exact_pole_ratios (x t r u : ℝ) (z w v : ℂ)
    (hv : v ≠ 0) (hzw : z ≠ w) (ht : t ≠ 0) :
    let F := fourT4PoleProduct z x w v t
    let D := v * (z - w)
    let R (i : Fin 24) := (F i - F 0) / D
    let y := x - 1
    let h := 1 - t
    let H := h + u
    let E := H * (1 - t * x) - h * r * y
    let J := H * (1 - t * x) + h * y
    let f := (t : ℂ) * v - x
    let T := (t : ℂ) * v - 1
    let W := -(r : ℂ) * f + (u : ℂ) * T
    let Z := f * T - v * W
    f ≠ 0 → T ≠ 0 → W ≠ 0 → Z ≠ 0 →
    z = (r : ℂ) * v * f / Z → w = -f * ((r : ℂ) + 1 - t * v) / W →
    let Q := t4QuadraticEval (t4ShiftedDen x t r u) f
    Q ≠ 0 ∧ R 2 = f / v ∧ R 6 = (r : ℂ) * f / T ∧
      R 10 = (t : ℂ) * v * u / f - x ∧
      R 9 = (y : ℂ) * R 10 + ((y ^ 2 - r * y + u : ℝ) : ℂ) ∧
      R 2 - R 13 = t4QuadraticEval (t4ShiftedNumD x t r u) f / Q ∧
      R 19 = t4QuadraticEval (t4ShiftedNumB x t r u) f / Q ∧
      R 16 - (h : ℂ) * R 10 + (t : ℂ) * (R 19 + (R 2 - R 13)) =
        ((t * (t + u - 1) : ℝ) : ℂ) ∧
      (E : ℂ) * R 14 - ((t * y * H : ℝ) : ℂ) * R 19 + (J : ℂ) * (R 2 - R 13) =
        (((h * x - y) * u ^ 2 + h ^ 2 * x * (u + y) - r * h * x * H : ℝ) : ℂ) := by
  intro F D R y h H E J f T W Z hf hT hW hZ hz hw Q
  let k := (r : ℂ) + 1 - t * v
  let Q₀ := v * W + k * f
  have hZW : z - w = f * T * Q₀ / (Z * W) := by
    rw [hz, hw]
    field_simp [hZ, hW]
    dsimp only [Z, Q₀, k, T]
    ring
  have hQ₀ : Q₀ ≠ 0 := by
    intro hzero
    apply sub_ne_zero.mpr hzw
    rw [hZW, hzero, mul_zero, zero_div]
  have hQ : Q = (t : ℂ) * Q₀ := by
    dsimp only [Q, Q₀, t4QuadraticEval, t4ShiftedDen, W, k, T, f]
    push_cast
    ring
  have hQnz : Q ≠ 0 := by rw [hQ]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) hQ₀
  have hF₀ : F 0 = -f * D := by
    have hh : F 0 = v * (z - w) * (x - (t : ℂ) * v) := t4RatioProductValues z x w v t 0
    rw [hh]
    dsimp only [f, D]
    ring
  have hF₂ : F 2 = (v - 1) * (z - w) * (x - (t : ℂ) * v) := t4RatioProductValues z x w v t 1
  have hF₆ : F 6 = w * (z - v) * (x - (t : ℂ) * v) := t4RatioProductValues z x w v t 2
  have hF₉ : F 9 = (z - v) * (x - w) * ((t : ℂ) * v - 1) := t4RatioProductValues z x w v t 3
  have hF₁₀ : F 10 = (t : ℂ) * v * (z - v) * (1 - w) := t4RatioProductValues z x w v t 4
  have hF₁₃ : F 13 = -w * (x - v) * ((t : ℂ) * v - 1) := t4RatioProductValues z x w v t 5
  have hF₁₄ : F 14 = v * ((t : ℂ) * v - x) * (w - 1) := t4RatioProductValues z x w v t 6
  have hF₁₆ : F 16 = (t : ℂ) * v * (x - v) * (1 - w) := t4RatioProductValues z x w v t 7
  have hF₁₉ : F 19 = w * (x - v) * (z - (t : ℂ) * v) := t4RatioProductValues z x w v t 8
  let Dn := v * f * T * Q₀
  have hDn : Dn ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hv hf) hT) hQ₀
  have hD : D = Dn / (Z * W) := by
    change v * (z - w) = _
    rw [hZW]
    dsimp only [Dn]
    ring
  have hDne : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hz' : z = (r : ℂ) * v * f / Z := hz
  have hw' : w = -f * k / W := hw
  have hR (i : Fin 24) : R i = F i / D + f := by
    dsimp only [R]
    rw [hF₀, neg_mul, sub_neg_eq_add, add_div, mul_div_cancel_right₀ _ hDne]
  have hRnorm (i : Fin 24) (a b : ℂ) (hb : b ≠ 0)
      (hnum : F i * (Z * W) * b = a * Dn) : R i = a / b + f := by
    rw [hR, hD, div_div_eq_mul_div, (div_eq_div_iff hDn hb).mpr hnum]
  have hzv : z - v = v * Q₀ / Z := by
    rw [hz']
    field_simp [hZ]
    dsimp only [Q₀, Z, k, T]
    ring
  have hxw : (x : ℂ) - w = ((x : ℂ) * W + f * k) / W := by
    rw [hw']
    field_simp [hW] <;> ring
  have hw₁ : w - 1 = (f - u) * T / W := by
    rw [hw']
    field_simp [hW]
    dsimp only [W, k, T]
    ring
  have h₁w : 1 - w = (u - f) * T / W := by
    have heq : 1 - w = -(w - 1) := by ring
    rw [heq, hw₁]
    field_simp [hW]
    ring
  have hztv : z - (t : ℂ) * v = v * T * ((t : ℂ) * v * u - ((r : ℂ) + t) * f) / Z := by
    rw [hz']
    field_simp [hZ]
    dsimp only [Z, W, T]
    ring
  have hR₂ : R 2 = f / v := by
    dsimp only [R]
    rw [hF₂, hF₀]
    change ((v - 1) * (z - w) * (x - (t : ℂ) * v) - -f * (v * (z - w))) /
      (v * (z - w)) = _
    field_simp [hv, sub_ne_zero.mpr hzw]
    dsimp only [f]
    ring
  have hR₆ : R 6 = (r : ℂ) * f / T := by
    rw [hRnorm 6 (f * k) T hT (by
      rw [hF₆, hzv, hw', show (x : ℂ) - (t : ℂ) * v = -f by dsimp only [f]; ring]
      field_simp [hZ, hW] <;> dsimp only [Dn] <;> ring)]
    field_simp [hT]
    dsimp only [k, T]
    ring
  have hR₁₀ : R 10 = (t : ℂ) * v * u / f - x := by
    rw [hRnorm 10 ((t : ℂ) * v * (u - f)) f hf (by
      rw [hF₁₀, hzv, h₁w]
      field_simp [hZ, hW] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf]
    dsimp only [f]
    ring
  have hR₉ : R 9 = (y : ℂ) * R 10 + ((y ^ 2 - r * y + u : ℝ) : ℂ) := by
    rw [hR₁₀, hRnorm 9 ((x : ℂ) * W + f * k) f hf (by
      rw [hF₉, hzv, hxw]
      change (v * Q₀ / Z * (((x : ℂ) * W + f * k) / W) * T) * (Z * W) * f = _
      field_simp [hZ, hW] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf]
    dsimp only [W, k, T, f, y]
    push_cast
    ring
  have hR₁₄ : R 14 = (f - u) * Z / Q₀ + f := by
    apply hRnorm 14 _ _ hQ₀
    rw [hF₁₄, hw₁]
    change (v * f * ((f - u) * T / W)) * (Z * W) * Q₀ = _
    field_simp [hW] <;> dsimp only [Dn] <;> ring
  have hR₁₆ : R 16 = (t : ℂ) * (x - v) * (u - f) * Z / (f * Q₀) + f := by
    apply hRnorm 16 _ _ (mul_ne_zero hf hQ₀)
    rw [hF₁₆, h₁w]
    field_simp [hW] <;> dsimp only [Dn] <;> ring
  let N := W * ((r : ℂ) * x + ((h : ℂ) * y - r) * v) + k * f * (h : ℂ) * y
  let M := k * (x - v) * (((r : ℂ) + t) * f - (t : ℂ) * v * u) + f * Q₀
  have hRD : R 2 - R 13 = N / Q₀ := by
    have h13 : R 13 = k * (x - v) * Z / (v * Q₀) + f := by
      apply hRnorm 13 _ _ (mul_ne_zero hv hQ₀)
      rw [hF₁₃, hw']
      change (-(-f * k / W) * (x - v) * T) * (Z * W) * (v * Q₀) = _
      field_simp [hW] <;> dsimp only [Dn] <;> ring
    rw [hR₂, h13]
    field_simp [hv, hQ₀]
    dsimp only [N, Q₀, Z, k, T, f, h, y]
    push_cast
    ring
  have hRB : R 19 = M / Q₀ := by
    rw [hRnorm 19 (k * (x - v) * (((r : ℂ) + t) * f - (t : ℂ) * v * u)) Q₀ hQ₀ (by
      rw [hF₁₉, hztv, hw']
      field_simp [hZ, hW] <;> dsimp only [Dn] <;> ring)]
    field_simp [hQ₀]
  have hN : t4QuadraticEval (t4ShiftedNumD x t r u) f = (t : ℂ) * N := by
    dsimp only [N, t4QuadraticEval, t4ShiftedNumD, Q₀, Z, W, k, T, f, h, y]
    push_cast
    ring
  have hM : t4QuadraticEval (t4ShiftedNumB x t r u) f = (t : ℂ) * M := by
    dsimp only [M, t4QuadraticEval, t4ShiftedNumB, t4ShiftedDen, Q₀, Z, W, k, T, f, h, y]
    push_cast
    ring
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine ⟨hQnz, hR₂, hR₆, hR₁₀, hR₉, ?_, ?_, ?_, ?_⟩
  · rw [hRD, hN, hQ]
    field_simp [ht', hQ₀] <;> ring
  · rw [hRB, hM, hQ]
    field_simp [ht', hQ₀] <;> ring
  · rw [hR₁₆, hR₁₀, hRD, hRB]
    field_simp [hf, hQ₀]
    dsimp only [N, M, Q₀, Z, W, k, T, f, h, y]
    push_cast
    ring
  · rw [hR₁₄, hRD, hRB]
    field_simp [hQ₀]
    dsimp only [N, M, Q₀, Z, W, k, T, f, E, J, H, h, y]
    push_cast
    ring

end MOC
