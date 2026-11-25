import MOC.FourContactCertificate
import Mathlib.Tactic.Linarith

/-! Threshold selection and rational chart coverage for the normalized T34
Bernstein certificate. -/

namespace MOC

noncomputable section

/-- The finite support threshold selected after normalizing the mixed
coefficient to one. A path with a zero denominator is unavailable. -/
def t34NormalizedThreshold (p b c q : ℝ) : ℝ :=
  let H := 1 + 1 / (b + c)
  let P := if q ≤ p then p else q
  let z := if q ≤ p then b else c
  if 0 < P * z then min H ((P + z) / (P * z)) else H

private theorem t34_threshold_le_cases {a H P z : ℝ} (hP : 0 ≤ P) (hz : 0 ≤ z)
    (ha : (if 0 < P * z then min H ((P + z) / (P * z)) else H) ≤ a) :
    H ≤ a ∨ (0 < P ∧ 0 < z ∧ 1 / P + 1 / z ≤ a) := by
  by_cases hpos : 0 < P * z
  · rw [if_pos hpos] at ha
    rcases min_le_iff.mp ha with hh | hchain
    · exact Or.inl hh
    · have hP' := pos_of_mul_pos_left hpos hz
      have hz' := pos_of_mul_pos_right hpos hP
      have heq : 1 / P + 1 / z = (P + z) / (P * z) := by
        field_simp [hP'.ne', hz'.ne']
        <;> ring
      exact Or.inr ⟨hP', hz', by rw [heq]; exact hchain⟩
  · exact Or.inl (by simpa only [if_neg hpos] using ha)

/-- Nonnegative Bernstein numerators at the selected threshold give the
three-way support bound on a nonnegative root of the radial quadratic. -/
theorem t34Normalized_safe_disjunction_of_bernstein {a p b c q k₀ k₁ k₂ : ℝ}
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hb : 0 ≤ b) (hc : 0 ≤ c) (hq : 0 ≤ q) (hk₀ : 0 < k₀)
    (hroot : k₂ * a ^ 2 + k₁ * a + k₀ = 0)
    (hmiddle : 0 ≤ 2 * k₀ + k₁ * t34NormalizedThreshold p b c q)
    (hend : 0 ≤ k₂ * (t34NormalizedThreshold p b c q) ^ 2 +
      k₁ * t34NormalizedThreshold p b c q + k₀) :
    1 + 1 / (b + c) ≤ a ∨
      (0 < p ∧ 0 < b ∧ 1 / p + 1 / b ≤ a) ∨
      (0 < c ∧ 0 < q ∧ 1 / c + 1 / q ≤ a) := by
  have hA := contact_bernstein_threshold_le_of_root ha hk₀ hmiddle hend hroot
  by_cases horder : q ≤ p
  · rcases t34_threshold_le_cases hp hb
      (by simpa only [t34NormalizedThreshold, if_pos horder] using hA) with hh | hchain
    · exact Or.inl hh
    · exact Or.inr (Or.inl hchain)
  · rcases t34_threshold_le_cases hq hc
      (by simpa only [t34NormalizedThreshold, if_neg horder] using hA) with hh | hchain
    · exact Or.inl hh
    · exact Or.inr (Or.inr ⟨hchain.2.1, hchain.1, by simpa only [add_comm] using hchain.2.2⟩)

/-- The path threshold is smaller exactly when the donor discriminant is
positive and the selected coefficient meets the chart boundary. -/
theorem t34_chain_threshold_le_scalar_iff {M z P : ℝ}
    (hM : 0 < M) (hz : 0 < z) (hP : 0 < P) :
    let V := z * (M + 1) - M
    1 / P + 1 / z ≤ 1 + 1 / M ↔ 0 < V ∧ M * z / V ≤ P := by
  let V := z * (M + 1) - M
  change (1 / P + 1 / z ≤ 1 + 1 / M) ↔ (0 < V ∧ M * z / V ≤ P)
  have hd : 0 < M * P * z := mul_pos (mul_pos hM hP) hz
  have heq : 1 + 1 / M - (1 / P + 1 / z) = (P * V - M * z) / (M * P * z) := by
    dsimp only [V]
    field_simp [hM.ne', hz.ne', hP.ne']
    <;> ring
  constructor
  · intro h
    have hf : 0 ≤ (P * V - M * z) / (M * P * z) := by rw [← heq]; exact sub_nonneg.mpr h
    have hpv : M * z ≤ P * V := by
      simpa only [zero_mul, sub_nonneg] using (le_div_iff₀ hd).mp hf
    have hV := pos_of_mul_pos_right ((mul_pos hM hz).trans_le hpv) hP.le
    exact ⟨hV, (div_le_iff₀ hV).mpr hpv⟩
  · rintro ⟨hV, hpv⟩
    have hnonneg : 0 ≤ P * V - M * z := sub_nonneg.mpr ((div_le_iff₀ hV).mp hpv)
    apply sub_nonneg.mp
    rw [heq]
    exact div_nonneg hnonneg hd.le

/-- The positive discriminant charts recover their parameter from the
donor gap and include the upper endpoint of its range. -/
theorem t34_positive_donor_chart {M z : ℝ}
    (hM : 0 < M) (hzM : z ≤ M) (hV : 0 < z * (M + 1) - M) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ z = M * (1 + M * θ) / (1 + M) ∧
      M * z / (z * (M + 1) - M) = (1 + M * θ) / ((1 + M) * θ) := by
  let V := z * (M + 1) - M
  let θ := V / M ^ 2
  have hθ : 0 < θ := div_pos hV (sq_pos_of_pos hM)
  have hden : 0 < 1 + M := add_pos zero_lt_one hM
  have hθ₁ : θ ≤ 1 := by
    change V / M ^ 2 ≤ 1
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
    dsimp only [V]
    nlinarith only [mul_le_mul_of_nonneg_right hzM (show 0 ≤ M + 1 by linarith only [hM])]
  have hveq : V = M ^ 2 * θ := by
    dsimp only [θ]
    field_simp [hM.ne']
    <;> ring
  have hzEq : z = M * (1 + M * θ) / (1 + M) := by
    apply (eq_div_iff hden.ne').mpr
    dsimp only [V] at hveq
    nlinarith only [hveq]
  refine ⟨θ, hθ, hθ₁, hzEq, ?_⟩
  change M * z / V = _
  rw [hveq, hzEq]
  field_simp [hM.ne', hden.ne', hθ.ne']
  <;> ring

/-- The remaining donor chart covers the nonpositive discriminant range. -/
theorem t34_nonpositive_donor_chart {M z : ℝ}
    (hM : 0 < M) (hz : 0 ≤ z) (hV : z * (M + 1) - M ≤ 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z = M * θ / (1 + M) := by
  have hden : 0 < 1 + M := add_pos zero_lt_one hM
  let θ := z * (1 + M) / M
  refine ⟨θ, div_nonneg (mul_nonneg hz hden.le) hM.le, ?_, ?_⟩
  · apply (div_le_iff₀ hM).mpr
    simpa only [one_mul, add_comm M 1] using sub_nonpos.mp hV
  · dsimp only [θ]
    field_simp [hM.ne', hden.ne']
    <;> ring

/-- A nonnegative polynomial certificate using the two failed-threshold
inequalities excludes a radial root on the corresponding ordered branch. -/
theorem t34Normalized_safe_of_nonnegative_certificate {a p b c radial : ℝ}
    (hp : 0 ≤ p) (hb : 0 ≤ b) (hM : 0 < b + c) (hroot : radial = 0)
    (s : Fin 6 → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hcert :
      let X := 1 + (b + c) - a * (b + c)
      let Y := p + b - a * p * b
      (b + c) * (radial - 1) =
        s 0 + s 1 * X + s 2 * Y + s 3 * X ^ 2 + s 4 * X * Y + s 5 * Y ^ 2) :
    1 + 1 / (b + c) ≤ a ∨ (0 < p ∧ 0 < b ∧ 1 / p + 1 / b ≤ a) := by
  by_contra h
  let M := b + c
  let X := 1 + M - a * M
  let Y := p + b - a * p * b
  have hH : a < 1 + 1 / M := lt_of_not_ge (fun hh => h (Or.inl hh))
  have hscalar : (1 + 1 / M) * M = 1 + M := by
    have hm : M ≠ 0 := hM.ne'
    field_simp [hm]
    <;> ring
  have hX : 0 ≤ X := by
    have hprod := mul_lt_mul_of_pos_right hH hM
    rw [hscalar] at hprod
    exact sub_nonneg.mpr hprod.le
  have hY : 0 ≤ Y := by
    by_cases hpz : 0 < p * b
    · have hp' := pos_of_mul_pos_left hpz hb
      have hb' := pos_of_mul_pos_right hpz hp
      have hthreshold : a < 1 / p + 1 / b :=
        lt_of_not_ge (fun hh => h (Or.inr ⟨hp', hb', hh⟩))
      have heq : (1 / p + 1 / b) * (p * b) = p + b := by
        field_simp [hp'.ne', hb'.ne']
        <;> ring
      have hprod := mul_lt_mul_of_pos_right hthreshold hpz
      rw [heq, ← mul_assoc] at hprod
      exact sub_nonneg.mpr hprod.le
    · have hz : p * b = 0 := le_antisymm (le_of_not_gt hpz) (mul_nonneg hp hb)
      dsimp only [Y]
      rw [mul_assoc, hz, mul_zero, sub_zero]
      exact add_nonneg hp hb
  have hnonneg : 0 ≤
      s 0 + s 1 * X + s 2 * Y + s 3 * X ^ 2 + s 4 * X * Y + s 5 * Y ^ 2 :=
    add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hs 0)
      (mul_nonneg (hs 1) hX)) (mul_nonneg (hs 2) hY)) (mul_nonneg (hs 3) (sq_nonneg X)))
      (mul_nonneg (mul_nonneg (hs 4) hX) hY)) (mul_nonneg (hs 5) (sq_nonneg Y))
  change M * (radial - 1) =
    s 0 + s 1 * X + s 2 * Y + s 3 * X ^ 2 + s 4 * X * Y + s 5 * Y ^ 2 at hcert
  rw [hroot, zero_sub, mul_neg, mul_one] at hcert
  have hm : 0 < M := hM
  linarith only [hcert, hnonneg, hm]

end

end MOC
