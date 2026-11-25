import MOC.FourT6Spectral

/-! Sign splits for the supported T6 projective gap profile. -/

namespace MOC

/-- The second set of projected gap equations follows by linear
reconstruction from the eight T6 source equations. -/
theorem fourT6_gap_equations_of_chart (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (h J K s E : ℝ) :
    let g : Fin 24 → ℝ := fun i => (η * matchingProduct a b (fourPerm i).symm).re - H
    g 9 = g 7 + s * g 3 → s * g 3 = E * K →
    g 18 = g 7 + E → g 19 = g 3 + E * (1 + J - K) →
    g 22 = g 3 + E * (1 + h * J - K) →
    g 11 = g 10 + s * g 3 ∧ g 15 = g 12 + E * J ∧ g 17 = g 12 + E * (h * J) ∧
    g 20 = g 10 + E ∧ g 21 = g 10 + E * (1 + J) ∧ g 23 = g 7 + E * (1 + h * J) ∧
    fourT6DefectA g = g 10 + E * (1 + h * J) ∧
    fourT6DefectB g = g 7 + E * (1 + J) := by
  intro g h9 hK h18 h19 h22
  obtain ⟨hr11, hr15, hr17, hr19, hr20, hr21, hr22, hr23⟩ := fourT6_gap_relations a b η H hc
  unfold fourT6DefectA fourT6DefectB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hr11 + h9
  · linear_combination hr15 - hr19 + h9 + h19 - h18 + hK
  · linear_combination hr17 - hr22 + h9 + h22 - h18 + hK
  · linear_combination hr20 + h18
  · linear_combination hr21 - hr19 + h9 + h19 + hK
  · linear_combination hr23 - hr22 + h9 + h22 + hK
  · linear_combination -hr22 + h9 + h22 + hK
  · linear_combination -hr19 + h9 + h19 + hK

/-- Both defects are nonnegative when the sign of the chart cross product
allows comparison with the supported gaps at indices 21 and 23. -/
theorem fourT6_minor_defects_of_chart_sign {J h E L M N O D x : ℝ}
    (hN : 0 < N) (hO : 0 < O) (hD : 0 < D)
    (hL : L ≠ 0) (hEL : E * L ≤ 0) (hx : 0 ≤ x * L)
    (hgeom : (M - L) * ((h - 1) * N * O) = J * D)
    (h21 : 0 ≤ x * M + E * (1 + J)) (h23 : 0 ≤ x * L + E * (1 + h * J)) :
    0 ≤ x * M + E * (1 + h * J) ∧ 0 ≤ x * L + E * (1 + J) := by
  let A := x * M + E * (1 + h * J)
  let B := x * L + E * (1 + J)
  let u := x * M + E * (1 + J)
  let v := x * L + E * (1 + h * J)
  let W := x * L * J ^ 2 * D / (N * O)
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact div_nonneg (mul_nonneg (mul_nonneg hx (sq_nonneg _)) hD.le) (mul_pos hN hO).le
  change 0 ≤ A ∧ 0 ≤ B
  apply fourT6_minor_defects_of_sign h21 h23 hL hEL hW
  · dsimp only [A, B, u, v]
    ring
  · dsimp only [A, B, u, v, W]
    field_simp [hN.ne', hO.ne']
    linear_combination -E * x * L ^ 2 * J * hgeom

/-- A positive cross product leaves three possible sign patterns. -/
theorem fourT6_positive_cross_cases {ρ s p K L : ℝ}
    (hK : 0 < K) (hg3 : 0 < ρ * K * (p - 1))
    (hg7 : 0 < ρ * L * p * (s - 1)) (hg12 : 0 < -ρ * s)
    (hEL : 0 < (ρ * s * (p - 1)) * L) :
    (s < 0 ∧ 1 < p ∧ L < 0 ∧ 0 < ρ) ∨
    (0 < s ∧ s < 1 ∧ 0 < p ∧ p < 1 ∧ 0 < L ∧ ρ < 0) ∨
    (1 < s ∧ p < 0 ∧ 0 < L ∧ ρ < 0) := by
  have hρp : 0 < ρ * (p - 1) := by
    apply (mul_pos_iff_of_pos_right hK).mp
    convert hg3 using 1 <;> ring
  have hρs : ρ * s < 0 := by linarith only [hg12]
  rcases mul_pos_iff.mp hρp with ⟨hρ, hp⟩ | ⟨hρ, hp⟩
  · have hs : s < 0 := neg_of_mul_neg_right hρs hρ.le
    have hE : ρ * s * (p - 1) < 0 := mul_neg_of_neg_of_pos hρs hp
    have hL := ((mul_pos_iff.mp hEL).resolve_left (fun h => hE.not_gt h.1)).2
    exact Or.inl ⟨hs, sub_pos.mp hp, hL, hρ⟩
  · have hs : 0 < s := pos_of_mul_neg_right hρs hρ.le
    have hE : 0 < ρ * s * (p - 1) := mul_pos_of_neg_of_neg hρs hp
    have hL : 0 < L := (mul_pos_iff_of_pos_left hE).mp hEL
    have hpS : p * (s - 1) < 0 := by
      have hprod : 0 < (ρ * L) * (p * (s - 1)) := by simpa only [mul_assoc] using hg7
      exact ((mul_pos_iff.mp hprod).resolve_left
        (fun h => (mul_neg_of_neg_of_pos hρ hL).not_gt h.1)).2
    rcases mul_neg_iff.mp hpS with ⟨hp₀, hs₁⟩ | ⟨hp₀, hs₁⟩
    · exact Or.inr (Or.inl ⟨hs, sub_neg.mp hs₁, hp₀, sub_neg.mp hp, hL, hρ⟩)
    · exact Or.inr (Or.inr ⟨sub_pos.mp hs₁, hp₀, hL, hρ⟩)

/-- The third positive-cross chart already has positive ordinary defects. -/
theorem fourT6_case_three_defects {ρ s p K J h g₇ g₁₀ : ℝ}
    (hρ : ρ < 0) (hs : 1 < s) (hp : p < 0) (hK : 0 < K)
    (hg₇ : 0 ≤ g₇) (hg₁₀ : 0 ≤ g₁₀)
    (h19 : 0 ≤ ρ * K * (p - 1) + ρ * s * (p - 1) * (1 + J - K))
    (h22 : 0 ≤ ρ * K * (p - 1) + ρ * s * (p - 1) * (1 + h * J - K)) :
    0 ≤ g₁₀ + ρ * s * (p - 1) * (1 + h * J) ∧
      0 ≤ g₇ + ρ * s * (p - 1) * (1 + J) := by
  have hp₁ : p - 1 < 0 := by linarith only [hp]
  have hg : 0 < ρ * K * (p - 1) := mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hρ hK) hp₁
  have hbase : ρ * K * (p - 1) * (1 - s) < 0 :=
    mul_neg_of_pos_of_neg hg (sub_neg.mpr hs)
  constructor
  · have hsplit : ρ * K * (p - 1) + ρ * s * (p - 1) * (1 + h * J - K) =
        ρ * K * (p - 1) * (1 - s) + ρ * s * (p - 1) * (1 + h * J) := by ring
    rw [hsplit] at h22
    have hpos : 0 < ρ * s * (p - 1) * (1 + h * J) := by linarith only [hbase, h22]
    exact add_nonneg hg₁₀ hpos.le
  · have hsplit : ρ * K * (p - 1) + ρ * s * (p - 1) * (1 + J - K) =
        ρ * K * (p - 1) * (1 - s) + ρ * s * (p - 1) * (1 + J) := by ring
    rw [hsplit] at h19
    have hpos : 0 < ρ * s * (p - 1) * (1 + J) := by linarith only [hbase, h19]
    exact add_nonneg hg₇ hpos.le

end MOC
