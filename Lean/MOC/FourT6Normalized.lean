import MOC.FourT6Signs

/-! The capacity bounds in the two nonminor T6 cases. -/

namespace MOC

/-- In the outer chart, the positive capacities give the ordinary minor
inequalities. -/
theorem fourT6_outer_capacity {p q K α l : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hK : 0 < K) (hl : 0 < l)
    (hA : α ≤ 1 + p) (hQ : α ≤ K * (1 + q)) (hL : K ≤ l * α) :
    α ≤ l * ((1 + p) * (1 + q)) := by
  have hα : 0 < α := by
    have h := hK.trans_le hL
    rw [mul_comm] at h
    exact pos_of_mul_pos_left h hl.le
  have hq' : 0 ≤ 1 + q := by positivity
  have hkq := hQ.trans (mul_le_mul_of_nonneg_right hL hq')
  have hlq : 1 ≤ l * (1 + q) := by
    apply (mul_le_mul_right hα).mp
    calc
      1 * α = α := one_mul _
      _ ≤ l * α * (1 + q) := hkq
      _ = l * (1 + q) * α := by ring
  calc
    α ≤ 1 + p := hA
    _ = (1 + p) * 1 := (mul_one _).symm
    _ ≤ (1 + p) * (l * (1 + q)) := mul_le_mul_of_nonneg_left hlq (by positivity)
    _ = _ := by ring

/-- The inner chart of case I satisfies the single quadratic capacity
required by the T6 remainder. -/
theorem fourT6_case_one_capacity_of_gaps {h J K p q l m : ℝ}
    (hh : h < 0) (hJ : 0 < J) (hK : 0 < K) (hp : 0 < p) (hq : 0 < q)
    (hl : 0 < l) (hlm : l ≤ m)
    (hpJ : J ≤ p) (hqJ : 1 + J - K ≤ K * q)
    (hmJ : 1 + J ≤ m * ((1 + p) * (1 + q)))
    (hI : m * (K - l * (1 + (2 - h) * J)) = l * (K - m * (1 + J))) :
    (1 + J) ^ 2 / (1 + (2 - h) * J) ≤ l * ((1 + p) * (1 + q)) := by
  let R := (1 + p) * (1 + q)
  let α := 1 + J
  let T := 1 + (2 - h) * J
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hT : 0 < T := by
    have hh' : 0 < 2 - h := by linarith only [hh]
    dsimp only [T]
    positivity
  have hq' : α ≤ K * (1 + q) := by dsimp only [α]; linarith only [hqJ]
  have hp' : α ≤ 1 + p := by dsimp only [α]; linarith only [hpJ]
  have hbound : α ^ 2 ≤ K * R := by
    calc
      _ = α * α := pow_two _
      _ ≤ (1 + p) * (K * (1 + q)) :=
        mul_le_mul hp' hq' hα (by positivity)
      _ = K * R := by dsimp only [R]; ring
  exact fourT6_geometric_budget hK hl hlm hα hT hbound hmJ hI

/-- The two positive gap constraints in case II furnish both inputs to
the geometric budget bound. -/
theorem fourT6_case_two_capacity_of_gaps {P α K L M p q : ℝ}
    (hP : 0 < P) (hα : 0 < P + α) (hK : 0 < K) (hM : 0 < M)
    (hML : M ≤ L) (hq : 0 < q) (hp : P ≤ p) (hKP : q * P ≤ K)
    (hL : q * P ≤ L * p)
    (hI : L * (K - M * (2 * P + α)) = M * (K - L * P)) :
    P ^ 2 / (2 * P + α) ≤ (M * p) / q := by
  let R := p / q
  have hT : 0 < 2 * P + α := by linarith only [hP, hα]
  have hKR : P ^ 2 ≤ K * R := by
    dsimp only [R]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hq).mpr
    calc
      P ^ 2 * q = (q * P) * P := by ring
      _ ≤ K * P := mul_le_mul_of_nonneg_right hKP hP.le
      _ ≤ K * p := mul_le_mul_of_nonneg_left hp hK.le
  have hLR : P ≤ L * R := by
    dsimp only [R]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hq).mpr
    simpa only [mul_comm P q] using hL
  simpa only [R, mul_div_assoc] using
    fourT6_geometric_budget hK hM hML hP.le hT hKR hLR hI

/-- The negative-`L` T6 chart has either two outer donor bounds or an
inner chart with negative `h` and `r` between zero and one. -/
theorem fourT6_negative_L_region {h r N O D G : ℝ}
    (hr : r ≠ 1) (hN : 0 < N) (hO : 0 < O) (hD : 0 < D) (hG : 0 ≤ G) :
    let K := h * r * (r - 1) / D
    let L := r / ((h - 1) * N)
    0 < K → L < 0 →
    (r ^ 2 * (r - 1) * G / ((h - 1) * N * D) ≤ 0 ∧
      h * r * (r - 1) ^ 2 * G / ((h - 1) * O * D) ≤ 0) ∨
    (h < 0 ∧ 0 < r ∧ r < 1) := by
  intro K L hK hL
  have hKr : 0 < h * r * (r - 1) := (div_pos_iff_of_pos_right hD).mp hK
  rcases div_neg_iff.mp hL with ⟨hr₀, hd⟩ | ⟨hr₀, hd⟩
  · have hh₁ := sub_neg.mp (neg_of_mul_neg_left hd hN.le)
    rcases lt_or_gt_of_ne hr with hr₁ | hr₁
    · have hh₀ : h < 0 := by
        have hx := ((mul_pos_iff.mp hKr).resolve_left (fun h => (sub_neg.mpr hr₁).not_gt h.2)).1
        exact neg_of_mul_neg_left hx hr₀.le
      exact Or.inr ⟨hh₀, hr₀, hr₁⟩
    · have hx := ((mul_pos_iff.mp hKr).resolve_right (fun h => (sub_pos.mpr hr₁).not_lt h.2)).1
      apply Or.inl
      exact ⟨div_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hr₁.le)) hG)
        (mul_nonpos_of_nonpos_of_nonneg hd.le hD.le),
        div_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hx.le (sq_nonneg _)) hG)
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh₁.le) hO.le) hD.le)⟩
  · have hh₁ := sub_pos.mp ((mul_pos_iff_of_pos_right hN).mp hd)
    have hh₀ : 0 < h := zero_lt_one.trans hh₁
    have hr₁ : r - 1 ≤ 0 := by linarith only [hr₀]
    apply Or.inl
    exact ⟨div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hr₁) hG)
      (mul_nonneg hd.le hD.le),
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hh₀.le hr₀.le) (sq_nonneg _)) hG)
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr hh₁.le) hO.le) hD.le)⟩

/-- A positive `L` chart has a positive `h`. Swapping the anchors
therefore makes either `h` or its reciprocal greater than one. -/
theorem fourT6_positive_L_region {h r N D : ℝ} (hN : 0 < N) (hD : 0 < D)
    (hK : 0 < h * r * (r - 1) / D) (hL : 0 < r / ((h - 1) * N)) :
    1 < h ∨ (0 < h ∧ h < 1) := by
  have hKr := (div_pos_iff_of_pos_right hD).mp hK
  rcases div_pos_iff.mp hL with ⟨_, hd⟩ | ⟨hr, hd⟩
  · exact Or.inl (sub_pos.mp ((mul_pos_iff_of_pos_right hN).mp hd))
  · have hr₁ : r - 1 < 0 := by linarith only [hr]
    have hx := ((mul_pos_iff.mp hKr).resolve_left (fun h => hr₁.not_gt h.2)).1
    exact Or.inr ⟨pos_of_mul_neg_left hx hr.le, sub_neg.mp (neg_of_mul_neg_left hd hN.le)⟩

/-- Rescaling case I replaces the cross coefficient by minus one. -/
theorem fourT6_case_one_rescaling (ρ s p K L M : ℝ) (hρ : 0 < ρ) (hs : s < 0) (hp : 1 < p) :
    let P := (p - 1)⁻¹
    let Q := (-s)⁻¹
    let z := P * Q / ρ
    let R := (1 + P) * (1 + Q)
    0 < P ∧ 0 < Q ∧ 0 < z ∧
    z * (ρ * K * (p - 1)) = K * Q ∧ z * (ρ * L * p * (s - 1)) = (-L) * R ∧
    z * (ρ * M * p * (s - 1)) = (-M) * R ∧ z * (-ρ * s) = P ∧
    z * (ρ * s * (p - 1)) = -1 := by
  intro P Q z R
  have hP : 0 < P := inv_pos.mpr (sub_pos.mpr hp)
  have hQ : 0 < Q := inv_pos.mpr (neg_pos.mpr hs)
  have hz : 0 < z := div_pos (mul_pos hP hQ) hρ
  have hp₀ : p - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hs₀ : -s ≠ 0 := neg_ne_zero.mpr hs.ne
  refine ⟨hP, hQ, hz, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [P, Q, z, R] <;>
    field_simp [hp₀, hs₀, hs.ne, hρ.ne'] <;> ring

/-- Rescaling case II replaces the cross coefficient by a positive split
ratio and preserves the two donor scales. -/
theorem fourT6_case_two_rescaling (ρ s p K L M : ℝ) (hρ : ρ < 0)
    (hs : 0 < s) (hs₁ : s < 1) (hp : 0 < p) (hp₁ : p < 1) :
    let P := p / (1 - p)
    let Q := s / (1 - s)
    let z := (1 + P) * (1 + Q) / (-ρ)
    0 < P ∧ 0 < Q ∧ 0 < z ∧
    z * (ρ * K * (p - 1)) = K * (1 + Q) ∧ z * (ρ * L * p * (s - 1)) = L * P ∧
    z * (ρ * M * p * (s - 1)) = M * P ∧ z * (-ρ * s) = Q * (1 + P) ∧
    z * (ρ * s * (p - 1)) = Q := by
  intro P Q z
  have hP : 0 < P := div_pos hp (sub_pos.mpr hp₁)
  have hQ : 0 < Q := div_pos hs (sub_pos.mpr hs₁)
  have hz : 0 < z := div_pos (mul_pos (by positivity) (by positivity)) (neg_pos.mpr hρ)
  have hp₀ : 1 - p ≠ 0 := sub_ne_zero.mpr hp₁.ne'
  have hs₀ : 1 - s ≠ 0 := sub_ne_zero.mpr hs₁.ne'
  refine ⟨hP, hQ, hz, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp only [P, Q, z] <;>
    field_simp [hp₀, hs₀, hρ.ne] <;> ring

/-- The anchors may be interchanged in the cross-product identity without
recomputing the projective chart. -/
theorem fourT6_swap_geometry {h J K L M : ℝ} (hh : h ≠ 0)
    (hI : (M - L) * K = (h - 1) * J * L * M) :
    (L - M) * K = (h⁻¹ - 1) * (h * J) * M * L := by
  field_simp [hh]
  linear_combination -h * hI

/-- The sign of the cross product orders the two donors. -/
theorem fourT6_donor_order {h J K L M : ℝ} (hK : 0 < K) (hLM : 0 ≤ L * M)
    (hcross : (h - 1) * J ≤ 0)
    (hI : (M - L) * K = (h - 1) * J * L * M) : M ≤ L := by
  have hnonpos : (M - L) * K ≤ 0 := by
    rw [hI, mul_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg hcross hLM
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_left hnonpos hK)

end MOC
