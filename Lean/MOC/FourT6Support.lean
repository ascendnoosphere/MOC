import MOC.FourT6Normalized
import MOC.FourT6Remainder

/-! The order-four support inequality for the full T6 contact face. -/

namespace MOC

set_option maxHeartbeats 5000000 in
/-- All spectral products in the T6 contact face satisfy its lower support
bound. Extra contacts and coincident spectra are allowed. -/
theorem fourT6_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  by_cases h12 : (η * matchingProduct a b (fourPerm 12).symm).re = H
  · exact fourT6_support_of_contact_twelve a b η H hn hc h12 U hU
  have hbound (hh : Holds a b U) := four_lower_support_of_holds a b η H U hh hn
  by_cases ha : Function.Injective a
  swap
  · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inl ha))
  by_cases hb : Function.Injective b
  swap
  · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inr hb))
  by_cases hzero : ∃ i j, a i + b j = 0
  · obtain ⟨i, j, hij⟩ := hzero
    exact hbound (holds_four_of_opposite_entries a b U hU hij)
  by_cases hη : η = 0
  · simpa [hη] using hn 0
  have hab (i j : Fin 4) : a i + b j ≠ 0 := fun hij => hzero ⟨i, j, hij⟩
  obtain ⟨h, r, s, p, v, ρ, hh₀, hh₁, hr₀, hr₁, hs₀, hs₁, hp₀, hp₁, hv₀, hv₁, _, _,
    hD, hg3, hg7, hg10, hg12, hg9, hg18, hg19, hg22⟩ :=
    exists_fourT6_spectral_gap_chart a b η H ha hb hab hη hc
  let g : Fin 24 → ℝ := fun i => (η * matchingProduct a b (fourPerm i).symm).re - H
  let A := h * r - h - r
  let N := Complex.normSq v
  let O := Complex.normSq (v - 1)
  let D := Complex.normSq ((A : ℂ) * v + r)
  let G := Complex.normSq (1 + ((h : ℂ) - 1) * v)
  let K := h * r * (r - 1) / D
  let J := (A * N + r * (2 * v.re - 1)) / D
  let L := r / ((h - 1) * N)
  let M := h * (r - 1) / ((h - 1) * O)
  let E := ρ * s * (p - 1)
  have hminor (hA : 0 ≤ fourT6DefectA g) (hB : 0 ≤ fourT6DefectB g) :
      H ≤ (η * determinantValue a b U).re :=
    fourT6_support_of_nonnegative_defects a b η H hn hc U hU ⟨hA, hB⟩
  have hg (i : Fin 24) : 0 ≤ g i := sub_nonneg.mpr (hn i)
  change 0 < D at hD
  change g 3 = ρ * K * (p - 1) at hg3
  change g 7 = ρ * L * p * (s - 1) at hg7
  change g 10 = ρ * M * p * (s - 1) at hg10
  change g 12 = -ρ * s at hg12
  change g 9 = g 7 + s * g 3 at hg9
  change g 18 = g 7 + E at hg18
  change g 19 = g 3 + E * (1 + J - K) at hg19
  change g 22 = g 3 + E * (1 + h * J - K) at hg22
  have hsK : s * g 3 = E * K := by rw [hg3]; dsimp only [E]; ring
  obtain ⟨hg11, hg15, hg17, hg20, hg21, hg23, hdefA, hdefB⟩ :=
    fourT6_gap_equations_of_chart a b η H hc h J K s E hg9 hsK hg18 hg19 hg22
  have hρ : ρ ≠ 0 := by
    intro he
    apply h12
    apply sub_eq_zero.mp
    change g 12 = 0
    rw [hg12, he, neg_zero, zero_mul]
  have hN : 0 < N := Complex.normSq_pos.mpr hv₀
  have hO : 0 < O := Complex.normSq_pos.mpr (sub_ne_zero.mpr hv₁)
  have hN' : N = v.re ^ 2 + v.im ^ 2 := by simp only [N, Complex.normSq_apply, pow_two]
  have hO' : O = (v.re - 1) ^ 2 + v.im ^ 2 := by
    simp only [O, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, sub_zero, pow_two]
  have hD' : D = (A * v.re + r) ^ 2 + (A * v.im) ^ 2 := by
    simp only [D, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      sub_zero, pow_two]
  have hG' : G = (1 + (h - 1) * v.re) ^ 2 + ((h - 1) * v.im) ^ 2 := by
    simp only [G, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, sub_self, zero_mul, zero_add, add_zero, sub_zero, pow_two]
  have hgeom := fourT6_chart_geometry h r v.re v.im (sub_ne_zero.mpr hh₁)
  dsimp only at hgeom
  rw [← hN', ← hO', ← hD', ← hG'] at hgeom
  obtain ⟨hKJ, hMD, hKD, hI, hLbound, hMbound⟩ := hgeom hN.ne' hO.ne' hD.ne'
  change K + A * J = 1 at hKJ
  change (M - L) * ((h - 1) * N * O) = J * D at hMD
  change K * D = (h - 1) ^ 2 * N * O * (L * M) at hKD
  change (M - L) * K = (h - 1) * J * L * M at hI
  change K + L * (1 + J) = _ at hLbound
  change K + M * (1 + h * J) = _ at hMbound
  have hL₀ : L ≠ 0 := div_ne_zero hr₀ (mul_ne_zero (sub_ne_zero.mpr hh₁) hN.ne')
  have hM₀ : M ≠ 0 := div_ne_zero (mul_ne_zero hh₀ (sub_ne_zero.mpr hr₁))
    (mul_ne_zero (sub_ne_zero.mpr hh₁) hO.ne')
  have hg7p : 0 < g 7 := lt_of_le_of_ne (hg 7) (by
    rw [hg7]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hρ hL₀) hp₀) (sub_ne_zero.mpr hs₁)).symm)
  have hg10p : 0 < g 10 := lt_of_le_of_ne (hg 10) (by
    rw [hg10]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hρ hM₀) hp₀) (sub_ne_zero.mpr hs₁)).symm)
  have hLM : 0 < L * M := by
    have hpos := mul_pos hg7p hg10p
    have hprod : g 7 * g 10 = (ρ * p * (s - 1)) ^ 2 * (L * M) := by rw [hg7, hg10]; ring
    rw [hprod] at hpos
    exact pos_of_mul_pos_right hpos (sq_nonneg _)
  have hK : 0 < K := by
    have hx := mul_pos (mul_pos (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hh₁)) hN) hO) hLM
    rw [← hKD] at hx
    exact pos_of_mul_pos_left hx hD.le
  by_cases hEL : E * L ≤ 0
  · let x := ρ * p * (s - 1)
    have hxL : x * L = g 7 := by rw [hg7]; dsimp only [x]; ring
    have hxM : x * M = g 10 := by rw [hg10]; dsimp only [x]; ring
    obtain ⟨hA, hB⟩ := fourT6_minor_defects_of_chart_sign hN hO hD hL₀ hEL
      (by rw [hxL]; exact hg 7) hMD
      (by rw [hxM, ← hg21]; exact hg 21) (by rw [hxL, ← hg23]; exact hg 23)
    rw [hxM, ← hdefA] at hA
    rw [hxL, ← hdefB] at hB
    exact hminor hA hB
  by_cases hJ₀ : J = 0
  · apply hminor
    · rw [hdefA, hJ₀, mul_zero, add_zero, mul_one, ← hg20]
      exact hg 20
    · rw [hdefB, hJ₀, add_zero, mul_one, ← hg18]
      exact hg 18
  have hg3p : 0 < g 3 := lt_of_le_of_ne (hg 3) (by
    rw [hg3]
    exact (mul_ne_zero (mul_ne_zero hρ hK.ne') (sub_ne_zero.mpr hp₁)).symm)
  have hg12p : 0 < g 12 := lt_of_le_of_ne (hg 12) (by
    rw [hg12]
    exact (mul_ne_zero (neg_ne_zero.mpr hρ) hs₀).symm)
  have hg3c : 0 < ρ * K * (p - 1) := by rwa [← hg3]
  have hg7c : 0 < ρ * L * p * (s - 1) := by rwa [← hg7]
  have hg12c : 0 < -ρ * s := by rwa [← hg12]
  rcases fourT6_positive_cross_cases hK hg3c hg7c hg12c
      (lt_of_not_ge hEL) with ⟨hs, hp, hL, hρ'⟩ | ⟨hs, hs', hp, hp', hL, hρ'⟩ | ⟨hs, hp, _, hρ'⟩
  · -- The case I scale has a negative mixed coefficient.
    let P := (p - 1)⁻¹
    let Q := (-s)⁻¹
    let z := P * Q / ρ
    let R := (1 + P) * (1 + Q)
    let B := (-L) * R
    let C := (-M) * R
    obtain ⟨hP, hQ, hz, hr3, hr7, hr10, hr12, hE⟩ :=
      fourT6_case_one_rescaling ρ s p K L M hρ' hs hp
    have h3' : z * g 3 = K * Q := hg3.symm ▸ hr3
    have h7' : z * g 7 = B := hg7.symm ▸ hr7
    have h10' : z * g 10 = C := hg10.symm ▸ hr10
    have h12' : z * g 12 = P := hg12.symm ▸ hr12
    change z * E = -1 at hE
    have h9' : z * g 9 = B - K := by linear_combination z * hg9 + h7' + z * hsK + K * hE
    have h11' : z * g 11 = C - K := by linear_combination z * hg11 + h10' + z * hsK + K * hE
    have h18' : z * g 18 = B - 1 := by linear_combination z * hg18 + h7' + hE
    have h20' : z * g 20 = C - 1 := by linear_combination z * hg20 + h10' + hE
    have h19' : z * g 19 = K * Q - (1 + J - K) := by
      linear_combination z * hg19 + h3' + (1 + J - K) * hE
    have h22' : z * g 22 = K * Q - (1 + h * J - K) := by
      linear_combination z * hg22 + h3' + (1 + h * J - K) * hE
    have h15' : z * g 15 = P - J := by linear_combination z * hg15 + h12' + J * hE
    have h17' : z * g 17 = P - h * J := by linear_combination z * hg17 + h12' + (h * J) * hE
    have h21' : z * g 21 = C - (1 + J) := by linear_combination z * hg21 + h10' + (1 + J) * hE
    have h23' : z * g 23 = B - (1 + h * J) := by
      linear_combination z * hg23 + h7' + (1 + h * J) * hE
    have hzge (i : Fin 24) {x : ℝ} (hx : z * g i = x) : 0 ≤ x := hx ▸ mul_nonneg hz.le (hg i)
    have hM := ((mul_pos_iff.mp hLM).resolve_left (fun h => hL.not_gt h.1)).2
    have hpJ : J ≤ P := sub_nonneg.mp (hzge 15 h15')
    have hpJ' : h * J ≤ P := sub_nonneg.mp (hzge 17 h17')
    have hqJ : 1 + J - K ≤ K * Q := sub_nonneg.mp (hzge 19 h19')
    have hqJ' : 1 + h * J - K ≤ K * Q := sub_nonneg.mp (hzge 22 h22')
    rcases fourT6_negative_L_region hr₁ hN hO hD
        (Complex.normSq_nonneg (1 + ((h : ℂ) - 1) * v)) hK hL with ⟨houterL, houterM⟩ | ⟨hh, hr, hr'⟩
    · have hKL : K ≤ (-L) * (1 + J) := by
        rw [← hLbound] at houterL
        linarith only [houterL]
      have hKM : K ≤ (-M) * (1 + h * J) := by
        rw [← hMbound] at houterM
        linarith only [houterM]
      have hB := fourT6_outer_capacity hP hQ hK (neg_pos.mpr hL)
        (show 1 + J ≤ 1 + P by linarith only [hpJ])
        (show 1 + J ≤ K * (1 + Q) by linarith only [hqJ]) hKL
      have hC := fourT6_outer_capacity hP hQ hK (neg_pos.mpr hM)
        (show 1 + h * J ≤ 1 + P by linarith only [hpJ'])
        (show 1 + h * J ≤ K * (1 + Q) by linarith only [hqJ']) hKM
      have hA' : z * fourT6DefectA g = C - (1 + h * J) := by
        linear_combination z * hdefA + h10' + (1 + h * J) * hE
      have hB' : z * fourT6DefectB g = B - (1 + J) := by
        linear_combination z * hdefB + h7' + (1 + J) * hE
      exact hminor ((mul_nonneg_iff_of_pos_left hz).mp (hA'.symm ▸ sub_nonneg.mpr hC))
        ((mul_nonneg_iff_of_pos_left hz).mp (hB'.symm ▸ sub_nonneg.mpr hB))
    · rcases lt_or_gt_of_ne hJ₀ with hJ | hJ
      · have hJ' : 0 < h * J := mul_pos_of_neg_of_neg hh hJ
        have hh' : h⁻¹ < 0 := inv_neg''.mpr hh
        have he : h⁻¹ * (h * J) = J := by field_simp [hh₀] <;> ring
        have hle : K ≤ 1 + h * J := by
          have hspl : 1 + h * J - K = r * (h - 1) * J := by
            dsimp only [A] at hKJ
            linear_combination -hKJ
          rw [← sub_nonneg, hspl]
          exact (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hr (by linarith only [hh])) hJ).le
        have hI' := fourT6_swap_geometry hh₀ hI
        have horder := fourT6_donor_order hK (by simpa only [mul_comm] using hLM.le)
          (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hh']) hJ'.le) hI'
        have hcap := fourT6_case_one_capacity_of_gaps hh' hJ' hK hP hQ (neg_pos.mpr hM)
          (neg_le_neg horder) hpJ' hqJ' (sub_nonneg.mp (hzge 23 h23'))
          (fourT6_geometric_budget_identities hI').1
        exact fourT6_support_case_one_swapped a b η H z hc U hU hz hJ' hh' hle
          (sub_nonneg.mp (hzge 20 h20')) (sub_nonneg.mp (hzge 11 h11')) hcap hpJ' hqJ'
          (sub_nonneg.mp (hzge 23 h23'))
          ⟨h3', h10', h11', h7', h12', h20', h22', by simpa only [he] using h19'⟩
      · have hle : K ≤ 1 + J := by
          have hspl : 1 + J - K = (h - 1) * (r - 1) * J := by
            dsimp only [A] at hKJ
            linear_combination -hKJ
          rw [← sub_nonneg, hspl]
          exact (mul_pos (mul_pos_of_neg_of_neg (by linarith only [hh]) (sub_neg.mpr hr')) hJ).le
        have horder := fourT6_donor_order hK hLM.le
          (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hh]) hJ.le) hI
        have hcap := fourT6_case_one_capacity_of_gaps hh hJ hK hP hQ (neg_pos.mpr hL)
          (neg_le_neg horder) hpJ hqJ (sub_nonneg.mp (hzge 21 h21'))
          (fourT6_geometric_budget_identities hI).1
        exact fourT6_support_case_one a b η H z hc U hU hz hJ hh hle
          (sub_nonneg.mp (hzge 18 h18')) (sub_nonneg.mp (hzge 9 h9')) hcap hpJ hqJ
          (sub_nonneg.mp (hzge 21 h21')) ⟨h3', h7', h9', h10', h12', h18', h19', h22'⟩
  · -- The case II scale has a positive mixed coefficient.
    let P := p / (1 - p)
    let Q := s / (1 - s)
    let z := (1 + P) * (1 + Q) / (-ρ)
    let B := M * P
    let C := L * P
    obtain ⟨hP, hQ, hz, hr3, hr7, hr10, hr12, hE⟩ :=
      fourT6_case_two_rescaling ρ s p K L M hρ' hs hs' hp hp'
    have h3' : z * g 3 = K * (1 + Q) := hg3.symm ▸ hr3
    have h7' : z * g 7 = C := hg7.symm ▸ hr7
    have h10' : z * g 10 = B := hg10.symm ▸ hr10
    have h12' : z * g 12 = Q * (1 + P) := hg12.symm ▸ hr12
    change z * E = Q at hE
    have h9' : z * g 9 = C + Q * K := by linear_combination z * hg9 + h7' + z * hsK + K * hE
    have h11' : z * g 11 = B + Q * K := by linear_combination z * hg11 + h10' + z * hsK + K * hE
    have h18' : z * g 18 = C + Q := by linear_combination z * hg18 + h7' + hE
    have h20' : z * g 20 = B + Q := by linear_combination z * hg20 + h10' + hE
    have h19' : z * g 19 = K + Q * (1 + J) := by
      linear_combination z * hg19 + h3' + (1 + J - K) * hE
    have h22' : z * g 22 = K + Q * (1 + h * J) := by
      linear_combination z * hg22 + h3' + (1 + h * J - K) * hE
    have h15' : z * g 15 = Q * (P + (1 + J)) := by linear_combination z * hg15 + h12' + J * hE
    have h17' : z * g 17 = Q * (P + (1 + h * J)) := by
      linear_combination z * hg17 + h12' + (h * J) * hE
    have h21' : z * g 21 = B + Q * (1 + J) := by linear_combination z * hg21 + h10' + (1 + J) * hE
    have h23' : z * g 23 = C + Q * (1 + h * J) := by
      linear_combination z * hg23 + h7' + (1 + h * J) * hE
    have hzge (i : Fin 24) {x : ℝ} (hx : z * g i = x) : 0 ≤ x := hx ▸ mul_nonneg hz.le (hg i)
    have hM := ((mul_pos_iff.mp hLM).resolve_right (fun h => hL.not_gt h.1)).2
    have hminor' (hα : 0 ≤ 1 + J) (hβ : 0 ≤ 1 + h * J) : H ≤ (η * determinantValue a b U).re := by
      have hE' : 0 ≤ E := (mul_nonneg_iff_of_pos_left hz).mp (hE.symm ▸ hQ.le)
      exact hminor (hdefA.symm ▸ add_nonneg (hg 10) (mul_nonneg hE' hβ))
        (hdefB.symm ▸ add_nonneg (hg 7) (mul_nonneg hE' hα))
    rcases fourT6_positive_L_region hN hD hK hL with hh | ⟨hh₀', hh₁'⟩
    · by_cases hβ : 0 ≤ 1 + h * J
      · apply hminor' _ hβ
        apply (mul_nonneg_iff_of_pos_left (zero_lt_one.trans hh)).mp
        have hsplit : h * (1 + J) = (h - 1) + (1 + h * J) := by ring
        rw [hsplit]
        exact add_nonneg (sub_nonneg.mpr hh.le) hβ
      let d := -(1 + h * J)
      have hd : 0 < d := neg_pos.mpr (lt_of_not_ge hβ)
      have hJ : J < 0 := by
        have hprod : h * J < 0 := by linarith only [lt_of_not_ge hβ]
        exact neg_of_mul_neg_right hprod (zero_lt_one.trans hh).le
      have hα' : 0 < d + (1 + J) := by
        have hsplit : d + (1 + J) = (1 - h) * J := by dsimp only [d]; ring
        rw [hsplit]
        exact mul_pos_of_neg_of_neg (sub_neg.mpr hh) hJ
      have hpD : d ≤ P := by
        have h := (mul_nonneg_iff_of_pos_left hQ).mp (hzge 17 h17')
        dsimp only [d]
        linarith only [h]
      have hKd : Q * d ≤ K := by
        have he := hzge 22 h22'
        dsimp only [d]
        linarith only [he]
      have hCd : Q * d ≤ C := by
        have he := hzge 23 h23'
        dsimp only [d]
        linarith only [he]
      have horder := fourT6_donor_order hK hLM.le
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hh.le) hJ.le) hI
      have hcap := fourT6_case_two_capacity_of_gaps hd hα' hK hM horder hQ hpD hKd hCd
        (fourT6_geometric_budget_identities hI).2
      exact fourT6_support_case_two a b η H z hc U hU hz hQ hd hα' hpD hKd hCd hcap
        ⟨h3', h7', h9', h10', h12', h18', h19', by dsimp only [d]; convert h22' using 1 <;> ring⟩
    · by_cases hα : 0 ≤ 1 + J
      · apply hminor' hα
        have hsplit : 1 + h * J = (1 - h) + h * (1 + J) := by ring
        rw [hsplit]
        exact add_nonneg (sub_nonneg.mpr hh₁'.le) (mul_nonneg hh₀'.le hα)
      let d := -(1 + J)
      have hd : 0 < d := neg_pos.mpr (lt_of_not_ge hα)
      have hJ : J < 0 := by linarith only [lt_of_not_ge hα]
      have hα' : 0 < d + (1 + h * J) := by
        have hsplit : d + (1 + h * J) = (h - 1) * J := by dsimp only [d]; ring
        rw [hsplit]
        exact mul_pos_of_neg_of_neg (sub_neg.mpr hh₁') hJ
      have hpD : d ≤ P := by
        have h := (mul_nonneg_iff_of_pos_left hQ).mp (hzge 15 h15')
        dsimp only [d]
        linarith only [h]
      have hKd : Q * d ≤ K := by
        have he := hzge 19 h19'
        dsimp only [d]
        linarith only [he]
      have hBd : Q * d ≤ B := by
        have he := hzge 21 h21'
        dsimp only [d]
        linarith only [he]
      have hi : 1 < h⁻¹ := by
        rw [← one_div]
        exact (lt_div_iff₀ hh₀').mpr (by simpa only [one_mul] using hh₁')
      have hI' := fourT6_swap_geometry hh₀ hI
      have horder := fourT6_donor_order hK (by simpa only [mul_comm] using hLM.le)
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hi.le)
          (mul_nonpos_of_nonneg_of_nonpos hh₀'.le hJ.le)) hI'
      have he : h⁻¹ * (h * J) = J := by field_simp [hh₀] <;> ring
      have hIcap : M * (K - L * (2 * d + (1 + h * J))) = L * (K - M * d) := by
        simpa only [he, d] using (fourT6_geometric_budget_identities hI').2
      have hcap := fourT6_case_two_capacity_of_gaps hd hα' hK hL horder hQ hpD hKd hBd hIcap
      exact fourT6_support_case_two_swapped a b η H z hc U hU hz hQ hd hα' hpD hKd hBd hcap
        ⟨h3', h10', h11', h7', h12', h20', h22', by dsimp only [d]; convert h19' using 1 <;> ring⟩
  · apply hminor
    · rw [hdefA]
      exact (fourT6_case_three_defects hρ' hs hp hK (hg 7) (hg 10)
        (by rw [← hg3, ← hg19]; exact hg 19) (by rw [← hg3, ← hg22]; exact hg 22)).1
    · rw [hdefB]
      exact (fourT6_case_three_defects hρ' hs hp hK (hg 7) (hg 10)
        (by rw [← hg3, ← hg19]; exact hg 19) (by rw [← hg3, ← hg22]; exact hg 22)).2

end MOC
