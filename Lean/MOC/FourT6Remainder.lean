import MOC.FourT6Capacity
import MOC.FourT6Minor
import MOC.FourTwoBudgetMinor

/-! The two quadratic certificates on the nonminor T6 charts. -/

namespace MOC

open BigOperators

noncomputable section

private def t6RemainderRows : Fin 12 → Finset (Fin 4) :=
  ![{0, 1}, {0, 3}, {0}, {1}, {1, 3}, {1, 2}, {0, 3}, {0, 1}, {0, 2}, {0, 3}, {0}, {3}]

private def t6RemainderColumns : Fin 12 → Finset (Fin 4) :=
  ![{2, 3}, {1, 2}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 3}, {1, 3}, {0, 1}, {2}, {1}]

private def t6RemainderSupports : Fin 12 → Finset (Fin 24) :=
  ![{16, 17, 22, 23}, {7, 10, 13, 16}, {12, 13, 14, 15, 16, 17}, {4, 5, 10, 11, 16, 17},
    {1, 3, 20, 22}, {1, 4, 15, 17}, {12, 14, 18, 20}, {10, 11, 20, 21}, {7, 9, 18, 23},
    {3, 5, 9, 11}, {12, 13, 14, 15, 16, 17}, {3, 5, 13, 16, 19, 22}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem t6RemainderSupports_spec : ∀ (k : Fin 12) (i : Fin 24),
    i ∈ t6RemainderSupports k ↔
      (t6RemainderColumns k).map (fourPerm i).symm.toEmbedding = t6RemainderRows k := by
  decide +kernel

private def t6RemainderWeights (x y d : ℝ) (w : Fin 6 → ℝ) : Fin 12 → ℝ :=
  ![x, y, d, d, d, -d, w 0, w 1, w 2, w 3, w 4, w 5]

private theorem t6_support_of_remainder (a b : Fin 4 → ℂ) (η : ℂ) (H z : ℝ)
    (hz : 0 < z) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (h0 : (η * matchingProduct a b (fourPerm 0).symm).re = H)
    {x y d : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : 0 ≤ d) (hcap : d ^ 2 ≤ x * y)
    (w : Fin 6 → ℝ) (hw : ∀ k, 0 ≤ w k)
    (he : ∀ i : Fin 24, z * ((η * matchingProduct a b (fourPerm i).symm).re - H) =
      ∑ k, if i ∈ t6RemainderSupports k then t6RemainderWeights x y d w k else 0) :
    H ≤ (η * determinantValue a b U).re := by
  let I := t6RemainderRows
  let J := t6RemainderColumns
  let W := t6RemainderWeights x y d w
  have hdecomp (i : Fin 24) : (η * matchingProduct a b (fourPerm i).symm).re - H =
      ∑ k, if (J k).map (fourPerm i).symm.toEmbedding = I k then W k / z else 0 := by
    apply (mul_left_cancel₀ hz.ne')
    rw [he, Finset.mul_sum]
    simp_rw [show ∀ k : Fin 12, (J k).map (fourPerm i).symm.toEmbedding = I k ↔
        i ∈ t6RemainderSupports k from fun k => (t6RemainderSupports_spec k i).symm]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · rw [mul_comm z, div_mul_cancel₀ _ hz.ne']
    · rw [mul_zero]
  have hresponse := four_gap_eq_minor_decomposition a b η H U hU 0 h0 I J (fun k => W k / z) hdecomp
  have hscaled : z * ((η * determinantValue a b U).re - H) =
      ∑ k, W k * subsetMinorSq U (I k) (J k) := by
    rw [hresponse, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_assoc, mul_comm z, div_mul_cancel₀ _ hz.ne']
  have hmix := four_two_budget_minor_nonneg hx hy hd hcap U hU
  have h₀ := mul_nonneg (hw 0) (subsetMinorSq_nonneg U {0, 3} {2, 3})
  have h₁ := mul_nonneg (hw 1) (subsetMinorSq_nonneg U {0, 1} {1, 3})
  have h₂ := mul_nonneg (hw 2) (subsetMinorSq_nonneg U {0, 2} {1, 3})
  have h₃ := mul_nonneg (hw 3) (subsetMinorSq_nonneg U {0, 3} {0, 1})
  have h₄ := mul_nonneg (hw 4) (subsetMinorSq_nonneg U {0} {2})
  have h₅ := mul_nonneg (hw 5) (subsetMinorSq_nonneg U {3} {1})
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left hz).mp
  rw [hscaled]
  norm_num [W, I, J, t6RemainderWeights, t6RemainderRows, t6RemainderColumns, Fin.sum_univ_succ]
  dsimp only at hmix
  nlinarith only [hmix, h₀, h₁, h₂, h₃, h₄, h₅]

private theorem t6_scaled_gap_profile (a b : Fin 4 → ℂ) (η : ℂ) (H z : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    ∀ i, z * g i = t6GapProfile (fun j => z * g j) i := by
  intro g i
  calc
    z * g i = z * t6GapProfile g i :=
      congrArg (z * ·) (fourT6_spectral_gap_profile a b η H hc i)
    _ = _ := by fin_cases i <;> simp [t6GapProfile, Matrix.cons_val] <;> ring

set_option maxHeartbeats 2000000 in
private theorem t6_case_one_gap_eq (K J h p q B C e : ℝ) (g : Fin 24 → ℝ)
    (h3 : g 3 = K * q) (h7 : g 7 = B) (h9 : g 9 = B - K) (h10 : g 10 = C)
    (h12 : g 12 = p) (h13 : g 13 = K * q + K + p - J)
    (h16 : g 16 = K * q + K + p - h * J) (h18 : g 18 = B - 1) (i : Fin 24) :
    t6GapProfile g i =
      ∑ k, if i ∈ t6RemainderSupports k then
        t6RemainderWeights (e - h * J) (e + 1) (J - e)
          ![e, C - (1 + J), B - e - 1, e + 1 - K, p - J, K * q - (1 + J - K)] k
      else 0 := by
  fin_cases i <;>
    simp (config := { decide := true }) [t6GapProfile, t6RemainderWeights, t6RemainderSupports,
      Fin.sum_univ_succ, Matrix.cons_val, h3, h7, h9, h10, h12, h13, h16, h18] <;> ring

set_option maxHeartbeats 2000000 in
/-- Case I in the T6 support proof, with the two donors and the positive
ordinary remainder written in the same matching labels. -/
theorem fourT6_support_case_one (a b : Fin 4 → ℂ) (η : ℂ) (H z : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (hz : 0 < z)
    {K J h p q B C : ℝ} (hJ : 0 < J) (hh : h < 0) (hK : K ≤ 1 + J)
    (hB₁ : 1 ≤ B) (hBK : K ≤ B) (hBA : (1 + J) ^ 2 / (1 + (2 - h) * J) ≤ B)
    (hP : J ≤ p) (hQ : 1 + J - K ≤ K * q) (hC : 1 + J ≤ C)
    (hprofile : let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      z * g 3 = K * q ∧ z * g 7 = B ∧ z * g 9 = B - K ∧ z * g 10 = C ∧
      z * g 12 = p ∧ z * g 18 = B - 1 ∧
      z * g 19 = K * q - (1 + J - K) ∧ z * g 22 = K * q - (1 + h * J - K)) :
    H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  let e := max 0 (max (K - 1) (J * (J + h) / (1 + (2 - h) * J)))
  let w : Fin 6 → ℝ := ![e, C - (1 + J), B - e - 1, e + 1 - K, p - J, K * q - (1 + J - K)]
  obtain ⟨he, heJ, heB, hKe, heh, hcap⟩ := fourT6_case_one_budget hJ hh hK hB₁ hBK hBA
  change 0 ≤ e at he
  change e ≤ J at heJ
  change e + 1 ≤ B at heB
  change K ≤ e + 1 at hKe
  change 0 ≤ e - h * J at heh
  change (J - e) ^ 2 ≤ (e - h * J) * (e + 1) at hcap
  obtain ⟨h3, h7, h9, h10, h12, h18, h19, h22⟩ := hprofile
  obtain ⟨_, _, _, h19', _, _, h22', _⟩ := fourT6_gap_relations a b η H hc
  have h13 : z * g 13 = K * q + K + p - J := by
    have heq := congrArg (z * ·) h19'
    change z * g 19 = z * (-g 7 - g 12 + g 13 + g 18) at heq
    linear_combination h19 - heq + h7 + h12 - h18
  have h16 : z * g 16 = K * q + K + p - h * J := by
    have heq := congrArg (z * ·) h22'
    change z * g 22 = z * (-g 7 - g 12 + g 16 + g 18) at heq
    linear_combination h22 - heq + h7 + h12 - h18
  refine t6_support_of_remainder a b η H z hz U hU (hc 0 (by decide)) heh
    (by linarith only [he]) (sub_nonneg.mpr heJ) hcap w ?_ ?_
  · intro k
    fin_cases k <;>
      (dsimp only [w]
       linarith only [he, hC, heB, hKe, hP, hQ, heJ, hB₁])
  · intro i
    rw [t6_scaled_gap_profile a b η H z hc i]
    fin_cases i <;>
      simp (config := { decide := true }) [t6GapProfile, t6RemainderWeights, t6RemainderSupports, w,
        Fin.sum_univ_succ, Matrix.cons_val, h3, h7, h9, h10, h12, h13, h16, h18] <;> ring

/-- Permutation indices after exchanging the two finite anchor labels of T6. -/
def fourT6SwapIndex : Fin 24 → Fin 24 :=
  ![2, 4, 0, 5, 1, 3, 8, 10, 6, 11, 7, 9, 14, 16, 12, 17, 13, 15, 20, 22, 18, 23, 19, 21]

set_option maxRecDepth 10000 in
private theorem t6_swap_indices : ∀ i : Fin 24,
    (fourPerm i).symm.trans (Equiv.swap 1 2) = (fourPerm (fourT6SwapIndex i)).symm := by
  decide +kernel

/-- Swapping anchor labels in the first spectrum permutes the matching products. -/
theorem fourT6_matching_swap12 (a b : Fin 4 → ℂ) (i : Fin 24) :
    matchingProduct (a ∘ Equiv.swap 1 2) b (fourPerm i).symm =
      matchingProduct a b (fourPerm (fourT6SwapIndex i)).symm := by
  unfold matchingProduct
  apply Finset.prod_congr rfl
  intro j _
  change a (((fourPerm i).symm.trans (Equiv.swap 1 2)) j) + b j =
    a ((fourPerm (fourT6SwapIndex i)).symm j) + b j
  rw [t6_swap_indices i]

/-- The six T6 contact labels survive the anchor swap. -/
theorem fourT6_contacts_swap12 (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    ∀ i ∈ fourT6ContactIndices,
      (η * matchingProduct (a ∘ Equiv.swap 1 2) b (fourPerm i).symm).re = H := by
  have h : ∀ i ∈ fourT6ContactIndices, fourT6SwapIndex i ∈ fourT6ContactIndices := by decide +kernel
  intro i hi
  rw [fourT6_matching_swap12]
  exact hc _ (h i hi)

/-- The anchor swap sends each gap used in the quadratic certificates to
the stated entry of the original contact profile. -/
theorem fourT6_gaps_swap12 (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    let g' (i : Fin 24) := (η * matchingProduct (a ∘ Equiv.swap 1 2) b (fourPerm i).symm).re - H
    g' 3 = g 3 ∧ g' 7 = g 10 ∧ g' 9 = g 11 ∧ g' 10 = g 7 ∧ g' 12 = g 12 ∧
      g' 18 = g 20 ∧ g' 19 = g 22 ∧ g' 22 = g 19 := by
  intro g g'
  have hm (i : Fin 24) : g' i = g (fourT6SwapIndex i) := by
    dsimp only [g, g']
    rw [fourT6_matching_swap12]
  have h5 : g 5 = g 3 := fourT6_spectral_gap_profile a b η H hc 5
  have h14 : g 14 = g 12 := fourT6_spectral_gap_profile a b η H hc 14
  exact ⟨(hm 3).trans h5, hm 7, hm 9, hm 10, (hm 12).trans h14, hm 18, hm 19, hm 22⟩

set_option maxHeartbeats 2000000 in
/-- Case II in the T6 support proof. The row swap exchanges the donor
positions, and multiplication by the positive chart parameter clears the
coefficients in the remainder identity. -/
theorem fourT6_support_case_two (a b : Fin 4 → ℂ) (η : ℂ) (H z : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (hz : 0 < z)
    {K P α p q B C : ℝ} (hq : 0 < q) (hP : 0 < P) (hα : 0 < P + α)
    (hp : P ≤ p) (hK : q * P ≤ K) (hC : q * P ≤ C)
    (hB : P ^ 2 / (2 * P + α) ≤ B / q)
    (hprofile : let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      z * g 3 = K * (1 + q) ∧ z * g 7 = C ∧ z * g 9 = C + q * K ∧ z * g 10 = B ∧
      z * g 12 = q * (1 + p) ∧ z * g 18 = C + q ∧
      z * g 19 = K + q * α ∧ z * g 22 = K - q * P) :
    H ≤ (η * determinantValue a b U).re := by
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  let e := P ^ 2 / (2 * P + α)
  let w : Fin 6 → ℝ :=
    ![q * (e + 1), C - q * P, B - q * e, q * (e + K), q * (p - P), K - q * P]
  obtain ⟨he, heα, heP, heB, hcap⟩ := fourT6_case_two_budget hP hα hB
  change 0 ≤ e at he
  change 0 ≤ e + α at heα
  change e ≤ P at heP
  change e ≤ B / q at heB
  change (P - e) ^ 2 = e * (e + α) at hcap
  have hcap' : (q * (P - e)) ^ 2 ≤ (q * (e + α)) * (q * e) := by
    rw [mul_pow, hcap]
    apply le_of_eq
    ring
  obtain ⟨h3, h7, h9, h10, h12, h18, h19, h22⟩ := hprofile
  obtain ⟨_, _, _, h19', _, _, h22', _⟩ := fourT6_gap_relations a b η H hc
  have h13 : z * g 13 = K + q * α + q * p := by
    have heq := congrArg (z * ·) h19'
    change z * g 19 = z * (-g 7 - g 12 + g 13 + g 18) at heq
    linear_combination h19 - heq + h7 + h12 - h18
  have h16 : z * g 16 = K - q * P + q * p := by
    have heq := congrArg (z * ·) h22'
    change z * g 22 = z * (-g 7 - g 12 + g 16 + g 18) at heq
    linear_combination h22 - heq + h7 + h12 - h18
  let r : FourPerm := Equiv.swap 1 2
  let s : FourPerm := Equiv.refl _
  have hperm (i : Fin 24) : matchingProduct (a ∘ r) (b ∘ s) (fourPerm i).symm =
      matchingProduct a b (fourPerm (fourT6SwapIndex i)).symm := fourT6_matching_swap12 a b i
  have h0 : (η * matchingProduct (a ∘ r) (b ∘ s) (fourPerm 0).symm).re = H := by
    rw [hperm]
    exact hc 2 (by decide)
  have hw (k : Fin 6) : 0 ≤ w k := by
    fin_cases k <;> norm_num [w]
    · exact mul_nonneg hq.le (by linarith only [he])
    · exact sub_nonneg.mpr hC
    · have hb := (le_div_iff₀ hq).mp heB
      linarith only [hb]
    · have hk := (mul_pos hq hP).le.trans hK
      exact mul_nonneg hq.le (add_nonneg he hk)
    · exact mul_nonneg hq.le (sub_nonneg.mpr hp)
    · exact sub_nonneg.mpr hK
  rw [← determinantValue_reindex r s a b U]
  refine t6_support_of_remainder (a ∘ r) (b ∘ s) η H z hz (U.submatrix r s)
    (unitary_reindex r s hU) h0 (mul_nonneg hq.le heα) (mul_nonneg hq.le he)
    (mul_nonneg hq.le (sub_nonneg.mpr heP)) hcap' w hw ?_
  intro i
  rw [hperm, t6_scaled_gap_profile a b η H z hc (fourT6SwapIndex i)]
  fin_cases i <;>
    simp (config := { decide := true }) [fourT6SwapIndex, t6GapProfile, t6RemainderWeights,
      t6RemainderSupports, w, Fin.sum_univ_succ, Matrix.cons_val,
      h3, h7, h9, h10, h12, h13, h16, h18] <;> ring

/-- The Case I certificate after exchanging the anchor labels. -/
theorem fourT6_support_case_one_swapped (a b : Fin 4 → ℂ) (η : ℂ) (H z : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (hz : 0 < z)
    {K J h p q B C : ℝ} (hJ : 0 < J) (hh : h < 0) (hK : K ≤ 1 + J)
    (hB₁ : 1 ≤ B) (hBK : K ≤ B) (hBA : (1 + J) ^ 2 / (1 + (2 - h) * J) ≤ B)
    (hP : J ≤ p) (hQ : 1 + J - K ≤ K * q) (hC : 1 + J ≤ C)
    (hprofile : let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      z * g 3 = K * q ∧ z * g 10 = B ∧ z * g 11 = B - K ∧ z * g 7 = C ∧
      z * g 12 = p ∧ z * g 20 = B - 1 ∧
      z * g 22 = K * q - (1 + J - K) ∧ z * g 19 = K * q - (1 + h * J - K)) :
    H ≤ (η * determinantValue a b U).re := by
  let r : FourPerm := Equiv.swap 1 2
  let s : FourPerm := Equiv.refl _
  rw [← determinantValue_reindex r s a b U]
  refine fourT6_support_case_one (a ∘ r) (b ∘ s) η H z (fourT6_contacts_swap12 a b η H hc)
    (U.submatrix r s) (unitary_reindex r s hU) hz hJ hh hK hB₁ hBK hBA hP hQ hC ?_
  obtain ⟨h3, h7, h9, h10, h12, h18, h19, h22⟩ := fourT6_gaps_swap12 a b η H hc
  simpa only [h3, h7, h9, h10, h12, h18, h19, h22] using hprofile

/-- The Case II certificate after exchanging the anchor labels. -/
theorem fourT6_support_case_two_swapped (a b : Fin 4 → ℂ) (η : ℂ) (H z : ℝ)
    (hc : ∀ i ∈ fourT6ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) (hz : 0 < z)
    {K P α p q B C : ℝ} (hq : 0 < q) (hP : 0 < P) (hα : 0 < P + α)
    (hp : P ≤ p) (hK : q * P ≤ K) (hC : q * P ≤ C)
    (hB : P ^ 2 / (2 * P + α) ≤ B / q)
    (hprofile : let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
      z * g 3 = K * (1 + q) ∧ z * g 10 = C ∧ z * g 11 = C + q * K ∧ z * g 7 = B ∧
      z * g 12 = q * (1 + p) ∧ z * g 20 = C + q ∧
      z * g 22 = K + q * α ∧ z * g 19 = K - q * P) :
    H ≤ (η * determinantValue a b U).re := by
  let r : FourPerm := Equiv.swap 1 2
  let s : FourPerm := Equiv.refl _
  rw [← determinantValue_reindex r s a b U]
  refine fourT6_support_case_two (a ∘ r) (b ∘ s) η H z (fourT6_contacts_swap12 a b η H hc)
    (U.submatrix r s) (unitary_reindex r s hU) hz hq hP hα hp hK hC hB ?_
  obtain ⟨h3, h7, h9, h10, h12, h18, h19, h22⟩ := fourT6_gaps_swap12 a b η H hc
  simpa only [h3, h7, h9, h10, h12, h18, h19, h22] using hprofile

end

end MOC
