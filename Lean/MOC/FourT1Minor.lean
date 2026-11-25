import MOC.ContactRectangle
import MOC.FourMatchingRelations
import MOC.FourCoincidence
import MOC.Support
import MOC.TwoExceptions

/-! The entry-face support inequality and its application to Zheng's case T1. -/

namespace MOC

open BigOperators

noncomputable section

/-- The six contacts of paper case T1 in lexicographic order. -/
def fourT1ContactIndices : Finset (Fin 24) := {0, 1, 2, 3, 6, 7}

private def entryMinorRows : Fin 9 → Finset (Fin 4) :=
  ![{0}, {0}, {0}, {0, 1}, {0, 1}, {0, 1}, {0, 2}, {0, 2}, {0, 2}]

private def entryMinorColumns : Fin 9 → Finset (Fin 4) :=
  ![{1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2}, {1, 3}, {2, 3}]

private def entryMinorSupport : Fin 9 → Finset ℕ :=
  ![{6, 7, 8, 9, 10, 11}, {12, 13, 14, 15, 16, 17}, {18, 19, 20, 21, 22, 23},
    {8, 9, 14, 15}, {10, 11, 20, 21}, {16, 17, 22, 23}, {6, 11, 12, 17},
    {7, 9, 18, 23}, {13, 15, 19, 21}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem entryMinorSupport_spec (k : Fin 9) (i : Fin 24) :
    i.val ∈ entryMinorSupport k ↔ (entryMinorColumns k).map (fourPerm i).symm.toEmbedding =
      entryMinorRows k := by
  fin_cases k <;> fin_cases i <;> decide

private def entryMinorCoefficients (g : Fin 24 → ℝ) : Fin 9 → ℝ :=
  ![g 7 + g 8 - g 9,
    g 12 - g 6 + g 7 + g 8 - g 9,
    g 18 + g 8 - g 9,
    -g 7 + g 9,
    g 10 - g 7 - g 8 + g 9,
    -g 12 + g 16 + g 6 - g 7 - g 8 + g 9,
    g 6 - g 7 - g 8 + g 9,
    -g 8 + g 9,
    -g 12 + g 13 + g 6 - g 7 - g 8 + g 9]

private def entryGapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![0, 0, 0, 0, 0, 0, g 6, g 7, g 8, g 9, g 10,
    g 10 + g 6 - g 7 - g 8 + g 9,
    g 12,
    g 13,
    g 12 - g 6 + g 8,
    g 13 - g 7 + g 9,
    g 16,
    g 16 + g 6 - g 7 - g 8 + g 9,
    g 18,
    -g 12 + g 13 + g 18 + g 6 - g 7,
    g 10 + g 18 - g 7,
    g 10 - g 12 + g 13 + g 18 + g 6 - 2 * g 7 - g 8 + g 9,
    -g 12 + g 16 + g 18 + g 6 - g 7,
    -g 12 + g 16 + g 18 + g 6 - g 7 - g 8 + g 9]

set_option maxHeartbeats 3000000 in
private theorem entryGapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (h0 : fourMatchingEvaluation m 0 = H) (h1 : fourMatchingEvaluation m 1 = H)
    (h2 : fourMatchingEvaluation m 2 = H) (h3 : fourMatchingEvaluation m 3 = H)
    (h4 : fourMatchingEvaluation m 4 = H)
    (i : Fin 24) :
    let g := fun j => fourMatchingEvaluation m j - H
    g i = entryGapProfile g i := by
  let g (j : Fin 24) := fourMatchingEvaluation m j - H
  change g i = entryGapProfile g i
  dsimp only [fourMatchingEvaluation, Matrix.cons_val] at h0 h1 h2 h3 h4
  fin_cases i
  · change g 0 = entryGapProfile g 0
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0
  · change g 1 = entryGapProfile g 1
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1
  · change g 2 = entryGapProfile g 2
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h2
  · change g 3 = entryGapProfile g 3
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h3
  · change g 4 = entryGapProfile g 4
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h4
  · change g 5 = entryGapProfile g 5
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0 - h1 - h2 + h3 + h4
  · change g 6 = entryGapProfile g 6
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 7 = entryGapProfile g 7
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 8 = entryGapProfile g 8
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 9 = entryGapProfile g 9
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 10 = entryGapProfile g 10
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 11 = entryGapProfile g 11
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 12 = entryGapProfile g 12
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 13 = entryGapProfile g 13
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 14 = entryGapProfile g 14
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h0 - h2
  · change g 15 = entryGapProfile g 15
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 - h3
  · change g 16 = entryGapProfile g 16
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 17 = entryGapProfile g 17
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + h2 - h3
  · change g 18 = entryGapProfile g 18
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 19 = entryGapProfile g 19
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 20 = entryGapProfile g 20
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 - h4
  · change g 21 = entryGapProfile g 21
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination h1 + h2 - h3 - h4
  · change g 22 = entryGapProfile g 22
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + h2 - h4
  · change g 23 = entryGapProfile g 23
    dsimp only [g, entryGapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -h0 + h1 + 2 * h2 - h3 - h4

set_option maxHeartbeats 3000000 in
private theorem entryGapProfile_eq_minorSum (g : Fin 24 → ℝ) (i : Fin 24) :
    entryGapProfile g i = ∑ k : Fin 9, if i.val ∈ entryMinorSupport k then
      entryMinorCoefficients g k else 0 := by
  let rhs (i : ℕ) := ∑ k : Fin 9, if i ∈ entryMinorSupport k then entryMinorCoefficients g k else 0
  change entryGapProfile g i = rhs i.val
  fin_cases i
  case' «0» => change 0 = rhs 0
  case' «1» => change 0 = rhs 1
  case' «2» => change 0 = rhs 2
  case' «3» => change 0 = rhs 3
  case' «4» => change 0 = rhs 4
  case' «5» => change 0 = rhs 5
  case' «6» => change g 6 = rhs 6
  case' «7» => change g 7 = rhs 7
  case' «8» => change g 8 = rhs 8
  case' «9» => change g 9 = rhs 9
  case' «10» => change g 10 = rhs 10
  case' «11» => change g 10 + g 6 - g 7 - g 8 + g 9 = rhs 11
  case' «12» => change g 12 = rhs 12
  case' «13» => change g 13 = rhs 13
  case' «14» => change g 12 - g 6 + g 8 = rhs 14
  case' «15» => change g 13 - g 7 + g 9 = rhs 15
  case' «16» => change g 16 = rhs 16
  case' «17» => change g 16 + g 6 - g 7 - g 8 + g 9 = rhs 17
  case' «18» => change g 18 = rhs 18
  case' «19» => change -g 12 + g 13 + g 18 + g 6 - g 7 = rhs 19
  case' «20» => change g 10 + g 18 - g 7 = rhs 20
  case' «21» => change g 10 - g 12 + g 13 + g 18 + g 6 - 2 * g 7 - g 8 + g 9 = rhs 21
  case' «22» => change -g 12 + g 16 + g 18 + g 6 - g 7 = rhs 22
  case' «23» => change -g 12 + g 16 + g 18 + g 6 - g 7 - g 8 + g 9 = rhs 23
  all_goals
    norm_num [rhs, Fin.sum_univ_succ, entryMinorSupport,
      entryMinorCoefficients, Matrix.cons_val] <;> ring

/-- If the six matchings fixing zero attain a common lower support height,
their height also bounds every unitary determinant. The nine basis probes
vanish at the marked cross pair and share one nonnegative weight law. -/
theorem four_entry_face_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i : Fin 24, i.val < 6 → (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  have he (i : Fin 24) : e i = (fourPerm i).symm := rfl
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hcontact (i : Fin 24) (hi : i.val < 6) : fourMatchingEvaluation m i = H :=
    (hm i).trans (hc i hi)
  have hprofile (i : Fin 24) : g i = entryGapProfile g i := by
    have h := entryGapProfile_of_contacts m H (hcontact 0 (by decide)) (hcontact 1 (by decide))
      (hcontact 2 (by decide)) (hcontact 3 (by decide)) (hcontact 4 (by decide)) i
    simpa only [hm, g] using h
  let c := entryMinorCoefficients g
  have hdecomp (i : Fin 24) : g i = ∑ k : Fin 9, if i.val ∈ entryMinorSupport k then c k else 0 :=
    (hprofile i).trans (entryGapProfile_eq_minorSum g i)
  obtain ⟨w, hw, _, _, hmatch⟩ := exists_four_zero_pair_weights U hU
  let s := realSignedWeight U
  have hmass (k : Fin 9) : (∑ i : Fin 24, if i.val ∈ entryMinorSupport k then s (e i) else 0) =
      ∑ i : Fin 24, if i.val ∈ entryMinorSupport k then w (e i) else 0 := by
    let I := entryMinorRows k
    let J := entryMinorColumns k
    have hI : (0 : Fin 4) ∈ I := (by decide +kernel : ∀ j, (0 : Fin 4) ∈ entryMinorRows j) k
    have hJ : (0 : Fin 4) ∉ J := (by decide +kernel : ∀ j, (0 : Fin 4) ∉ entryMinorColumns j) k
    have hcard : I.card = J.card := (by decide +kernel :
      ∀ j, (entryMinorRows j).card = (entryMinorColumns j).card) k
    have h := hmatch (fun i => if i ∈ I then 0 else 1) (fun j => if j ∈ J then 1 else 0)
      (if_pos hI) (if_neg hJ)
    rw [← real_signed_determinant _ _ U hU] at h
    simp_rw [matchingProduct_subset_marker I J hcard] at h
    have hr := congrArg Complex.re h
    simp_rw [Complex.re_sum, mul_ite, mul_one, mul_zero, apply_ite, Complex.ofReal_re,
      Complex.zero_re] at hr
    simp_rw [entryMinorSupport_spec]
    change (∑ i : Fin 24, if J.map (e i).toEmbedding = I then s (e i) else 0) =
      ∑ i : Fin 24, if J.map (e i).toEmbedding = I then w (e i) else 0
    calc
      _ = ∑ σ, if J.map σ.toEmbedding = I then s σ else 0 :=
        Equiv.sum_comp e (fun σ => if J.map σ.toEmbedding = I then s σ else 0)
      _ = ∑ σ, if J.map σ.toEmbedding = I then w σ else 0 := hr.symm
      _ = _ := (Equiv.sum_comp e (fun σ => if J.map σ.toEmbedding = I then w σ else 0)).symm
  have hsum (v : FourPerm → ℝ) : (∑ i : Fin 24, v (e i) * g i) =
      ∑ k : Fin 9, c k * ∑ i : Fin 24, if i.val ∈ entryMinorSupport k then v (e i) else 0 := by
    simp_rw [hdecomp, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [mul_comm]
  have hdet := support_gap_eq a b U hU (-η) (fourPerm 0).symm
  simp only [matchingGap, neg_mul, Complex.neg_re, hc 0 (by decide)] at hdet
  have hneg (u v : ℝ) : -u - -v = v - u := by ring
  simp only [hneg] at hdet
  apply sub_nonneg.mp
  rw [hdet, ← Equiv.sum_comp e]
  change 0 ≤ ∑ i : Fin 24, s (e i) * g i
  have hequal : (∑ i : Fin 24, s (e i) * g i) = ∑ i : Fin 24, w (e i) * g i := by
    rw [hsum, hsum]
    simp_rw [hmass]
  rw [hequal]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw _) (sub_nonneg.mpr (hn i))

private theorem t1_entry_matching_relations (a b : Fin 4 → ℂ) :
    let p i := matchingProduct a b (fourPerm i).symm
    (p 0 * p 3) * p 4 = (p 1 * p 2) * p 5 ∧
    p 0 + p 3 + p 4 = p 1 + p 2 + p 5 ∧
    p 4 - p 5 = (a 0 + b 0) * (a 1 + b 3) * (a 2 - a 3) * (b 2 - b 1) := by
  dsimp only
  have h0 : matchingProduct a b (fourPerm 0).symm =
      (a 0 + b 0) * (a 1 + b 1) * (a 2 + b 2) * (a 3 + b 3) := by
    rw [matchingProduct_inverse, Fin.prod_univ_four]
    <;> rfl
  have h1 : matchingProduct a b (fourPerm 1).symm =
      (a 0 + b 0) * (a 1 + b 1) * (a 2 + b 3) * (a 3 + b 2) := by
    rw [matchingProduct_inverse, Fin.prod_univ_four]
    <;> rfl
  have h2 : matchingProduct a b (fourPerm 2).symm =
      (a 0 + b 0) * (a 1 + b 2) * (a 2 + b 1) * (a 3 + b 3) := by
    rw [matchingProduct_inverse, Fin.prod_univ_four]
    <;> rfl
  have h3 : matchingProduct a b (fourPerm 3).symm =
      (a 0 + b 0) * (a 1 + b 2) * (a 2 + b 3) * (a 3 + b 1) := by
    rw [matchingProduct_inverse, Fin.prod_univ_four]
    <;> rfl
  have h4 : matchingProduct a b (fourPerm 4).symm =
      (a 0 + b 0) * (a 1 + b 3) * (a 2 + b 1) * (a 3 + b 2) := by
    rw [matchingProduct_inverse, Fin.prod_univ_four]
    <;> rfl
  have h5 : matchingProduct a b (fourPerm 5).symm =
      (a 0 + b 0) * (a 1 + b 3) * (a 2 + b 2) * (a 3 + b 1) := by
    rw [matchingProduct_inverse, Fin.prod_univ_four]
    <;> rfl
  rw [h0, h1, h2, h3, h4, h5]
  exact ⟨by ac_rfl, by ring, by ring⟩

set_option maxHeartbeats 1000000 in
private theorem t1_extra_contacts (a b : Fin 4 → ℂ) (η : ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hη : η ≠ 0)
    (hnz : ∀ i j, a i + b j ≠ 0)
    (hc : ∀ i ∈ fourT1ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = 0) :
    ∀ i : Fin 24, i.val < 6 → (η * matchingProduct a b (fourPerm i).symm).re = 0 := by
  let p (i : Fin 24) := matchingProduct a b (fourPerm i).symm
  let z (i : Fin 24) := η * p i
  have hp (i : Fin 24) : z i ≠ 0 := mul_ne_zero hη
    (Finset.prod_ne_zero_iff.mpr fun j _ => hnz ((fourPerm i).symm j) j)
  have h0 : (z 0).re = 0 := hc 0 (by decide)
  have h1 : (z 1).re = 0 := hc 1 (by decide)
  have h2 : (z 2).re = 0 := hc 2 (by decide)
  have h3 : (z 3).re = 0 := hc 3 (by decide)
  obtain ⟨hprod, hsum, hdif⟩ := t1_entry_matching_relations a b
  change (p 0 * p 3) * p 4 = (p 1 * p 2) * p 5 at hprod
  change p 0 + p 3 + p 4 = p 1 + p 2 + p 5 at hsum
  change p 4 - p 5 = (a 0 + b 0) * (a 1 + b 3) * (a 2 - a 3) * (b 2 - b 1) at hdif
  have h4ne5 : z 4 ≠ z 5 := by
    apply sub_ne_zero.mp
    dsimp only [z]
    rw [← mul_sub, hdif]
    exact mul_ne_zero hη (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (hnz 0 0) (hnz 1 3)) (sub_ne_zero.mpr (ha.ne (by decide))))
      (sub_ne_zero.mpr (hb.ne (by decide))))
  let A := z 0 * z 3
  let B := z 1 * z 2
  have hA : A.im = 0 := by simp [A, Complex.mul_im, h0, h3]
  have hB : B.im = 0 := by simp [B, Complex.mul_im, h1, h2]
  have hmul : A * z 4 = B * z 5 := calc
    _ = η ^ 3 * ((p 0 * p 3) * p 4) := by dsimp only [A, z]; ring
    _ = η ^ 3 * ((p 1 * p 2) * p 5) := by rw [hprod]
    _ = _ := by dsimp only [B, z]; ring
  have hAneB : A ≠ B := by
    intro he
    rw [he] at hmul
    exact h4ne5 (mul_left_cancel₀ (mul_ne_zero (hp 1) (hp 2)) hmul)
  have hre : A.re ≠ B.re := by
    intro he
    exact hAneB (Complex.ext he (hA.trans hB.symm))
  have hadd : z 0 + z 3 + z 4 = z 1 + z 2 + z 5 := by
    simpa only [z, mul_add] using congrArg (fun q : ℂ => η * q) hsum
  have heq := congrArg Complex.re hadd
  simp only [Complex.add_re, h0, h1, h2, h3, zero_add] at heq
  have hreal := congrArg Complex.re hmul
  simp only [Complex.mul_re, hA, hB, zero_mul, sub_zero, ← heq] at hreal
  have hz4 : (z 4).re = 0 := by
    have hzero : (A.re - B.re) * (z 4).re = 0 := by rw [sub_mul, hreal, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hre)
  have hz5 : (z 5).re = 0 := heq.symm.trans hz4
  intro i hi
  change (z i).re = 0
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
    simp only [Fin.ext_iff]
    change i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5
    omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, hz4, hz5]

/-- The order-four support inequality for the six prescribed contacts of case T1. -/
theorem fourT1_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT1ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  have hbound (hh : Holds a b U) : H ≤ (η * determinantValue a b U).re := by
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hh (-η)
    obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
    have hgi := hn i
    rw [hi, Equiv.symm_symm] at hgi
    simp only [neg_mul, Complex.neg_re, neg_le_neg_iff] at hσ
    exact hgi.trans hσ
  by_cases hη : η = 0
  · simpa [hη] using hn 0
  by_cases ha : Function.Injective a
  · by_cases hb : Function.Injective b
    · by_cases hzero : ∃ i j, a i + b j = 0
      · obtain ⟨i, j, hij⟩ := hzero
        exact hbound (holds_four_of_opposite_entries a b U hU hij)
      · have hnz (i j : Fin 4) : a i + b j ≠ 0 := fun hij => hzero ⟨i, j, hij⟩
        have hp0 : (fourPerm 0).symm = 1 := by decide +kernel
        have hp1 : (fourPerm 1).symm = Equiv.swap 2 3 := by decide +kernel
        have hp6 : (fourPerm 6).symm = Equiv.swap 0 1 := by decide +kernel
        have hp7 : (fourPerm 7).symm = Equiv.swap 0 1 * Equiv.swap 2 3 := by decide +kernel
        have hH := matchingProduct_swap_rectangle_height_zero ha hb hη
          (by simpa only [hp0] using hc 0 (by decide))
          (by simpa only [hp6] using hc 6 (by decide))
          (by simpa only [hp1] using hc 1 (by decide))
          (by simpa only [hp7] using hc 7 (by decide))
        subst H
        exact four_entry_face_support a b η 0 hn (t1_extra_contacts a b η ha hb hη hnz hc) U hU
    · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inr hb))
  · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inl ha))

end

end MOC
