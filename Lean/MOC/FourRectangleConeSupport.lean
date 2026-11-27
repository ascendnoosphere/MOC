import MOC.FourMinorCertificate
import MOC.FourCoincidence
import MOC.FourMatchingRelations
import MOC.MatchingQuartet
import MOC.Support
import MOC.TwoExceptions
import Mathlib.Tactic.Linarith

/-! The cone decomposition and minor certificate for contact case rectangle-cone pattern. -/

namespace MOC

open BigOperators

noncomputable section

/-- The six matching permutations of contact pattern rectangle-cone pattern. -/
def fourRectangleConeContactIndices : Finset (Fin 24) := {0, 3, 5, 9, 11, 12}

/-- The contact rectangle 3, 5, 9, 11 forces zero height in case rectangle-cone pattern. -/
theorem fourRectangleCone_height_eq_zero (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hnz : ∀ i j, a i + b j ≠ 0)
    (hη : η ≠ 0)
    (hc : ∀ i ∈ fourRectangleConeContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    H = 0 := by
  let σ := (fourPerm 3).symm
  have h5 : (fourPerm 3).symm * Equiv.swap 2 3 = (fourPerm 5).symm := by decide +kernel
  have h9 : (fourPerm 3).symm * Equiv.swap 0 1 = (fourPerm 9).symm := by decide +kernel
  have h11 : (fourPerm 3).symm * Equiv.swap 2 3 * Equiv.swap 0 1 =
      (fourPerm 11).symm := by decide +kernel
  apply matchingProduct_disjoint_swaps_common_height_eq_zero a b σ 2 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb hnz hη
  · exact hc 3 (by decide)
  · simpa only [σ, h5] using hc 5 (by decide)
  · simpa only [σ, h9] using hc 9 (by decide)
  · simpa only [σ, h11] using hc 11 (by decide)

/-- The single possible mixed term is accompanied by coefficients of the
ordinary profiles 1 and 9. The canonical lift omits these two profiles. -/
private def rectangleConeConeLift (q a b c e f d h u v : ℝ) : Fin 14 → ℝ :=
  fun i => rectangleConeCanonicalLift q a b c e f d h i +
    u * (![0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1] : Fin 14 → ℝ) i +
    v * (![1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0] : Fin 14 → ℝ) i

set_option maxHeartbeats 2000000 in
/-- A nonnegative rectangle-cone pattern evaluation admits a nonnegative decomposition. When
the mixed term is positive, the two absorbable ordinary coefficients vanish. -/
private theorem fourRectangleCone_cone_decomposition (m : Fin 14 → ℝ)
    (hn : ∀ i, 0 ≤ fourMatchingEvaluation m i)
    (hc : ∀ i ∈ fourRectangleConeContactIndices, fourMatchingEvaluation m i = 0) :
    ∃ q a b c e f d h u v : ℝ,
      0 ≤ q ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ e ∧ 0 ≤ f ∧ 0 ≤ d ∧ 0 ≤ h ∧
      0 ≤ u ∧ 0 ≤ v ∧ (0 < d → u = 0 ∧ v = 0) ∧ m = rectangleConeConeLift q a b c e f d h u v := by
  let g := fourMatchingEvaluation m
  have h0 := hc 0 (by decide)
  have h3 := hc 3 (by decide)
  have h5 := hc 5 (by decide)
  have h9 := hc 9 (by decide)
  have h11 := hc 11 (by decide)
  have h12 := hc 12 (by decide)
  let B := g 8 - g 2 - g 6
  let L := g 7 + B - g 16
  let A := g 7 - g 13
  let K := max 0 (max L A)
  have hB : B = g 14 := by
    simp [B, g, fourMatchingEvaluation] at h0 h12 ⊢
    linarith only [h0, h12]
  have hL1 : g 1 - L = g 17 := by
    simp [L, B, g, fourMatchingEvaluation] at h0 h3 h9 ⊢
    linarith only [h0, h3, h9]
  have hL18 : g 18 - L = g 23 := by
    simp [L, B, g, fourMatchingEvaluation] at h5 h9 h12 ⊢
    linarith only [h5, h9, h12]
  have hA1 : g 1 - A = g 15 := by
    simp [A, g, fourMatchingEvaluation] at h3 h9 ⊢
    linarith only [h3, h9]
  have hA18 : g 18 - A = g 21 := by
    simp [A, g, fourMatchingEvaluation] at h0 h5 h11 h12 ⊢
    linarith only [h0, h5, h11, h12]
  have hB₀ : 0 ≤ B := by rw [hB]; exact hn 14
  have hL1' : L ≤ g 1 := sub_nonneg.mp (by rw [hL1]; exact hn 17)
  have hL18' : L ≤ g 18 := sub_nonneg.mp (by rw [hL18]; exact hn 23)
  have hA1' : A ≤ g 1 := sub_nonneg.mp (by rw [hA1]; exact hn 15)
  have hA18' : A ≤ g 18 := sub_nonneg.mp (by rw [hA18]; exact hn 21)
  have hK₀ : 0 ≤ K := le_max_left _ _
  have hKL : L ≤ K := (le_max_left L A).trans (le_max_right _ _)
  have hKA : A ≤ K := (le_max_right L A).trans (le_max_right _ _)
  have hK1 : K ≤ g 1 := max_le (hn 1) (max_le hL1' hA1')
  have hK18 : K ≤ g 18 := max_le (hn 18) (max_le hL18' hA18')
  have hA7 : A ≤ g 7 := sub_le_self _ (hn 13)
  have hK7B : K ≤ g 7 + B := max_le (add_nonneg (hn 7) hB₀)
    (max_le (sub_le_self _ (hn 16)) (hA7.trans (le_add_of_nonneg_right hB₀)))
  let h := min K (g 7)
  let d := K - h
  have hh : 0 ≤ h := le_min hK₀ (hn 7)
  have hd : 0 ≤ d := sub_nonneg.mpr (min_le_left _ _)
  have hdB : d ≤ B := by
    rcases le_total K (g 7) with hle | hle
    · simpa [d, h, min_eq_left hle] using hB₀
    · have he : h = g 7 := min_eq_right hle
      dsimp only [d]
      linarith only [he, hK7B]
  have hAh : A ≤ h := le_min hKA hA7
  have hsum : d + h = K := by dsimp only [d]; ring
  have h7h : h ≤ g 7 := min_le_right _ _
  let u := d + h + g 16 + g 2 + g 6 - g 7 - g 8
  let v := g 7 - h
  have hu : u = K - L := by dsimp only [u, L, B]; linarith only [hsum]
  refine ⟨g 18 - d - h, g 13 - g 7 + h, B - d, g 6, g 2, g 1 - d - h, d, h, u, v,
    by linarith only [hsum, hK18], by dsimp only [A] at hAh; linarith only [hAh],
    sub_nonneg.mpr hdB, hn 6, hn 2, by linarith only [hsum, hK1], hd, hh,
    by rw [hu]; exact sub_nonneg.mpr hKL, sub_nonneg.mpr h7h, ?_, ?_⟩
  · intro hd'
    have hgt : g 7 < K := by
      by_contra! hle
      simp [d, h, min_eq_left hle] at hd'
    have he : h = g 7 := min_eq_right hgt.le
    have hKL' : K = L := by
      have hLA : A < L := by
        by_contra! hnLA
        have hle : K ≤ g 7 := by
          simpa [K, max_eq_right hnLA] using (max_le (hn 7) hA7)
        exact (not_le_of_gt hgt) hle
      have hL₀ : 0 ≤ L := by
        by_contra! hnL
        have hnK : K = 0 := by simp [K, max_eq_left hLA.le, max_eq_left hnL.le]
        linarith only [hnK, hn 7, hgt]
      simp [K, max_eq_left hLA.le, max_eq_right hL₀]
    exact ⟨by rw [hu, hKL', sub_self], sub_eq_zero.mpr he.symm⟩
  · funext i
    simp [fourMatchingEvaluation] at h0 h3 h5 h9 h11 h12
    fin_cases i <;> simp [rectangleConeConeLift, rectangleConeCanonicalLift, B, u, v, g, fourMatchingEvaluation] <;>
      linarith only [h0, h3, h5, h9, h11, h12]

/-- At zero height, every rectangle-cone pattern spectral evaluation has a lift with only the
nine ordinary profiles. The conclusion includes all additional contacts. -/
private theorem fourRectangleCone_spectral_ordinary_lift (α β : Fin 4 → ℂ) (η : ℂ)
    (hn : ∀ i, 0 ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourRectangleConeContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = 0) :
    ∃ q a b c e f h u v : ℝ,
      0 ≤ q ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ e ∧ 0 ≤ f ∧ 0 ≤ h ∧
      0 ≤ u ∧ 0 ≤ v ∧ ∀ i, fourMatchingEvaluation (rectangleConeConeLift q a b c e f 0 h u v) i =
        (η * matchingProduct α β (fourPerm i).symm).re := by
  let m (i : Fin 14) := (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct α β (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part α β η i
  obtain ⟨q, a, b, c, e, f, d, h, u, v, hq, ha, hb, hc', he, hf, hd, hh, hu, hv, habs, hrep⟩ :=
    fourRectangleCone_cone_decomposition m (fun i => by rw [hm]; exact hn i)
      (fun i hi => (hm i).trans (hc i hi))
  have hdz : d = 0 := by
    by_contra hne
    obtain ⟨rfl, rfl⟩ := habs (lt_of_le_of_ne hd (Ne.symm hne))
    have hcan : m = rectangleConeCanonicalLift q a b c e f d h := by
      funext i
      rw [hrep]
      simp [rectangleConeConeLift]
    exact hne (rectangleCone_mixed_coefficient_zero_of_spectral α β η hq ha hb hc' he hf hd hh
      (fun i => by rw [← hcan, hm]))
  subst d
  exact ⟨q, a, b, c, e, f, h, u, v, hq, ha, hb, hc', he, hf, hh, hu, hv,
    fun i => by rw [← hrep, hm]⟩

private def rectangleConeMinorRows : Fin 9 → Finset (Fin 4) :=
  ![{0}, {0, 2}, {2}, {0, 3}, {0, 2}, {0, 3}, {3}, {0, 1}, {0, 3}]

private def rectangleConeMinorColumns : Fin 9 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {0}, {1, 3}, {0, 1}, {0, 2}, {2}, {2, 3}, {1, 2}]

private def rectangleConeMinorCoordinates : Fin 9 → Fin 14 → ℤ :=
  ![![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, -1, 0, 0, -1, 0, 0, 1, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0],
    ![-1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 1, 0],
    ![0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    ![-1, 1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1],
    ![1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0]]

private def rectangleConeMinorProfile (k : Fin 9) (i : Fin 24) : ℝ :=
  if (rectangleConeMinorColumns k).map (fourPerm i).symm.toEmbedding = rectangleConeMinorRows k then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem rectangleConeMinorCoordinates_evaluation (k : Fin 9) (i : Fin 24) :
    ((fourMatchingEvaluation (rectangleConeMinorCoordinates k) i : ℤ) : ℝ) = rectangleConeMinorProfile k i := by
  have h : ∀ (x : Fin 9) (y : Fin 24), fourMatchingEvaluation (rectangleConeMinorCoordinates x) y =
      (if (rectangleConeMinorColumns x).map (fourPerm y).symm.toEmbedding = rectangleConeMinorRows x then 1 else 0) := by
    decide +kernel
  rw [h]
  unfold rectangleConeMinorProfile
  split_ifs <;> norm_num

set_option maxHeartbeats 4000000 in
private theorem rectangleConeConeLift_evaluation_ordinary (q a b c e f h u v : ℝ) (i : Fin 24) :
    fourMatchingEvaluation (rectangleConeConeLift q a b c e f 0 h u v) i =
      ∑ k : Fin 9, (![q, a, b, c, e, f, h, u, v] : Fin 9 → ℝ) k * rectangleConeMinorProfile k i := by
  simp_rw [← rectangleConeMinorCoordinates_evaluation]
  fin_cases i <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, fourMatchingEvaluation, rectangleConeConeLift,
      rectangleConeCanonicalLift, rectangleConeMinorCoordinates, Matrix.cons_val] <;> norm_num <;> ring

private theorem fourRectangleCone_minor_response_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (k : Fin 9) :
    0 ≤ ∑ i : Fin 24, realSignedWeight U (fourPerm i).symm * rectangleConeMinorProfile k i := by
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  let I := rectangleConeMinorRows k
  let J := rectangleConeMinorColumns k
  have he (i : Fin 24) : e i = (fourPerm i).symm := rfl
  have hsum := Equiv.sum_comp e (fun σ =>
    if J.map σ.toEmbedding = I then realSignedWeight U σ else 0)
  simp only [he] at hsum
  have hminor := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re, Complex.ofReal_re] at hminor
  have hprofile (i : Fin 24) :
      realSignedWeight U (fourPerm i).symm * rectangleConeMinorProfile k i =
        if J.map (fourPerm i).symm.toEmbedding = I then realSignedWeight U (fourPerm i).symm else 0 := by
    simp only [rectangleConeMinorProfile, I, J, mul_ite, mul_one, mul_zero]
  simp_rw [hprofile]
  rw [hsum]
  exact (subsetMinorSq_nonneg U I J).trans_eq hminor.symm

/-- In paper case rectangle-cone pattern with zero contact height, every unitary response has
nonnegative projection along the chosen supporting normal. -/
theorem fourRectangleCone_zero_height_support (α β : Fin 4 → ℂ) (η : ℂ)
    (hn : ∀ i, 0 ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourRectangleConeContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = 0)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ (η * determinantValue α β U).re := by
  obtain ⟨q, a, b, c, e, f, h, u, v, hq, ha, hb, hc', he, hf, hh, hu, hv, hrep⟩ :=
    fourRectangleCone_spectral_ordinary_lift α β η hn hc
  let w : Fin 9 → ℝ := ![q, a, b, c, e, f, h, u, v]
  let E : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  have hw (k : Fin 9) : 0 ≤ w k := by fin_cases k <;> assumption
  have hdet :
      (η * determinantValue α β U).re =
        ∑ σ : FourPerm, realSignedWeight U σ * (η * matchingProduct α β σ).re := by
    rw [← real_signed_determinant α β U hU, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [mul_left_comm η, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hr (k : Fin 9) :
      (∑ i : Fin 24, realSignedWeight U (fourPerm i).symm * (w k * rectangleConeMinorProfile k i)) =
        w k * ∑ i : Fin 24, realSignedWeight U (fourPerm i).symm * rectangleConeMinorProfile k i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdet, ← Equiv.sum_comp E]
  change 0 ≤ ∑ i : Fin 24, realSignedWeight U (fourPerm i).symm *
    (η * matchingProduct α β (fourPerm i).symm).re
  simp_rw [← hrep, rectangleConeConeLift_evaluation_ordinary, Finset.mul_sum]
  change 0 ≤ ∑ i : Fin 24, ∑ k : Fin 9, realSignedWeight U (fourPerm i).symm *
    (w k * rectangleConeMinorProfile k i)
  rw [Finset.sum_comm]
  simp_rw [hr]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (fourRectangleCone_minor_response_nonneg U hU k))

/-- For eight distinct marked points, the rectangle-cone pattern contact and spectral gap
conditions imply the support inequality in the stated direction. -/
theorem fourRectangleCone_support_of_distinct (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β) (hnz : ∀ i j, α i + β j ≠ 0)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourRectangleConeContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue α β U).re := by
  by_cases hη : η = 0
  · simpa [hη] using hn 0
  have hH := fourRectangleCone_height_eq_zero α β η H ha hb hnz hη hc
  subst H
  exact fourRectangleCone_zero_height_support α β η hn hc U hU

/-- The rectangle-cone pattern support inequality holds for every unitary response, including
additional contacts and coincidences among the eight marked points. -/
theorem fourRectangleCone_support (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourRectangleConeContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue α β U).re := by
  have hbound (hh : Holds α β U) :=
    four_lower_support_of_holds α β η H U hh hn
  by_cases ha : Function.Injective α
  · by_cases hb : Function.Injective β
    · by_cases hzero : ∃ i j, α i + β j = 0
      · obtain ⟨i, j, hij⟩ := hzero
        exact hbound (holds_four_of_opposite_entries α β U hU hij)
      · exact fourRectangleCone_support_of_distinct α β η H ha hb
          (fun i j hij => hzero ⟨i, j, hij⟩) hn hc U hU
    · exact hbound (holds_four_of_repeated_spectrum α β U hU (Or.inr hb))
  · exact hbound (holds_four_of_repeated_spectrum α β U hU (Or.inl ha))

end

end MOC
