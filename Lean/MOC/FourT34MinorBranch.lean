import MOC.ContactRectangle
import MOC.FourContactCones

/-! The minor branch of the paper's T34 contact case. -/

namespace MOC

open BigOperators

noncomputable section

private def t34MinorRows : Fin 7 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0, 3}, {1}, {0, 1}]

private def t34MinorColumns : Fin 7 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {2, 3}, {1, 3}, {0, 2}, {1}, {0, 1}]

private def t34MinorCoordinates : Fin 7 → Fin 14 → ℤ :=
  ![![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1],
    ![0, 1, 0, -1, 0, 0, -1, 0, 0, 1, 0, -1, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 1, 0],
    ![-1, 1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem t34MinorCoordinates_evaluation (k : Fin 7) (i : Fin 24) :
    ((fourMatchingEvaluation (t34MinorCoordinates k) i : ℤ) : ℝ) =
      if (t34MinorColumns k).map (fourPerm i).symm.toEmbedding = t34MinorRows k then 1 else 0 := by
  have h : ∀ (x : Fin 7) (y : Fin 24), fourMatchingEvaluation (t34MinorCoordinates x) y =
      (if (t34MinorColumns x).map (fourPerm y).symm.toEmbedding = t34MinorRows x then 1 else 0) := by
    decide +kernel
  simp only [h, apply_ite, Int.cast_one, Int.cast_zero]

set_option maxHeartbeats 4000000 in
private theorem t34HeightLift_evaluation_minor (p r a b c q s H : ℝ) (i : Fin 24) :
    fourMatchingEvaluation (t34HeightLift p r a b c q 0 s H) i - H =
      ∑ k : Fin 7, (![p, r, a, b, c, q, s] : Fin 7 → ℝ) k *
        ((fourMatchingEvaluation (t34MinorCoordinates k) i : ℤ) : ℝ) := by
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, fourMatchingEvaluation, t34HeightLift, t34MinorCoordinates] <;> ring

private theorem t34Minor_response_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (k : Fin 7) :
    0 ≤ ∑ σ : FourPerm, if (t34MinorColumns k).map σ.toEmbedding = t34MinorRows k then
      realSignedWeight U σ else 0 := by
  have hminor := congrArg Complex.re
    (sum_signedWeight_image_eq_subsetMinorSq U hU (t34MinorRows k) (t34MinorColumns k))
  simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re, Complex.ofReal_re,
    ← realSignedWeight] at hminor
  rw [hminor]
  exact subsetMinorSq_nonneg U _ _

/-- An additional contact at index 11 eliminates the mixed coefficient of
T34, leaving a nonnegative combination of squared minors. -/
theorem fourT34_support_of_contact_eleven (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (h11 : (η * matchingProduct α β (fourPerm 11).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue α β U).re := by
  let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
  let w : Fin 7 → ℝ := ![g 18, g 16, g 13, g 8, g 4, g 14, g 7]
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
  have hw (i : Fin 7) : 0 ≤ w i := by
    have hg (j : Fin 24) : 0 ≤ g j := sub_nonneg.mpr (hn j)
    fin_cases i <;> first | exact hg 18 | exact hg 16 | exact hg 13 | exact hg 8 |
      exact hg 4 | exact hg 14 | exact hg 7
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct α β (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part α β η i
  have hd : g 11 = 0 := sub_eq_zero.mpr h11
  have hrep : m = t34HeightLift (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) 0 (g 7) H := by
    have h := fourT34_height_lift_of_contacts m H (fun i hi => (hm i).trans (hc i hi))
    dsimp only at h
    simp only [hm] at h
    change m = t34HeightLift (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7) H at h
    rwa [hd] at h
  have hsum (i : Fin 24) :
      g i = ∑ k : Fin 7, w k * ((fourMatchingEvaluation (t34MinorCoordinates k) i : ℤ) : ℝ) := by
    have h := t34HeightLift_evaluation_minor (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 7) H i
    rwa [← hrep, hm] at h
  have hgap := support_gap_eq α β U hU (-η) (fourPerm 2).symm
  have h2 := hc 2 (by decide)
  simp only [matchingGap, neg_mul, Complex.neg_re, h2] at hgap
  have heq (x y : ℝ) : -x - -y = y - x := by ring
  simp only [heq] at hgap
  apply sub_nonneg.mp
  rw [hgap]
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  rw [← Equiv.sum_comp e]
  change 0 ≤ ∑ i : Fin 24, realSignedWeight U (fourPerm i).symm * g i
  simp_rw [hsum, t34MinorCoordinates_evaluation, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg (fun k _ => ?_)
  have hprod (i : Fin 24) :
      realSignedWeight U (fourPerm i).symm *
          (w k * (if (t34MinorColumns k).map (fourPerm i).symm.toEmbedding = t34MinorRows k
            then 1 else 0)) =
        w k * (if (t34MinorColumns k).map (fourPerm i).symm.toEmbedding = t34MinorRows k
          then realSignedWeight U (fourPerm i).symm else 0) := by
    split_ifs <;> simp [mul_comm]
  simp_rw [hprod, ← Finset.mul_sum]
  have he (i : Fin 24) : e i = (fourPerm i).symm := rfl
  have hfilter := Equiv.sum_comp e (fun σ =>
    if (t34MinorColumns k).map σ.toEmbedding = t34MinorRows k then realSignedWeight U σ else 0)
  simp only [he] at hfilter
  rw [hfilter]
  exact mul_nonneg (hw k) (t34Minor_response_nonneg U hU k)

/-- On the zero-height T34 branch, the multiplicative rectangle 3, 5, 9,
11 forces another contact if the index-3 matching product is nonzero. -/
theorem fourT34_contact_eleven_of_zero_height (α β : Fin 4 → ℂ) (η : ℂ)
    (hη : η ≠ 0) (hm : matchingProduct α β (fourPerm 3).symm ≠ 0)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = 0) :
    (η * matchingProduct α β (fourPerm 11).symm).re = 0 := by
  let σ := (fourPerm 3).symm
  have h5 : (fourPerm 3).symm * Equiv.swap 2 3 = (fourPerm 5).symm := by decide +kernel
  have h9 : (fourPerm 3).symm * Equiv.swap 0 1 = (fourPerm 9).symm := by decide +kernel
  have h11 : (fourPerm 3).symm * Equiv.swap 2 3 * Equiv.swap 0 1 =
      (fourPerm 11).symm := by decide +kernel
  have hdiag := matchingProduct_disjoint_swaps_identity α β σ 2 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [σ, h5, h9, h11] at hdiag
  let z (i : Fin 24) := η * matchingProduct α β (fourPerm i).symm
  have hmul : z 3 * z 11 = z 5 * z 9 := calc
    _ = η ^ 2 * (matchingProduct α β (fourPerm 3).symm *
          matchingProduct α β (fourPerm 11).symm) := by dsimp only [z]; ring
    _ = η ^ 2 * (matchingProduct α β (fourPerm 5).symm *
          matchingProduct α β (fourPerm 9).symm) := by rw [hdiag]
    _ = _ := by dsimp only [z]; ring
  have h3 : (z 3).re = 0 := hc 3 (by decide)
  have hprod : z 3 ≠ 0 := mul_ne_zero hη hm
  have him : (z 3).im ≠ 0 := by
    intro hz
    exact hprod (Complex.ext h3 hz)
  have hg := rectangle_fourth_gap hmul h3 (hc 5 (by decide)) (hc 9 (by decide))
  have hz : -(z 11).re * (z 3).im ^ 2 = 0 := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, zero_sub, zero_mul] using hg
  exact neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ him))

/-- The paper's T34 support inequality at zero height, including vanishing
matching products. -/
theorem fourT34_zero_height_support (α β : Fin 4 → ℂ) (η : ℂ)
    (hn : ∀ i, 0 ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = 0)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    0 ≤ (η * determinantValue α β U).re := by
  by_cases hη : η = 0
  · simp [hη]
  by_cases hm : matchingProduct α β (fourPerm 3).symm = 0
  · have hh := holds_four_of_zero_matchingProduct α β U hU hm
    obtain ⟨σ, hσ⟩ := (holds_iff_directional α β U).mp hh (-η)
    obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
    have hei : (fourPerm i).symm = σ := by simp [hi]
    have hgi := hn i
    rw [hei] at hgi
    simp only [neg_mul, Complex.neg_re, neg_le_neg_iff] at hσ
    exact hgi.trans hσ
  · exact fourT34_support_of_contact_eleven α β η 0 hn hc
      (fourT34_contact_eleven_of_zero_height α β η hη hm hc) U hU

/-- When both donor gaps of T34 vanish, a second rectangle forces zero
height. Consequently their sum is positive on the regular mixed branch. -/
theorem fourT34_donor_sum_pos_of_mixed (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (ha : Function.Injective α) (hb : Function.Injective β)
    (hnz : ∀ i j, α i + β j ≠ 0) (hη : η ≠ 0)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (hd : H < (η * matchingProduct α β (fourPerm 11).symm).re) :
    0 < ((η * matchingProduct α β (fourPerm 4).symm).re - H) +
      ((η * matchingProduct α β (fourPerm 8).symm).re - H) := by
  by_contra! hsum
  have he4 : (η * matchingProduct α β (fourPerm 4).symm).re = H := by
    linarith only [hsum, hn 4, hn 8]
  have he8 : (η * matchingProduct α β (fourPerm 8).symm).re = H := by
    linarith only [hsum, hn 4, hn 8]
  let σ := (fourPerm 2).symm
  have h4 : (fourPerm 2).symm * Equiv.swap 2 3 = (fourPerm 4).symm := by decide +kernel
  have h8 : (fourPerm 2).symm * Equiv.swap 0 1 = (fourPerm 8).symm := by decide +kernel
  have h10 : (fourPerm 2).symm * Equiv.swap 2 3 * Equiv.swap 0 1 =
      (fourPerm 10).symm := by decide +kernel
  have hH : H = 0 := matchingProduct_disjoint_swaps_common_height_eq_zero α β σ 2 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb hnz hη
    (hc 2 (by decide)) (by simpa only [σ, h4] using he4) (by simpa only [σ, h8] using he8)
    (by simpa only [σ, h10] using hc 10 (by decide))
  subst H
  have hm : matchingProduct α β (fourPerm 3).symm ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hnz _ j)
  exact (ne_of_gt hd) (fourT34_contact_eleven_of_zero_height α β η hη hm hc)

end

end MOC
