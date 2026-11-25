import MOC.FourMatchingRelations
import MOC.FourCoincidence
import MOC.TwoExceptions
import MOC.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! A nonnegative squared-minor certificate for Zheng's contact case T2. -/

namespace MOC

open BigOperators

noncomputable section

/-- The six contacts of paper case T2 in lexicographic order. -/
def fourT2ContactIndices : Finset (Fin 24) := {0, 1, 2, 3, 6, 8}

private def t2MinorRows : Fin 11 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 3}, {0}, {0, 1}, {3}, {0, 3}, {0, 2}, {0, 1}, {1}]

private def t2MinorColumns : Fin 11 → Finset (Fin 4) :=
  ![{3}, {2, 3}, {2, 3}, {2, 3}, {2}, {1, 3}, {0}, {1, 2}, {1, 3}, {0, 3}, {3}]

private def t2MinorSupports : Fin 11 → Finset ℕ :=
  ![{18, 19, 20, 21, 22, 23}, {16, 17, 22, 23}, {13, 15, 19, 21}, {12, 14, 18, 20},
    {12, 13, 14, 15, 16, 17}, {10, 11, 20, 21}, {9, 11, 15, 17, 21, 23}, {7, 10, 13, 16},
    {7, 9, 18, 23}, {4, 5, 18, 19}, {4, 5, 10, 11, 16, 17}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem t2MinorSupports_spec (k : Fin 11) (i : Fin 24) :
    i.val ∈ t2MinorSupports k ↔ (t2MinorColumns k).map (fourPerm i).symm.toEmbedding =
      t2MinorRows k := by
  fin_cases k <;> fin_cases i <;> decide

private def t2GapProfile (g : Fin 24 → ℝ) : Fin 24 → ℝ :=
  ![0, 0, 0, 0, g 4, g 4, 0, g 7, 0, g 7, g 10, g 10, g 12, g 13, g 12,
    g 13, g 16, g 16, g 18, g 18 + g 13 - g 12 - g 7, g 18 + g 10 - g 4 - g 7,
    g 18 + g 10 + g 13 - g 4 - g 7 - g 12,
    g 18 + g 16 - g 4 - g 7 - g 12, g 18 + g 16 - g 4 - g 12]

private def t2MinorWeights (g : Fin 24 → ℝ) (x y z : ℝ) : Fin 11 → ℝ :=
  ![g 18 - g 4 - g 7 - g 12 + x + y + z, g 16 - x - y - z, g 13 - x - y,
    g 12 - x, x, g 10 - y - z, y, y, g 7 - y, g 4 - z, z]

set_option maxHeartbeats 3000000 in
private theorem t2GapProfile_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (h0 : fourMatchingEvaluation m 0 = H) (h1 : fourMatchingEvaluation m 1 = H)
    (h2 : fourMatchingEvaluation m 2 = H) (h3 : fourMatchingEvaluation m 3 = H)
    (h6 : fourMatchingEvaluation m 6 = H) (h8 : fourMatchingEvaluation m 8 = H)
    (h79 : fourMatchingEvaluation m 7 = fourMatchingEvaluation m 9)
    (i : Fin 24) :
    let g := fun j => fourMatchingEvaluation m j - H
    g i = t2GapProfile g i := by
  let g (j : Fin 24) := fourMatchingEvaluation m j - H
  change g i = t2GapProfile g i
  dsimp only [fourMatchingEvaluation, Matrix.cons_val] at h0 h1 h2 h3 h6 h8 h79
  fin_cases i
  · change g 0 = t2GapProfile g 0
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h0
  · change g 1 = t2GapProfile g 1
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h1
  · change g 2 = t2GapProfile g 2
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h2
  · change g 3 = t2GapProfile g 3
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h3
  · change g 4 = t2GapProfile g 4
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 5 = t2GapProfile g 5
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h0 - 1 * h1 - 1 * h2 + 1 * h3
  · change g 6 = t2GapProfile g 6
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h6
  · change g 7 = t2GapProfile g 7
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 8 = t2GapProfile g 8
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h8
  · change g 9 = t2GapProfile g 9
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -1 * h79
  · change g 10 = t2GapProfile g 10
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 11 = t2GapProfile g 11
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h6 - 1 * h8 - 1 * h79
  · change g 12 = t2GapProfile g 12
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 13 = t2GapProfile g 13
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 14 = t2GapProfile g 14
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h0 - 1 * h2 - 1 * h6 + 1 * h8
  · change g 15 = t2GapProfile g 15
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h1 - 1 * h3 - 1 * h79
  · change g 16 = t2GapProfile g 16
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 17 = t2GapProfile g 17
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -1 * h0 + 1 * h1 + 1 * h2 - 1 * h3 + 1 * h6 - 1 * h8 - 1 * h79
  · change g 18 = t2GapProfile g 18
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val] <;> ring
  · change g 19 = t2GapProfile g 19
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h6
  · change g 20 = t2GapProfile g 20
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h1
  · change g 21 = t2GapProfile g 21
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination 1 * h1 + 1 * h2 - 1 * h3 + 1 * h6 - 1 * h8 - 1 * h79
  · change g 22 = t2GapProfile g 22
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -1 * h0 + 1 * h1 + 1 * h2 + 1 * h6
  · change g 23 = t2GapProfile g 23
    dsimp only [g, t2GapProfile, fourMatchingEvaluation, Matrix.cons_val]
    <;> linear_combination -1 * h0 + 1 * h1 + 2 * h2 - 1 * h3 + 1 * h6 - 1 * h8 - 1 * h79

set_option maxHeartbeats 3000000 in
private theorem t2GapProfile_eq_minorSum (g : Fin 24 → ℝ) (x y z : ℝ) (i : Fin 24) :
    t2GapProfile g i = ∑ k : Fin 11, if i.val ∈ t2MinorSupports k then
      t2MinorWeights g x y z k else 0 := by
  let rhs (i : ℕ) := ∑ k : Fin 11, if i ∈ t2MinorSupports k then t2MinorWeights g x y z k else 0
  change t2GapProfile g i = rhs i.val
  fin_cases i
  case' «0» => change 0 = rhs 0
  case' «1» => change 0 = rhs 1
  case' «2» => change 0 = rhs 2
  case' «3» => change 0 = rhs 3
  case' «4» => change g 4 = rhs 4
  case' «5» => change g 4 = rhs 5
  case' «6» => change 0 = rhs 6
  case' «7» => change g 7 = rhs 7
  case' «8» => change 0 = rhs 8
  case' «9» => change g 7 = rhs 9
  case' «10» => change g 10 = rhs 10
  case' «11» => change g 10 = rhs 11
  case' «12» => change g 12 = rhs 12
  case' «13» => change g 13 = rhs 13
  case' «14» => change g 12 = rhs 14
  case' «15» => change g 13 = rhs 15
  case' «16» => change g 16 = rhs 16
  case' «17» => change g 16 = rhs 17
  case' «18» => change g 18 = rhs 18
  case' «19» => change g 18 + g 13 - g 12 - g 7 = rhs 19
  case' «20» => change g 18 + g 10 - g 4 - g 7 = rhs 20
  case' «21» => change g 18 + g 10 + g 13 - g 4 - g 7 - g 12 = rhs 21
  case' «22» => change g 18 + g 16 - g 4 - g 7 - g 12 = rhs 22
  case' «23» => change g 18 + g 16 - g 4 - g 12 = rhs 23
  all_goals
    norm_num [rhs, Fin.sum_univ_succ, t2MinorSupports,
      t2MinorWeights, Matrix.cons_val] <;> ring

private theorem t2_exists_minorWeights (g : Fin 24 → ℝ)
    (hn : ∀ i, 0 ≤ g i) (hprofile : ∀ i, g i = t2GapProfile g i) :
    ∃ x y z : ℝ, ∀ k, 0 ≤ t2MinorWeights g x y z k := by
  have h19 : 0 ≤ g 18 + g 13 - g 12 - g 7 := by
    simpa only [hprofile 19, t2GapProfile] using hn 19
  have h20 : 0 ≤ g 18 + g 10 - g 4 - g 7 := by
    simpa only [hprofile 20, t2GapProfile] using hn 20
  have h21 : 0 ≤ g 18 + g 10 + g 13 - g 4 - g 7 - g 12 := by
    simpa only [hprofile 21, t2GapProfile] using hn 21
  have h22 : 0 ≤ g 18 + g 16 - g 4 - g 7 - g 12 := by
    simpa only [hprofile 22, t2GapProfile] using hn 22
  by_cases h : g 7 ≤ g 18
  · let T := g 4 + g 7 + g 12 - g 18
    let L := max 0 T
    let x := min L (min (g 12) (g 13))
    let z := L - x
    have hT : T ≤ L := le_max_right _ _
    have hL : 0 ≤ L := le_max_left _ _
    have h16 : L ≤ g 16 := max_le (hn 16) (by dsimp [T]; linarith only [h22])
    have hbound : L ≤ min (g 12) (g 13) + min (g 4) (g 10) := by
      apply max_le
      · exact add_nonneg (le_min (hn 12) (hn 13)) (le_min (hn 4) (hn 10))
      · dsimp only [T]
        rcases le_total (g 12) (g 13) with hb | hb <;>
          rcases le_total (g 4) (g 10) with hc | hc
        · rw [min_eq_left hb, min_eq_left hc]
          linarith only [h]
        · rw [min_eq_left hb, min_eq_right hc]
          linarith only [h20]
        · rw [min_eq_right hb, min_eq_left hc]
          linarith only [h19]
        · rw [min_eq_right hb, min_eq_right hc]
          linarith only [h21]
    have hx : 0 ≤ x := le_min hL (le_min (hn 12) (hn 13))
    have hxL : x ≤ L := min_le_left _ _
    have hx12 : x ≤ g 12 := (min_le_right _ _).trans (min_le_left _ _)
    have hx13 : x ≤ g 13 := (min_le_right _ _).trans (min_le_right _ _)
    have hz : 0 ≤ z := sub_nonneg.mpr hxL
    have hz' : z ≤ min (g 4) (g 10) := by
      rcases le_total L (min (g 12) (g 13)) with hl | hl
      · dsimp only [z, x]
        rw [min_eq_left hl, sub_self]
        exact le_min (hn 4) (hn 10)
      · dsimp only [z, x]
        rw [min_eq_right hl]
        linarith only [hbound]
    have hz4 := hz'.trans (min_le_left _ _)
    have hz10 := hz'.trans (min_le_right _ _)
    have hxz : x + z = L := by dsimp only [z]; ring
    change g 4 + g 7 + g 12 - g 18 ≤ L at hT
    refine ⟨x, 0, z, ?_⟩
    intro k
    fin_cases k <;> norm_num [t2MinorWeights, Matrix.cons_val] <;>
      linarith only [hT, h16, hx, hx12, hx13, hz, hz4, hz10, hxz, hn 7]
  · have hy : 0 ≤ g 7 - g 18 := sub_nonneg.mpr (le_of_lt (lt_of_not_ge h))
    refine ⟨g 12, g 7 - g 18, g 4, ?_⟩
    intro k
    fin_cases k <;> norm_num [t2MinorWeights, Matrix.cons_val] <;>
      linarith only [h19, h20, h22, hy, hn 4, hn 12, hn 18]

private theorem t2_matching_chords (a b : Fin 4 → ℂ) :
    let p i := matchingProduct a b (fourPerm i).symm
    (p 7 - p 9) * (p 0 - p 2) = (p 6 - p 8) * (p 1 - p 3) ∧
    p 0 - p 2 = (a 0 + b 0) * (a 3 + b 3) * (a 1 - a 2) * (b 2 - b 1) := by
  let p i := matchingProduct a b (fourPerm i).symm
  have h79 : p 7 - p 9 = (a 0 + b 1) * (a 2 + b 3) * (a 1 - a 3) * (b 2 - b 0) := by
    simp [p, matchingProduct_inverse, Fin.prod_univ_four, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring
  have h02 : p 0 - p 2 = (a 0 + b 0) * (a 3 + b 3) * (a 1 - a 2) * (b 2 - b 1) := by
    simp [p, matchingProduct_inverse, Fin.prod_univ_four, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring
  have h68 : p 6 - p 8 = (a 0 + b 1) * (a 3 + b 3) * (a 1 - a 2) * (b 2 - b 0) := by
    simp [p, matchingProduct_inverse, Fin.prod_univ_four, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring
  have h13 : p 1 - p 3 = (a 0 + b 0) * (a 2 + b 3) * (a 1 - a 3) * (b 2 - b 1) := by
    simp [p, matchingProduct_inverse, Fin.prod_univ_four, fourPerm,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;> ring
  change (p 7 - p 9) * (p 0 - p 2) = (p 6 - p 8) * (p 1 - p 3) ∧ _
  refine ⟨?_, h02⟩
  rw [h79, h02, h68, h13]
  ring

private theorem t2_equal_seventh_ninth_values (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hη : η ≠ 0)
    (hnz : ∀ i j, a i + b j ≠ 0)
    (hc : ∀ i ∈ fourT2ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    (η * matchingProduct a b (fourPerm 7).symm).re =
      (η * matchingProduct a b (fourPerm 9).symm).re := by
  let p (i : Fin 24) := matchingProduct a b (fourPerm i).symm
  let d (i j : Fin 24) := η * (p i - p j)
  have hz (i j : Fin 24) (hi : i ∈ fourT2ContactIndices) (hj : j ∈ fourT2ContactIndices) :
      (d i j).re = 0 := by
    simp only [d, mul_sub, Complex.sub_re, p, hc i hi, hc j hj, sub_self]
  have h02 := hz 0 2 (by decide) (by decide)
  have h68 := hz 6 8 (by decide) (by decide)
  have h13 := hz 1 3 (by decide) (by decide)
  obtain ⟨hchord, hfactor⟩ := t2_matching_chords a b
  change (p 7 - p 9) * (p 0 - p 2) = (p 6 - p 8) * (p 1 - p 3) at hchord
  change p 0 - p 2 = (a 0 + b 0) * (a 3 + b 3) * (a 1 - a 2) * (b 2 - b 1) at hfactor
  have h02ne : d 0 2 ≠ 0 := by
    dsimp only [d]
    rw [hfactor]
    exact mul_ne_zero hη (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (hnz 0 0) (hnz 3 3))
        (sub_ne_zero.mpr (ha.ne (by decide)))) (sub_ne_zero.mpr (hb.ne (by decide))))
  have h02im : (d 0 2).im ≠ 0 := by
    intro h
    exact h02ne (Complex.ext h02 h)
  have hprod : d 7 9 * d 0 2 = d 6 8 * d 1 3 := calc
    _ = η ^ 2 * ((p 7 - p 9) * (p 0 - p 2)) := by dsimp only [d]; ring
    _ = η ^ 2 * ((p 6 - p 8) * (p 1 - p 3)) := by rw [hchord]
    _ = _ := by dsimp only [d]; ring
  have him := congrArg Complex.im hprod
  simp only [Complex.mul_im, h02, h68, h13, mul_zero, zero_mul, add_zero] at him
  have h79 := (mul_eq_zero.mp him).resolve_right h02im
  exact sub_eq_zero.mp (by simpa only [d, mul_sub, Complex.sub_re, p] using h79)

private theorem fourT2_support_of_distinct (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hnz : ∀ i j, a i + b j ≠ 0)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT2ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  by_cases hη : η = 0
  · simpa [hη] using hn 0
  let m : Fin 14 → ℝ := fun i => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) i).re
  let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct a b (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part a b η i
  have hi (i : Fin 24) (hi : i ∈ fourT2ContactIndices) : fourMatchingEvaluation m i = H :=
    (hm i).trans (hc i hi)
  have h79 := t2_equal_seventh_ninth_values a b η H ha hb hη hnz hc
  have h79' : fourMatchingEvaluation m 7 = fourMatchingEvaluation m 9 := by
    simpa only [hm] using h79
  have hprofile (i : Fin 24) : g i = t2GapProfile g i := by
    have h := t2GapProfile_of_contacts m H (hi 0 (by decide)) (hi 1 (by decide))
      (hi 2 (by decide)) (hi 3 (by decide)) (hi 6 (by decide)) (hi 8 (by decide)) h79' i
    simpa only [hm, g] using h
  obtain ⟨x, y, z, hw⟩ := t2_exists_minorWeights g (fun i => sub_nonneg.mpr (hn i)) hprofile
  let w := t2MinorWeights g x y z
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  have he (i : Fin 24) : e i = (fourPerm i).symm := rfl
  have hdecomp (i : Fin 24) : g i = ∑ k : Fin 11, if i.val ∈ t2MinorSupports k then w k else 0 :=
    (hprofile i).trans (t2GapProfile_eq_minorSum g x y z i)
  have hminor (k : Fin 11) : 0 ≤ ∑ i : Fin 24,
      if i.val ∈ t2MinorSupports k then realSignedWeight U (fourPerm i).symm else 0 := by
    simp_rw [t2MinorSupports_spec]
    have hmap := Equiv.sum_comp e (fun σ =>
      if (t2MinorColumns k).map σ.toEmbedding = t2MinorRows k then realSignedWeight U σ else 0)
    simp only [he] at hmap
    rw [hmap]
    have hs := congrArg Complex.re
      (sum_signedWeight_image_eq_subsetMinorSq U hU (t2MinorRows k) (t2MinorColumns k))
    simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re, Complex.ofReal_re] at hs
    exact (subsetMinorSq_nonneg U _ _).trans_eq hs.symm
  have hdet := support_gap_eq a b U hU (-η) (fourPerm 0).symm
  simp only [matchingGap, neg_mul, Complex.neg_re, hc 0 (by decide)] at hdet
  have hneg (s t : ℝ) : -s - -t = t - s := by ring
  simp only [hneg] at hdet
  apply sub_nonneg.mp
  rw [hdet, ← Equiv.sum_comp e]
  change 0 ≤ ∑ i : Fin 24, realSignedWeight U (fourPerm i).symm * g i
  simp_rw [hdecomp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg (fun k _ => ?_)
  have hp (i : Fin 24) :
      realSignedWeight U (fourPerm i).symm *
          (if i.val ∈ t2MinorSupports k then w k else 0) =
        w k * (if i.val ∈ t2MinorSupports k then realSignedWeight U (fourPerm i).symm else 0) := by
    split_ifs <;> simp [mul_comm]
  simp_rw [hp, ← Finset.mul_sum]
  exact mul_nonneg (hw k) (hminor k)

/-- The order-four support inequality for the six prescribed contacts of case T2.
The same inequality holds when extra permutations make contact. -/
theorem fourT2_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT2ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  have hbound (hh : Holds a b U) : H ≤ (η * determinantValue a b U).re := by
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hh (-η)
    obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
    have hgi := hn i
    rw [hi, Equiv.symm_symm] at hgi
    simp only [neg_mul, Complex.neg_re, neg_le_neg_iff] at hσ
    exact hgi.trans hσ
  by_cases ha : Function.Injective a
  · by_cases hb : Function.Injective b
    · by_cases hzero : ∃ i j, a i + b j = 0
      · obtain ⟨i, j, hij⟩ := hzero
        exact hbound (holds_four_of_opposite_entries a b U hU hij)
      · exact fourT2_support_of_distinct a b η H ha hb
          (fun i j hij => hzero ⟨i, j, hij⟩) hn hc U hU
    · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inr hb))
  · exact hbound (holds_four_of_repeated_spectrum a b U hU (Or.inl ha))

end

end MOC
