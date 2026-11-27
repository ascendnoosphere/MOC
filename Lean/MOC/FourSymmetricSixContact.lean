import MOC.FourMatchingHessian
import MOC.FourTwoBudgetMinor

/-! The seven ordinary budgets of the symmetric six-contact family. The radial
cubic gives a necessary height and a singular Hessian. The unitary support
proof below applies when one compensator can share its budget with the other two. -/

namespace MOC

open BigOperators Matrix

noncomputable section

/-- Row sets of the nine squared minors. The order of the first seven
follows ordinary rays 0, 7, 10, 13, 18, 23, and 28. -/
def symmetricSixContactRows : Fin 9 → Finset (Fin 4) :=
  ![{0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {0, 1}, {0, 2}]

/-- Column sets paired with the row sets of the nine squared minors. -/
def symmetricSixContactCols : Fin 9 → Finset (Fin 4) :=
  ![{0}, {3}, {2}, {1}, {0, 3}, {0, 2}, {0, 1}, {0, 2}, {1, 2}]

/-- The mixed ray is the sum of rays 7, 10, and 17 minus ray 25.
The last two entries are its two additional signed minors. -/
def symmetricSixContactWeights (b : Fin 7 → ℝ) (mixedWeight : ℝ) : Fin 9 → ℝ :=
  ![b 0, b 1 + mixedWeight, b 2 + mixedWeight, b 3, b 4, b 5, b 6, mixedWeight, -mixedWeight]

/-- The reference matchings have lexicographic row-to-column order.
The signed moment convention acts from columns to rows. -/
def symmetricSixContactProfile (b : Fin 7 → ℝ) (mixedWeight : ℝ) (i : Fin 24) : ℝ :=
  ∑ k, if (symmetricSixContactCols k).map (fourPerm i).symm.toEmbedding =
    symmetricSixContactRows k then symmetricSixContactWeights b mixedWeight k else 0

/-- The real noncrossing coordinates of the profile after subtraction
of its common height. -/
def symmetricSixContactLift (b : Fin 7 → ℝ) (mixedWeight h : ℝ) : Fin 14 → ℝ :=
  ![mixedWeight + b 5, -b 5 - b 6, b 1, b 6, b 0, -b 4 - b 5, -mixedWeight + b 5,
    -b 1 - b 2 - mixedWeight, b 2, b 2 + mixedWeight, b 4, -b 2 - b 3 - mixedWeight, b 3, -h]

/-- The squared-minor indicators at each lexicographic permutation. -/
def symmetricSixContactActiveMinors : Fin 24 → Finset (Fin 9) :=
  ![{0, 2, 5}, {0}, {0, 7}, {0, 3, 6, 7}, {0, 1, 4}, {0, 1, 2, 3, 4, 5, 6},
    {2, 8}, ∅, ∅, {6}, {1}, {1, 2, 6, 8}, {7, 8}, {3, 7}, {5}, ∅,
    {1, 3, 5}, {1, 8}, {4}, {2, 3, 4}, ∅, {2}, {3}, ∅]

theorem symmetricSixContactMinorAgreement : ∀ i k,
    (symmetricSixContactCols k).map (fourPerm i).symm.toEmbedding =
      symmetricSixContactRows k ↔ k ∈ symmetricSixContactActiveMinors i := by
  decide +kernel

set_option maxHeartbeats 2000000 in
/-- Evaluating the lift gives the actual affine profile, including on
all coefficient boundaries. -/
theorem symmetricSixContactLift_evaluation (b : Fin 7 → ℝ) (mixedWeight h : ℝ) (i : Fin 24) :
    fourMatchingEvaluation (symmetricSixContactLift b mixedWeight h) i =
      symmetricSixContactProfile b mixedWeight i - h := by
  simp only [symmetricSixContactProfile, symmetricSixContactMinorAgreement,
    ← Finset.sum_filter, Finset.filter_univ_mem]
  fin_cases i <;>
    simp (disch := decide) only [fourMatchingEvaluation, symmetricSixContactActiveMinors,
      Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero', Finset.sum_insert,
      Finset.sum_singleton, Finset.sum_empty] <;>
    dsimp only [symmetricSixContactLift, symmetricSixContactWeights, Matrix.cons_val] <;>
    ring

/-- The numerator in the spectral height formula. -/
def symmetricSixContactHeightNumerator (b : Fin 7 → ℝ) (mixedWeight : ℝ) : ℝ :=
  mixedWeight ^ 3 + (b 0 + b 1 + b 2 + b 3) * mixedWeight ^ 2 +
    (b 0 * b 1 + b 0 * b 2 + b 0 * b 3 + b 1 * b 2 + b 1 * b 3 + b 2 * b 3) * mixedWeight +
    (b 0 * b 1 * b 2 + b 0 * b 1 * b 3 + b 0 * b 2 * b 3 + b 1 * b 2 * b 3) +
    b 4 * b 5 * b 6

/-- The denominator in the spectral height formula. -/
def symmetricSixContactHeightDenominator (b : Fin 7 → ℝ) (mixedWeight : ℝ) : ℝ :=
  mixedWeight ^ 2 + b 4 * b 5 + b 4 * b 6 + b 5 * b 6

theorem symmetricSixContactLift_cubic (b : Fin 7 → ℝ) (mixedWeight h : ℝ) :
    fourMatchingCubic (symmetricSixContactLift b mixedWeight h) =
      h * symmetricSixContactHeightDenominator b mixedWeight - symmetricSixContactHeightNumerator b mixedWeight := by
  simp only [fourMatchingCubic, symmetricSixContactLift, Matrix.cons_val,
    symmetricSixContactHeightNumerator, symmetricSixContactHeightDenominator]
  ring

private theorem symmetricSixContactLift_eq_spectral
    (a c : Fin 4 → ℂ) (η : ℂ) (b : Fin 7 → ℝ) (mixedWeight h : ℝ)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b mixedWeight i) :
    symmetricSixContactLift b mixedWeight h = fun j =>
      (η * fourNoncrossingCoordinates (fourSpectralPoints a c) j).re := by
  apply fourMatchingEvaluation_injective
  funext i
  rw [symmetricSixContactLift_evaluation, ← hgap i, fourMatchingEvaluation_spectral_real_part]
  exact add_sub_cancel_right _ _

/-- A positive mixed coefficient forces the common height formula.
This uses only spectral cubic vanishing and retains repeated eigenvalues. -/
theorem symmetricSixContact_spectralHeight
    (a c : Fin 4 → ℂ) (η : ℂ) (b : Fin 7 → ℝ) {mixedWeight h : ℝ}
    (hb : ∀ k, 0 ≤ b k) (hMixedWeight : 0 < mixedWeight)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b mixedWeight i) :
    h = symmetricSixContactHeightNumerator b mixedWeight / symmetricSixContactHeightDenominator b mixedWeight ∧
    0 < h := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  have h5 := hb 5
  have h6 := hb 6
  have hD : 0 < symmetricSixContactHeightDenominator b mixedWeight := by
    unfold symmetricSixContactHeightDenominator
    positivity
  have hN : 0 < symmetricSixContactHeightNumerator b mixedWeight := by
    unfold symmetricSixContactHeightNumerator
    positivity
  have hcubic : fourMatchingCubic (symmetricSixContactLift b mixedWeight h) = 0 := by
    rw [symmetricSixContactLift_eq_spectral a c η b mixedWeight h hgap]
    exact fourMatchingCubic_of_spectral_real_part a c η
  rw [symmetricSixContactLift_cubic] at hcubic
  have hh : h = symmetricSixContactHeightNumerator b mixedWeight /
      symmetricSixContactHeightDenominator b mixedWeight :=
    (eq_div_iff (ne_of_gt hD)).mpr (sub_eq_zero.mp hcubic)
  exact ⟨hh, hh.symm ▸ div_pos hN hD⟩

/-- The Hessian obstruction holds for the eight-ray profile and
for every real mixed coefficient. -/
theorem symmetricSixContact_spectralHessian_singular
    (a c : Fin 4 → ℂ) (η : ℂ) (b : Fin 7 → ℝ) (mixedWeight h : ℝ)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b mixedWeight i) :
    (fourMatchingHessian (symmetricSixContactLift b mixedWeight h)).det = 0 := by
  rw [symmetricSixContactLift_eq_spectral a c η b mixedWeight h hgap]
  exact fourMatchingHessian_det_spectral_real_part_eq_zero a c η

private abbrev MinorTable (R : Type*) := Finset (Fin 4) → Finset (Fin 4) → R

private def contactMinor {R : Type*} (m : MinorTable R) (k : Fin 9) : R :=
  m (symmetricSixContactRows k) (symmetricSixContactCols k)

private def contactMixed {R : Type*} [AddGroup R] (m : MinorTable R) : R :=
  contactMinor m 1 + contactMinor m 2 + contactMinor m 7 - contactMinor m 8

private def twoBudgetMixed {R : Type*} [AddGroup R] (m : MinorTable R) : R :=
  m {0} {2} + m {1} {3} + m {1, 3} {1, 2} - m {1, 2} {1, 3}

private def edgeRows : Fin 3 → FourPerm := ![fourPerm 3, fourPerm 0, fourPerm 15]
private def edgeCols : Fin 3 → FourPerm := ![fourPerm 10, fourPerm 14, fourPerm 6]
private def edgeFirst : Fin 3 → Fin 9 := ![5, 4, 6]
private def edgeSecond : Fin 3 → Fin 9 := ![4, 6, 5]

private def edgeTable {R : Type*} (edge : Fin 3) (m : MinorTable R) : MinorTable R :=
  fun I J => m (I.map (edgeRows edge).toEmbedding) (J.map (edgeCols edge).toEmbedding)

private def permutationMinorTable {R : Type*} [Zero R] [One R] (σ : FourPerm) : MinorTable R :=
  fun I J => if J.map σ.toEmbedding = I then 1 else 0

private theorem edgeProfileInteger : ∀ (edge : Fin 3) (i : Fin 24),
    let m : MinorTable ℤ := permutationMinorTable (fourPerm i).symm
    twoBudgetMixed (edgeTable edge m) = contactMixed m ∧
      edgeTable edge m {0, 1} {2, 3} = contactMinor m (edgeFirst edge) ∧
      edgeTable edge m {0, 3} {1, 2} = contactMinor m (edgeSecond edge) := by
  decide +kernel

private theorem cast_permutationMinorTable (σ : FourPerm) (I J : Finset (Fin 4)) :
    ((permutationMinorTable σ I J : ℤ) : ℝ) = permutationMinorTable σ I J := by
  unfold permutationMinorTable
  split_ifs <;> norm_num

private theorem edgeProfileReal (edge : Fin 3) (σ : FourPerm) :
    let m : MinorTable ℝ := permutationMinorTable σ
    twoBudgetMixed (edgeTable edge m) = contactMixed m ∧
      edgeTable edge m {0, 1} {2, 3} = contactMinor m (edgeFirst edge) ∧
      edgeTable edge m {0, 3} {1, 2} = contactMinor m (edgeSecond edge) := by
  obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
  have hs : (fourPerm i).symm = σ := by rw [hi, Equiv.symm_symm]
  rw [← hs]
  obtain ⟨hm, hf, ht⟩ := edgeProfileInteger edge i
  refine ⟨?_, ?_, ?_⟩
  · simpa only [twoBudgetMixed, contactMixed, edgeTable, contactMinor, Int.cast_add, Int.cast_sub,
      cast_permutationMinorTable] using congrArg (fun z : ℤ => (z : ℝ)) hm
  · simpa only [edgeTable, contactMinor, cast_permutationMinorTable]
      using congrArg (fun z : ℤ => (z : ℝ)) hf
  · simpa only [edgeTable, contactMinor, cast_permutationMinorTable]
      using congrArg (fun z : ℤ => (z : ℝ)) ht

private theorem minorTable_signed_sum (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    subsetMinorSq U = ∑ σ : FourPerm, realSignedWeight U σ • permutationMinorTable σ := by
  funext I J
  have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
  simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re, Complex.ofReal_re,
    realSignedWeight] at h
  rw [← h]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, permutationMinorTable, mul_ite,
    mul_one, mul_zero, realSignedWeight]

private theorem edgeUnitary (edge : Fin 3) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let m := subsetMinorSq U
    twoBudgetMixed (edgeTable edge m) = contactMixed m ∧
      edgeTable edge m {0, 1} {2, 3} = contactMinor m (edgeFirst edge) ∧
      edgeTable edge m {0, 3} {1, 2} = contactMinor m (edgeSecond edge) := by
  dsimp only
  rw [minorTable_signed_sum U hU]
  constructor
  · simp only [twoBudgetMixed, contactMixed, edgeTable, contactMinor, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← mul_add, ← mul_sub]
    apply Finset.sum_congr rfl
    intro σ _
    exact congrArg (fun z => realSignedWeight U σ * z) (edgeProfileReal edge σ).1
  · constructor
    · simp only [edgeTable, contactMinor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun σ _ =>
        congrArg (fun z => realSignedWeight U σ * z) (edgeProfileReal edge σ).2.1)
    · simp only [edgeTable, contactMinor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun σ _ =>
        congrArg (fun z => realSignedWeight U σ * z) (edgeProfileReal edge σ).2.2)

private theorem edge_nonneg (edge : Fin 3) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) {u v mixedWeight : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hMixedWeight : 0 ≤ mixedWeight)
    (hcap : mixedWeight ^ 2 ≤ u * v) :
    0 ≤ u * contactMinor (subsetMinorSq U) (edgeFirst edge) +
      v * contactMinor (subsetMinorSq U) (edgeSecond edge) +
      mixedWeight * contactMixed (subsetMinorSq U) := by
  let V := U.submatrix (edgeRows edge) (edgeCols edge)
  let m := subsetMinorSq V
  have h := four_two_budget_minor_nonneg hu hv hMixedWeight hcap V
    (unitary_reindex (edgeRows edge) (edgeCols edge) hU)
  change 0 ≤ u * m {0, 1} {2, 3} + v * m {0, 3} {1, 2} + mixedWeight * twoBudgetMixed m at h
  have hm : m = edgeTable edge (subsetMinorSq U) := by
    funext I J
    exact squared_minor_reindex (edgeRows edge) (edgeCols edge) U hU I J
  obtain ⟨hg, hf, hs⟩ := edgeUnitary edge U hU
  rw [hm, hg, hf, hs] at h
  exact h

private theorem star_nonneg {p q r mixedWeight X Y Z F : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hcap : mixedWeight ^ 2 ≤ p * (q + r))
    (hXY : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → mixedWeight ^ 2 ≤ u * v →
      0 ≤ u * X + v * Y + mixedWeight * F)
    (hXZ : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → mixedWeight ^ 2 ≤ u * v →
      0 ≤ u * X + v * Z + mixedWeight * F) :
    0 ≤ p * X + q * Y + r * Z + mixedWeight * F := by
  by_cases hzero : q + r = 0
  · have hMixedWeightZero : mixedWeight = 0 := by
      rw [hzero, mul_zero] at hcap
      exact sq_eq_zero_iff.mp (le_antisymm hcap (sq_nonneg mixedWeight))
    rw [hMixedWeightZero, zero_mul, add_zero]
    positivity
  have ht : 0 < q + r := lt_of_le_of_ne (add_nonneg hq hr) (Ne.symm hzero)
  let u := mixedWeight ^ 2 / (q + r)
  have hu : 0 ≤ u := div_nonneg (sq_nonneg mixedWeight) ht.le
  have heq : u * (q + r) = mixedWeight ^ 2 := div_mul_cancel₀ _ hzero
  have hXY' := mul_nonneg hq (hXY u (q + r) hu ht.le heq.ge)
  have hXZ' := mul_nonneg hr (hXZ u (q + r) hu ht.le heq.ge)
  have hbudget : 0 ≤ (p * (q + r) - u * (q + r)) * X := by
    rw [heq]
    exact mul_nonneg (sub_nonneg.mpr hcap) hX
  refine nonneg_of_mul_nonneg_left ?_ ht
  calc
    0 ≤ q * (u * X + (q + r) * Y + mixedWeight * F) +
        r * (u * X + (q + r) * Z + mixedWeight * F) +
        (p * (q + r) - u * (q + r)) * X :=
      add_nonneg (add_nonneg hXY' hXZ') hbudget
    _ = (p * X + q * Y + r * Z + mixedWeight * F) * (q + r) := by ring

/-- Weighted compensation settles the symmetric six-contact gap when any
one of the three compensator coefficients has enough budget to work with
the sum of the other two. The first four ordinary coefficients are independent. -/
theorem symmetricSixContact_support_of_compensator_budget
    (a c : Fin 4 → ℂ) (η : ℂ) (b : Fin 7 → ℝ) {mixedWeight h : ℝ}
    (hb : ∀ k, 0 ≤ b k) (hMixedWeight : 0 ≤ mixedWeight)
    (hgap : ∀ i, (η * matchingProduct a c (fourPerm i).symm).re + h =
      symmetricSixContactProfile b mixedWeight i)
    (hcap : mixedWeight ^ 2 ≤ b 4 * (b 5 + b 6) ∨
      mixedWeight ^ 2 ≤ b 5 * (b 4 + b 6) ∨ mixedWeight ^ 2 ≤ b 6 * (b 4 + b 5))
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    -h ≤ (η * determinantValue a c U).re := by
  let m := subsetMinorSq U
  let X := contactMinor m 4
  let Y := contactMinor m 5
  let Z := contactMinor m 6
  let F := contactMixed m
  have hX : 0 ≤ X := subsetMinorSq_nonneg U _ _
  have hY : 0 ≤ Y := subsetMinorSq_nonneg U _ _
  have hZ : 0 ≤ Z := subsetMinorSq_nonneg U _ _
  have hYX (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : mixedWeight ^ 2 ≤ u * v) :
      0 ≤ u * Y + v * X + mixedWeight * F := edge_nonneg 0 U hU hu hv hMixedWeight hc
  have hXZ (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : mixedWeight ^ 2 ≤ u * v) :
      0 ≤ u * X + v * Z + mixedWeight * F := edge_nonneg 1 U hU hu hv hMixedWeight hc
  have hZY (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : mixedWeight ^ 2 ≤ u * v) :
      0 ≤ u * Z + v * Y + mixedWeight * F := edge_nonneg 2 U hU hu hv hMixedWeight hc
  have hXY (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : mixedWeight ^ 2 ≤ u * v) :
      0 ≤ u * X + v * Y + mixedWeight * F := by
    rw [add_comm (u * X)]
    exact hYX v u hv hu (by rwa [mul_comm])
  have hYZ (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : mixedWeight ^ 2 ≤ u * v) :
      0 ≤ u * Y + v * Z + mixedWeight * F := by
    rw [add_comm (u * Y)]
    exact hZY v u hv hu (by rwa [mul_comm])
  have hZX (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : mixedWeight ^ 2 ≤ u * v) :
      0 ≤ u * Z + v * X + mixedWeight * F := by
    rw [add_comm (u * Z)]
    exact hXZ v u hv hu (by rwa [mul_comm])
  have htriangle : 0 ≤ b 4 * X + b 5 * Y + b 6 * Z + mixedWeight * F := by
    rcases hcap with hcap | hcap | hcap
    · exact star_nonneg (hb 4) (hb 5) (hb 6) hX hY hZ hcap hXY hXZ
    · rw [add_comm (b 4 * X) (b 5 * Y)]
      exact star_nonneg (hb 5) (hb 4) (hb 6) hY hX hZ hcap hYX hYZ
    · have he : b 4 * X + b 5 * Y + b 6 * Z + mixedWeight * F =
          b 6 * Z + b 4 * X + b 5 * Y + mixedWeight * F := by ring
      rw [he]
      exact star_nonneg (hb 6) (hb 4) (hb 5) hZ hX hY hcap hZX hZY
  have hdecomp (σ : FourPerm) : (η * matchingProduct a c σ).re - (-h) =
      ∑ k, if (symmetricSixContactCols k).map σ.toEmbedding = symmetricSixContactRows k
        then symmetricSixContactWeights b mixedWeight k else 0 := by
    obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
    have hs : (fourPerm i).symm = σ := by rw [hi, Equiv.symm_symm]
    rw [← hs, sub_neg_eq_add]
    exact hgap i
  apply sub_nonneg.mp
  rw [gap_eq_minor_decomposition a c η (-h) U hU symmetricSixContactRows
    symmetricSixContactCols (symmetricSixContactWeights b mixedWeight) hdecomp]
  change 0 ≤ ∑ k, symmetricSixContactWeights b mixedWeight k * contactMinor m k
  have hrest (k : Fin 9) : 0 ≤ contactMinor m k := subsetMinorSq_nonneg U _ _
  have hsum : (∑ k, symmetricSixContactWeights b mixedWeight k * contactMinor m k) =
      (b 4 * X + b 5 * Y + b 6 * Z + mixedWeight * F) +
      (b 0 * contactMinor m 0 + b 1 * contactMinor m 1 +
        b 2 * contactMinor m 2 + b 3 * contactMinor m 3) := by
    let values : Fin 9 → ℝ := ![contactMinor m 0, contactMinor m 1, contactMinor m 2,
      contactMinor m 3, contactMinor m 4, contactMinor m 5, contactMinor m 6,
      contactMinor m 7, contactMinor m 8]
    have hvalues (k : Fin 9) : contactMinor m k = values k := by
      fin_cases k <;> rfl
    simp only [X, Y, Z, F, contactMixed, hvalues]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, symmetricSixContactWeights,
      values, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    ring
  rw [hsum]
  exact add_nonneg htriangle
    (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (hb 0) (hrest 0))
      (mul_nonneg (hb 1) (hrest 1))) (mul_nonneg (hb 2) (hrest 2))) (mul_nonneg (hb 3) (hrest 3)))

end

end MOC
