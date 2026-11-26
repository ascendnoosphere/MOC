import MOC.FourMinorCertificate
import MOC.FourMinorGeometricMean
import MOC.FourSignedHeightReduction

/-! The signed minor identity gives an exact scalar test for lower support. -/

open BigOperators

namespace MOC

noncomputable section

/-- The gap above the projected value of the matching r. -/
def fourSignedGap (a b : Fin 4 → ℂ) (η : ℂ) (r : FourPerm) (p : Fin 24) : ℝ :=
  (η * matchingProduct a b (fourPerm p).symm).re - (η * matchingProduct a b r).re

/-- The signed gap at 1423 minus the gaps at 4123, 2314, 3421, and 1432. -/
def fourSignedGapHeight (f : Fin 24 → ℝ) : ℝ :=
  f 4 - f 18 - f 8 - f 17 - f 5

/-- The ordinary contribution in the signed identity. -/
def fourSignedWeightedGap (U : Matrix (Fin 4) (Fin 4) ℂ) (f : Fin 24 → ℝ) : ℝ :=
  ∑ i : Fin 13, fourSignedMinorWeight U i * f (fourSignedMinorIndex i)

/-- The signed expansion has mass one. -/
theorem fourSignedMinorMass (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    (∑ i : Fin 13, fourSignedMinorWeight U i) + 3 * fourSignedMinorCorrection U = 1 := by
  have h := fourSignedMinorProjection (fun _ => (1 : ℂ)) (fun _ => (0 : ℂ)) U hU 1
  have hd : Matrix.diagonal (fun _ : Fin 4 => (1 : ℂ)) = 1 := by
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hz : Matrix.diagonal (fun _ : Fin 4 => (0 : ℂ)) = 0 := Matrix.diagonal_zero
  have hc : fourSignedMinorCombination (fun _ => (1 : ℝ)) = 3 := by
    rw [fourSignedMinorCombination_apply]
    norm_num
  simp only [one_mul, matchingProduct, add_zero, Finset.prod_const_one, Complex.one_re,
    mul_one, determinantValue, hd, hz, mul_zero, zero_mul, Matrix.det_one, hc] at h
  calc
    _ = (∑ i : Fin 13, fourSignedMinorWeight U i) + fourSignedMinorCorrection U * 3 := by ring
    _ = 1 := h.symm

/-- A minimum matching gives nonnegative gaps. -/
theorem fourSignedGap_nonneg (a b : Fin 4 → ℂ) (η : ℂ) (r : FourPerm)
    (hmin : ∀ σ, (η * matchingProduct a b r).re ≤ (η * matchingProduct a b σ).re)
    (p : Fin 24) : 0 ≤ fourSignedGap a b η r p :=
  sub_nonneg.mpr (hmin (fourPerm p).symm)

/-- The ordinary contribution is nonnegative on nonnegative gaps. -/
theorem fourSignedWeightedGap_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (f : Fin 24 → ℝ) (hf : ∀ p, 0 ≤ f p) :
    0 ≤ fourSignedWeightedGap U f :=
  Finset.sum_nonneg fun i _ => mul_nonneg (fourSignedMinorWeight_nonneg U hU i) (hf _)

/-- The directional lower bound is equivalent to the signed height inequality. -/
theorem fourSignedHeight_iff (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (η : ℂ) (r : FourPerm)
    (hmin : ∀ σ, (η * matchingProduct a b r).re ≤ (η * matchingProduct a b σ).re) :
    let f := fourSignedGap a b η r
    (η * matchingProduct a b r).re ≤ (η * determinantValue a b U).re ↔
      fourSignedMinorCorrection U * fourSignedGapHeight f ≤ fourSignedWeightedGap U f := by
  let f := fourSignedGap a b η r
  have hform :
      (fun p : Fin 24 => -(η * matchingProduct a b r).re -
        ((-η) * matchingProduct a b (fourPerm p).symm).re) = f := by
    funext p
    simp only [f, fourSignedGap, neg_mul, Complex.neg_re]
    ring
  have hg := fourSpectralGap_mem_supportCost a b (-η) r (fun σ => by
    simpa only [matchingGap, neg_mul, Complex.neg_re, sub_nonneg, neg_le_neg_iff] using hmin σ)
  have hgf : FourSupportCost f := by
    rw [← hform]
    simpa only [matchingGap, neg_mul, Complex.neg_re] using hg
  obtain ⟨⟨m, hm⟩, _⟩ := hgf
  have hspan : f ∈ Submodule.span ℝ (Set.range ordinaryCostRay) := by
    rw [← hm]
    exact fourMatchingEvaluation_mem_ordinarySpan m
  have hvalue := fourSupportCostValue_spectral_eq a b (-η) (-(η * matchingProduct a b r).re) U hU
  rw [hform, neg_mul, Complex.neg_re] at hvalue
  have hc : fourSignedMinorCombination f = -fourSignedGapHeight f := by
    rw [fourSignedMinorCombination_apply, fourSignedGapHeight]
    ring
  rw [fourSignedMinorEvaluation U f hspan, hc, mul_neg] at hvalue
  change _ ↔ fourSignedMinorCorrection U * fourSignedGapHeight f ≤ fourSignedWeightedGap U f
  unfold fourSignedWeightedGap
  constructor <;> intro h <;> linarith only [h, hvalue]

/-- A violation on the positive-correction branch has positive signed height. -/
theorem fourSignedHeight_pos_of_violation (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (η : ℂ) (r : FourPerm)
    (hmin : ∀ σ, (η * matchingProduct a b r).re ≤ (η * matchingProduct a b σ).re)
    (hq : 0 < fourSignedMinorCorrection U)
    (hv : (η * determinantValue a b U).re < (η * matchingProduct a b r).re) :
    0 < fourSignedGapHeight (fourSignedGap a b η r) := by
  have hf := fourSignedGap_nonneg a b η r hmin
  have hbad := lt_of_not_ge fun he => (not_le_of_gt hv)
    ((fourSignedHeight_iff a b U hU η r hmin).mpr he)
  exact pos_of_mul_pos_right ((fourSignedWeightedGap_nonneg U hU _ hf).trans_lt hbad) hq.le

/-- The two geometric mean estimates imply the signed height bound for a fixed gap. -/
theorem fourSignedHeight_le_of_geometric_mean (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (f : Fin 24 → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hq : 0 ≤ fourSignedMinorCorrection U)
    (hspectral : fourSignedGapHeight f ≤ Real.sqrt (f 17 * f 22)) :
    fourSignedMinorCorrection U * fourSignedGapHeight f ≤ fourSignedWeightedGap U f := by
  let w := fourSignedMinorWeight U
  have hw := fourSignedMinorWeight_nonneg U hU
  have hmatrix : fourSignedMinorCorrection U ≤ 2 * Real.sqrt (w 8 * w 11) := by
    change fourSignedMinorCorrection U ≤
      2 * Real.sqrt (fourSignedMinorWeight U 8 * fourSignedMinorWeight U 11)
    rw [fourSignedMinorCorrection_eq_minors U hU, fourSignedMinorWeight_eq_minor U hU 8,
      fourSignedMinorWeight_eq_minor U hU 11]
    exact four_minor_geometric_mean U hU
  let x := w 8 * f 17
  let y := w 11 * f 22
  have hx : 0 ≤ x := mul_nonneg (hw 8) (hf 17)
  have hy : 0 ≤ y := mul_nonneg (hw 11) (hf 22)
  have hproducts : (w 8 * w 11) * (f 17 * f 22) = x * y := by
    dsimp only [x, y]
    ring
  have hamp : 2 * Real.sqrt (x * y) ≤ x + y := by
    rw [Real.sqrt_mul hx]
    nlinarith only [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx, Real.sq_sqrt hy]
  have hpart : x + y ≤ fourSignedWeightedGap U f := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({8, 11} : Finset (Fin 13)))
      (f := fun i => w i * f (fourSignedMinorIndex i))
      (fun i _ _ => mul_nonneg (hw i) (hf _))
    have h₈ : fourSignedMinorIndex 8 = 17 := by decide +kernel
    have h₁₁ : fourSignedMinorIndex 11 = 22 := by decide +kernel
    simpa only [Finset.sum_pair (show (8 : Fin 13) ≠ 11 by decide), h₈, h₁₁,
      x, y, w, fourSignedWeightedGap] using h
  calc
    _ ≤ fourSignedMinorCorrection U * Real.sqrt (f 17 * f 22) :=
      mul_le_mul_of_nonneg_left hspectral hq
    _ ≤ (2 * Real.sqrt (w 8 * w 11)) * Real.sqrt (f 17 * f 22) :=
      mul_le_mul_of_nonneg_right hmatrix (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (x * y) := by
      rw [← hproducts, Real.sqrt_mul (mul_nonneg (hw 8) (hw 11)), mul_assoc]
    _ ≤ x + y := hamp
    _ ≤ _ := hpart

/-- The 48 relabelings reduce order four to the branch where both factors are positive. -/
theorem conjecture_four_iff_signed_height_bound :
    Conjecture (Fin 4) ↔
      ∀ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U →
        0 < fourSignedMinorCorrection U → ∀ (η : ℂ) (r : FourPerm),
          (∀ σ, (η * matchingProduct a b r).re ≤ (η * matchingProduct a b σ).re) →
          let f := fourSignedGap a b η r
          0 < fourSignedGapHeight f →
          fourSignedMinorCorrection U * fourSignedGapHeight f ≤ fourSignedWeightedGap U f := by
  classical
  constructor
  · intro h a b U hU _ η r hmin _
    exact (fourSignedHeight_iff a b U hU η r hmin).mp
      (four_lower_support_of_holds a b η (η * matchingProduct a b r).re U (h a b U hU)
        (fun i => hmin (fourPerm i).symm))
  · intro h
    apply conjecture_four_iff_positive_signed_minor.mpr
    intro a b U hU hq
    apply (holds_iff_directional a b U).mpr
    intro η
    obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ
      (fun σ : FourPerm => (η * matchingProduct a b σ).re)
      ⟨1, Finset.mem_univ _⟩
    have hmin (σ : FourPerm) :
        ((-η) * matchingProduct a b r).re ≤ ((-η) * matchingProduct a b σ).re := by
      simpa only [neg_mul, Complex.neg_re, neg_le_neg_iff] using hr σ (Finset.mem_univ σ)
    refine ⟨r, ?_⟩
    by_contra! hlt
    have hfail : ((-η) * determinantValue a b U).re < ((-η) * matchingProduct a b r).re := by
      simpa only [neg_mul, Complex.neg_re, neg_lt_neg_iff] using hlt
    have hheight := fourSignedHeight_pos_of_violation a b U hU (-η) r hmin hq hfail
    exact (not_le_of_gt hfail) ((fourSignedHeight_iff a b U hU (-η) r hmin).mpr
      (h a b U hU hq (-η) r hmin hheight))

/-! Remaining goal.
Prove the signed height bound for all spectral gaps in the equivalence.
The spectral geometric mean bound fails. See
`exists_four_spectral_geometric_mean_counterexample`.
-/

end

end MOC
