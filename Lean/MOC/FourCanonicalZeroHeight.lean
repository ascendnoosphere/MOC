import MOC.FourMatchingRelations
import MOC.FourTerminalCoverage
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Positivity

/-! The canonical mixed profile at zero support height. The matching cubic
gives three possible compensation budgets. Rectangle closure excludes all
three budgets when at least eight matching products lie on the support line. -/

open BigOperators

namespace MOC

noncomputable section

/-- The thirteen ordinary rays in the canonical mixed profile, in increasing
order. The argument of `fourCanonicalZeroHeightProfile` uses this order. -/
def fourCanonicalZeroHeightRay (j : Fin 13) : Fin 34 :=
  ![0, 7, 10, 13, 17, 18, 20, 22, 23, 27, 28, 30, 31] j

/-- The mixed coefficient is one. The supplied coefficients are the budgets
of the ordinary rays. -/
def fourCanonicalZeroHeightProfile (c : Fin 13 → ℝ) (p : Fin 24) : ℝ :=
  mixedCostRay 0 p + ∑ j, c j * ordinaryCostRay (fourCanonicalZeroHeightRay j) p

private def zeroHeightLift (c : Fin 13 → ℝ) : Fin 14 → ℝ :=
  ![c 11 + c 12 + c 8 + 1, -c 10 + c 7 - c 8 + c 9, c 1 - c 11, c 10 - c 9,
    c 0 - c 12, c 4 - c 5 + c 6 - c 8, -c 4 - c 6 - c 7 + c 8 - c 9 - 1,
    -c 1 - c 2 - c 6 - 1, -c 12 + c 2, c 2 + c 6 + c 9 + 1, c 5 - c 6,
    -c 2 - c 3 - c 9 - 1, -c 11 + c 3, c 11]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem zeroHeightLift_eval (c : Fin 13 → ℝ) (p : Fin 24) :
    fourMatchingEvaluation (zeroHeightLift c) p = fourCanonicalZeroHeightProfile c p := by
  fin_cases p <;>
    norm_num [fourMatchingEvaluation, zeroHeightLift, fourCanonicalZeroHeightProfile,
      fourCanonicalZeroHeightRay, mixedCostRay, mixedCostRayInt, mixedCostSeedInt,
      ordinaryCostRay, ordinaryCostRayInt, fourCostRelabelIndex, fourCostPermutation,
      fourCostPair, fourPermIndex, fourPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      Fin.sum_univ_succ, Matrix.cons_val] <;> ring

private def compensation (center x y : ℝ) : ℝ :=
  center * x * y - (x * y + x + y)

private def canonicalCubicRemainder (c : Fin 13 → ℝ) : ℝ :=
  c 9 * c 12 + c 9 * c 11 + c 9 * c 11 * c 12 + c 7 * c 12 +
  c 7 * c 11 + c 7 * c 11 * c 12 + c 7 * c 9 * c 12 + c 7 * c 9 * c 11 +
  c 6 * c 12 + c 6 * c 11 + c 6 * c 11 * c 12 + c 6 * c 9 +
  c 6 * c 9 * c 11 + c 6 * c 7 + c 6 * c 7 * c 12 + c 6 * c 7 * c 9 +
  c 5 * c 8 * c 10 + c 4 * c 12 + c 4 * c 11 + c 4 * c 11 * c 12 +
  c 4 * c 9 + c 4 * c 9 * c 12 + c 4 * c 7 + c 4 * c 7 * c 11 +
  c 4 * c 7 * c 9 + c 4 * c 6 * c 12 + c 4 * c 6 * c 11 + c 4 * c 6 * c 9 +
  c 4 * c 6 * c 7 + c 3 + c 3 * c 11 + c 3 * c 7 +
  c 3 * c 7 * c 11 + c 3 * c 6 + c 3 * c 6 * c 11 + c 3 * c 6 * c 7 +
  c 2 + c 2 * c 12 + c 2 * c 7 + c 2 * c 7 * c 12 +
  c 2 * c 4 + c 2 * c 4 * c 12 + c 2 * c 4 * c 7 + c 2 * c 3 +
  c 2 * c 3 * c 7 + c 1 + c 1 * c 11 + c 1 * c 9 +
  c 1 * c 9 * c 11 + c 1 * c 4 + c 1 * c 4 * c 11 + c 1 * c 4 * c 9 +
  c 1 * c 3 + c 1 * c 3 * c 11 + c 1 * c 2 + c 1 * c 2 * c 4 +
  c 1 * c 2 * c 3 + c 0 + c 0 * c 12 + c 0 * c 9 +
  c 0 * c 9 * c 12 + c 0 * c 6 + c 0 * c 6 * c 12 + c 0 * c 6 * c 9 +
  c 0 * c 3 + c 0 * c 3 * c 6 + c 0 * c 2 + c 0 * c 2 * c 12 +
  c 0 * c 2 * c 3 + c 0 * c 1 + c 0 * c 1 * c 9 + c 0 * c 1 * c 3 +
  c 0 * c 1 * c 2

private theorem zeroHeightLift_cubic (c : Fin 13 → ℝ) :
    fourMatchingCubic (zeroHeightLift c) =
      compensation (c 10) (c 4) (c 6) + compensation (c 8) (c 11) (c 12) +
        compensation (c 5) (c 7) (c 9) - 1 - canonicalCubicRemainder c := by
  simp only [fourMatchingCubic, zeroHeightLift, Matrix.cons_val, compensation,
    canonicalCubicRemainder]
  ring

private theorem canonicalCubicRemainder_nonneg (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j) :
    0 ≤ canonicalCubicRemainder c := by
  have h₀ := hc 0
  have h₁ := hc 1
  have h₂ := hc 2
  have h₃ := hc 3
  have h₄ := hc 4
  have h₅ := hc 5
  have h₆ := hc 6
  have h₇ := hc 7
  have h₈ := hc 8
  have h₉ := hc 9
  have h₁₀ := hc 10
  have h₁₁ := hc 11
  have h₁₂ := hc 12
  unfold canonicalCubicRemainder
  positivity

private theorem positive_compensation {center x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : 0 < compensation center x y) :
    0 < x ∧ 0 < y ∧ x * y + x + y < center * x * y := by
  have hxne : x ≠ 0 := by
    intro he
    simp only [compensation, he, mul_zero, zero_mul, zero_add, zero_sub] at h
    linarith only [h, hy]
  have hyne : y ≠ 0 := by
    intro he
    simp only [compensation, he, mul_zero, add_zero, zero_add, zero_sub] at h
    linarith only [h, hx]
  exact ⟨lt_of_le_of_ne hx hxne.symm, lt_of_le_of_ne hy hyne.symm, sub_pos.mp h⟩

private theorem compensation_center_ne_zero {center x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x * y + x + y < center * x * y) : center ≠ 0 := by
  intro he
  have hnonneg : 0 ≤ x * y + x + y := by positivity
  simp only [he, zero_mul] at h
  exact (not_lt_of_ge hnonneg) h

/-- A canonical mixed profile realized by the real parts of matching products
supplies one of three strict compensation budgets. For each budget, the
conclusion lists the two leaf coefficients and the inequality on the
coefficient of the ordinary ray shared by the leaves. -/
theorem fourCanonicalZeroHeight_compensation (a b : Fin 4 → ℂ) (η : ℂ)
    (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hvalues : ∀ p : Fin 24, (η * matchingProduct a b (fourPerm p).symm).re =
      fourCanonicalZeroHeightProfile c p) :
    (0 < c 4 ∧ 0 < c 6 ∧ c 4 * c 6 + c 4 + c 6 < c 10 * c 4 * c 6) ∨
    (0 < c 11 ∧ 0 < c 12 ∧ c 11 * c 12 + c 11 + c 12 < c 8 * c 11 * c 12) ∨
    (0 < c 7 ∧ 0 < c 9 ∧ c 7 * c 9 + c 7 + c 9 < c 5 * c 7 * c 9) := by
  have h := fourMatchingCubic_zero_of_evaluation_eq_spectral a b η (zeroHeightLift c)
    (fun p => (zeroHeightLift_eval c p).trans (hvalues p).symm)
  rw [zeroHeightLift_cubic] at h
  have hr := canonicalCubicRemainder_nonneg c hc
  by_cases first : 0 < compensation (c 10) (c 4) (c 6)
  · exact Or.inl (positive_compensation (hc _) (hc _) first)
  by_cases second : 0 < compensation (c 8) (c 11) (c 12)
  · exact Or.inr (Or.inl (positive_compensation (hc _) (hc _) second))
  have third : 0 < compensation (c 5) (c 7) (c 9) := by
    linarith only [h, hr, le_of_not_gt first, le_of_not_gt second]
  exact Or.inr (Or.inr (positive_compensation (hc _) (hc _) third))

private def seedZeros : Finset (Fin 24) := {1, 6, 7, 8, 9, 12, 14, 15, 17, 18, 20, 22, 23}

private def zeroLabel (j : Fin 13) : Fin 24 :=
  ![1, 17, 6, 22, 12, 18, 20, 8, 14, 15, 9, 23, 7] j

private theorem seed_zero_iff (p : Fin 24) :
    mixedCostRayInt 0 p = 0 ↔ p ∈ seedZeros :=
  (by decide +kernel : ∀ p : Fin 24, mixedCostRayInt 0 p = 0 ↔ p ∈ seedZeros) p

private theorem seed_nonneg (p : Fin 24) : 0 ≤ mixedCostRay 0 p := by
  have hi : ∀ p : Fin 24, 0 ≤ mixedCostRayInt 0 p := by decide +kernel
  change (0 : ℝ) ≤ (mixedCostRayInt 0 p : ℝ)
  exact_mod_cast hi p

private theorem ray_nonneg (r : Fin 34) (p : Fin 24) : 0 ≤ ordinaryCostRay r p := by
  unfold ordinaryCostRay
  rw [ordinaryCostRayInt_indicator]
  split <;> norm_num

private theorem seed_ray_at_zeroLabel (j k : Fin 13) :
    ordinaryCostRayInt (fourCanonicalZeroHeightRay j) (zeroLabel k) =
      if j = k then 1 else 0 :=
  (by decide +kernel : ∀ j k : Fin 13,
    ordinaryCostRayInt (fourCanonicalZeroHeightRay j) (zeroLabel k) =
      if j = k then 1 else 0) j k

private theorem canonicalProfile_zeroLabel (c : Fin 13 → ℝ) (k : Fin 13) :
    fourCanonicalZeroHeightProfile c (zeroLabel k) = c k := by
  have hz : ∀ k : Fin 13, mixedCostRayInt 0 (zeroLabel k) = 0 := by decide +kernel
  classical
  simp only [fourCanonicalZeroHeightProfile, mixedCostRay, hz, Int.cast_zero, zero_add,
    ordinaryCostRay, seed_ray_at_zeroLabel, apply_ite, Int.cast_one, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def contactRectangle (r : Fin 6) : Fin 4 → Fin 24 :=
  ![![0, 1, 6, 7], ![1, 3, 20, 22], ![6, 11, 12, 17], ![8, 9, 14, 15],
    ![12, 14, 18, 20], ![16, 17, 22, 23]] r

private abbrev RectangleClosed (s : Finset (Fin 24)) : Prop :=
  ∀ r : Fin 6,
    let p := contactRectangle r
    (p 0 ∈ s → p 1 ∈ s → p 2 ∈ s → p 3 ∈ s) ∧
    (p 0 ∈ s → p 1 ∈ s → p 3 ∈ s → p 2 ∈ s) ∧
    (p 0 ∈ s → p 2 ∈ s → p 3 ∈ s → p 1 ∈ s) ∧
    (p 1 ∈ s → p 2 ∈ s → p 3 ∈ s → p 0 ∈ s)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem eight_closed_contacts :
    ∀ s ∈ seedZeros.powerset, 8 ≤ s.card → RectangleClosed s →
      (9 ∈ s ∨ 12 ∈ s ∨ 20 ∈ s) ∧
      (14 ∈ s ∨ 23 ∈ s ∨ 7 ∈ s) ∧
      (18 ∈ s ∨ 8 ∈ s ∨ 15 ∈ s) := by
  decide +kernel

private def inversePermutationTable (p : Fin 24) : Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 3, 1, 2],
    ![0, 2, 3, 1], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 0, 3, 2],
    ![2, 0, 1, 3], ![3, 0, 1, 2], ![2, 0, 3, 1], ![3, 0, 2, 1],
    ![1, 2, 0, 3], ![1, 3, 0, 2], ![2, 1, 0, 3], ![3, 1, 0, 2],
    ![2, 3, 0, 1], ![3, 2, 0, 1], ![1, 2, 3, 0], ![1, 3, 2, 0],
    ![2, 1, 3, 0], ![3, 1, 2, 0], ![2, 3, 1, 0], ![3, 2, 1, 0]] p

private theorem inversePermutationTable_apply (p : Fin 24) (i : Fin 4) :
    (fourPerm p).symm i = inversePermutationTable p i :=
  (by decide +kernel : ∀ p : Fin 24, ∀ i : Fin 4,
    (fourPerm p).symm i = inversePermutationTable p i) p i

private theorem contactRectangle_product (a b : Fin 4 → ℂ) (η : ℂ) (r : Fin 6) :
    let z (p : Fin 24) := η * matchingProduct a b (fourPerm p).symm
    let p := contactRectangle r
    z (p 0) * z (p 3) = z (p 1) * z (p 2) := by
  fin_cases r <;> simp only [contactRectangle, matchingProduct, Fin.prod_univ_four,
    inversePermutationTable_apply, inversePermutationTable, Matrix.cons_val] <;> ring

private theorem rectangle_fourth_real_zero {x y z w : ℂ} (h : x * w = y * z) (hx : x ≠ 0)
    (h₀ : x.re = 0) (h₁ : y.re = 0) (h₂ : z.re = 0) : w.re = 0 := by
  have hi : x.im ≠ 0 := by
    intro he
    exact hx (Complex.ext (h₀.trans Complex.zero_re.symm) (he.trans Complex.zero_im.symm))
  have him := congrArg Complex.im h
  simp only [Complex.mul_im, h₀, h₁, h₂, zero_mul, zero_add, mul_zero] at him
  exact (mul_eq_zero.mp him).resolve_left hi

private theorem zeroHeight_rectangleClosed (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0)
    (hn : ∀ i j, a i + b j ≠ 0) :
    RectangleClosed (Finset.univ.filter fun p : Fin 24 =>
      (η * matchingProduct a b (fourPerm p).symm).re = 0) := by
  let z (p : Fin 24) := η * matchingProduct a b (fourPerm p).symm
  have hz (p : Fin 24) : z p ≠ 0 :=
    mul_ne_zero hη (Finset.prod_ne_zero_iff.mpr fun j _ => hn _ j)
  intro r
  let p := contactRectangle r
  have hm : z (p 0) * z (p 3) = z (p 1) * z (p 2) := contactRectangle_product a b η r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change ((z (p 0)).re = 0 → (z (p 1)).re = 0 → (z (p 2)).re = 0 → (z (p 3)).re = 0) ∧
    ((z (p 0)).re = 0 → (z (p 1)).re = 0 → (z (p 3)).re = 0 → (z (p 2)).re = 0) ∧
    ((z (p 0)).re = 0 → (z (p 2)).re = 0 → (z (p 3)).re = 0 → (z (p 1)).re = 0) ∧
    ((z (p 1)).re = 0 → (z (p 2)).re = 0 → (z (p 3)).re = 0 → (z (p 0)).re = 0)
  refine ⟨fun h₀ h₁ h₂ => rectangle_fourth_real_zero hm (hz _) h₀ h₁ h₂,
    fun h₀ h₁ h₃ => rectangle_fourth_real_zero hm.symm (hz _) h₁ h₀ h₃,
    fun h₀ h₂ h₃ => rectangle_fourth_real_zero ?_ (hz _) h₂ h₀ h₃,
    fun h₁ h₂ h₃ => rectangle_fourth_real_zero ?_ (hz _) h₃ h₁ h₂⟩
  · rw [mul_comm (z (p 2)), hm]
  · rw [mul_comm (z (p 3)), hm]

/-- A canonical mixed profile realized by nonzero matching products at zero
support height has fewer than eight contacts. -/
theorem fourCanonicalZeroHeight_contacts_lt_eight
    (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0) (hn : ∀ i j, a i + b j ≠ 0)
    (c : Fin 13 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hvalues : ∀ p : Fin 24, (η * matchingProduct a b (fourPerm p).symm).re =
      fourCanonicalZeroHeightProfile c p) :
    (Finset.univ.filter fun p : Fin 24 =>
      (η * matchingProduct a b (fourPerm p).symm).re = 0).card < 8 := by
  let s := Finset.univ.filter fun p : Fin 24 =>
    (η * matchingProduct a b (fourPerm p).symm).re = 0
  have hs (p : Fin 24) : p ∈ s ↔ fourCanonicalZeroHeightProfile c p = 0 := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, hvalues]
  have hseed : s ⊆ seedZeros := by
    intro p hp
    apply (seed_zero_iff p).mp
    have hsum : 0 ≤ ∑ j, c j * ordinaryCostRay (fourCanonicalZeroHeightRay j) p :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (ray_nonneg _ p)
    have hzero := (hs p).mp hp
    unfold fourCanonicalZeroHeightProfile at hzero
    have hz : mixedCostRay 0 p = 0 := by linarith only [hzero, hsum, seed_nonneg p]
    change (mixedCostRayInt 0 p : ℝ) = 0 at hz
    exact_mod_cast hz
  have hz (j : Fin 13) (hj : zeroLabel j ∈ s) : c j = 0 :=
    (canonicalProfile_zeroLabel c j).symm.trans ((hs _).mp hj)
  change s.card < 8
  by_contra! hcard
  obtain ⟨h₁, h₂, h₃⟩ :=
    eight_closed_contacts s (Finset.mem_powerset.mpr hseed) hcard
      (zeroHeight_rectangleClosed a b η hη hn)
  rcases fourCanonicalZeroHeight_compensation a b η c hc hvalues with h | h | h
  · rcases h₁ with hp | hp | hp
    · exact compensation_center_ne_zero h.1.le h.2.1.le h.2.2 (hz 10 hp)
    · exact h.1.ne' (hz 4 hp)
    · exact h.2.1.ne' (hz 6 hp)
  · rcases h₂ with hp | hp | hp
    · exact compensation_center_ne_zero h.1.le h.2.1.le h.2.2 (hz 8 hp)
    · exact h.1.ne' (hz 11 hp)
    · exact h.2.1.ne' (hz 12 hp)
  · rcases h₃ with hp | hp | hp
    · exact compensation_center_ne_zero h.1.le h.2.1.le h.2.2 (hz 5 hp)
    · exact h.1.ne' (hz 7 hp)
    · exact h.2.1.ne' (hz 9 hp)

private theorem sum_zeroHeightRays {c : Fin 34 → ℝ}
    (hc : ∀ j ∉ fourCanonicalCapOrdinaryRays, c j = 0) (p : Fin 24) :
    (∑ j : Fin 13, c (fourCanonicalZeroHeightRay j) *
      ordinaryCostRay (fourCanonicalZeroHeightRay j) p) =
      ∑ j : Fin 34, c j * ordinaryCostRay j p := by
  have hi : Function.Injective fourCanonicalZeroHeightRay := by
    change ∀ i j : Fin 13, fourCanonicalZeroHeightRay i = fourCanonicalZeroHeightRay j → i = j
    decide +kernel
  have hcap : Finset.univ.image fourCanonicalZeroHeightRay = fourCanonicalCapOrdinaryRays := by
    decide +kernel
  calc
    _ = ∑ j ∈ Finset.univ.image fourCanonicalZeroHeightRay, c j * ordinaryCostRay j p :=
      (Finset.sum_image (fun _ _ _ _ h => hi h)).symm
    _ = _ := by
      rw [hcap]
      exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by rw [hc j hj, zero_mul])

/-- A regular canonical mixed terminal witness at zero support height has
exactly seven contacts. -/
theorem fourCanonicalZeroHeight_terminal_contacts_eq_seven
    {U : Matrix (Fin 4) (Fin 4) ℂ} (w : StrictMatchingSupport U)
    (hreg : FourRegularSpectra w) (hterminal : 7 ≤ w.contacts.card)
    (hheight : (w.η * matchingProduct w.a w.b w.pivot).re = 0)
    (c : Fin 34 → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hcs : ∀ j ∉ fourCanonicalCapOrdinaryRays, c j = 0)
    (hgap : fourTerminalGap w = (∑ j, c j • ordinaryCostRay j) + mixedCostRay 0) :
    w.contacts.card = 7 := by
  let c' : Fin 13 → ℝ := fun j => c (fourCanonicalZeroHeightRay j)
  have hη : w.η ≠ 0 := by
    intro he
    have hs := w.strict
    simp [he] at hs
  have hscore (p : Fin 24) :
      ((-w.η) * matchingProduct w.a w.b (fourPerm p).symm).re = fourTerminalGap w p := by
    rw [fourTerminalGap, matchingGap, hheight, neg_mul, Complex.neg_re, zero_sub]
  have heval (p : Fin 24) :
      ((-w.η) * matchingProduct w.a w.b (fourPerm p).symm).re =
        fourCanonicalZeroHeightProfile c' p := by
    rw [hscore, hgap, fourCanonicalZeroHeightProfile]
    simp only [c', Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      sum_zeroHeightRays hcs, add_comm]
  have he := fourCanonicalZeroHeight_contacts_lt_eight w.a w.b (-w.η)
    (neg_ne_zero.mpr hη) hreg.1 c' (fun j => hc _) heval
  simp only [hscore, fourTerminalGap_zero_count] at he
  omega

end

end MOC
