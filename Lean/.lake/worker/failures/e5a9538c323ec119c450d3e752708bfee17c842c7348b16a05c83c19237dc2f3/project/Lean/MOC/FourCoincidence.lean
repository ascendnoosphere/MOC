import MOC.TwoValues
import MOC.Small

/-! Zheng's opposite-eigenvalue case in order four. The involution
exchanges the two assignments that are disjoint from the zero label.
After this exchange, the relevant signed masses are singleton marginals. -/

open BigOperators Matrix Finset

namespace MOC

noncomputable section

private abbrev Perm4 := Equiv.Perm (Fin 4)

private def anchorColumns (σ : Perm4) : Perm4 :=
  Equiv.swap 1 (σ.symm 0)

private def anchoredTwist (σ : Perm4) : Perm4 :=
  if σ 0 = 0 then σ else
    σ * anchorColumns σ * Equiv.swap 2 3 * (anchorColumns σ).symm

private theorem anchoredTwist_involutive : ∀ σ : Perm4, anchoredTwist (anchoredTwist σ) = σ := by
  decide

private def twistEquiv : Perm4 ≃ Perm4 :=
  ⟨anchoredTwist, anchoredTwist, anchoredTwist_involutive, anchoredTwist_involutive⟩

private theorem anchoredTwist_apply_zero : ∀ σ : Perm4, anchoredTwist σ 0 = σ 0 := by
  decide

private theorem anchoredTwist_zero_image :
    ∀ (σ : Perm4) (j : Fin 4), anchoredTwist σ j = 0 ↔ σ j = 0 := by
  decide

private theorem anchoredTwist_fibre :
    ∀ (σ : Perm4) (i j : Fin 4), i ≠ 0 → j ≠ 0 →
      (σ 0 ≠ 0 ∧ σ j = i ↔
        ({0, j} : Finset (Fin 4)).map (anchoredTwist σ).toEmbedding = ({0, i} : Finset (Fin 4))ᶜ) := by
  decide

private def anchoredProduct (a : Fin 4 → ℂ) : ℂ :=
  ∏ i, if i = 0 then 1 else a i

private def anchoredExcept (a : Fin 4 → ℂ) (k : Fin 4) : ℂ :=
  ∏ i, if i = 0 ∨ i = k then 1 else a i

private def twistCoefficient (a b : Fin 4 → ℂ) (j i : Fin 4) : ℂ :=
  if j = 0 then anchoredProduct b * a i else
    if i = 0 then anchoredProduct a * b j else anchoredExcept a i * anchoredExcept b j

private theorem anchoredProduct_reindex (a : Fin 4 → ℂ) (e : Perm4) (k : Fin 4)
    (he : e k = 0) :
    anchoredProduct a = ∏ j, if j = k then 1 else a (e j) := by
  unfold anchoredProduct
  rw [← Equiv.prod_comp e (fun j => if j = 0 then (1 : ℂ) else a j)]
  simp [← he, e.injective.eq_iff]

private theorem anchoredExcept_reindex (a : Fin 4 → ℂ) (e : Perm4) (k l : Fin 4)
    (he : e k = 0) :
    anchoredExcept a (e l) = ∏ j, if j = k ∨ j = l then 1 else a (e j) := by
  unfold anchoredExcept
  rw [← Equiv.prod_comp e (fun j => if j = 0 ∨ j = e l then (1 : ℂ) else a j)]
  simp [← he, e.injective.eq_iff]

private theorem matching_twist_expansion (a b : Fin 4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (σ : Perm4) (hσ : σ 0 ≠ 0) :
    matchingProduct a b (anchoredTwist σ) = ∑ j, twistCoefficient a b j (σ j) := by
  let e := anchorColumns σ
  let f := σ * e
  have hr : σ.symm 0 ≠ 0 := by
    intro h
    apply hσ
    calc
      σ 0 = σ (σ.symm 0) := congrArg σ h.symm
      _ = 0 := σ.apply_symm_apply _
  have he₀ : e 0 = 0 := by
    simp [e, anchorColumns, Equiv.swap_apply_def, hr.symm]
  have he₁ : e 1 = σ.symm 0 := Equiv.swap_apply_left _ _
  have hf₁ : f 1 = 0 := by
    simp only [f, Equiv.Perm.mul_apply, he₁, Equiv.apply_symm_apply]
  have he₂ : e 2 ≠ 0 := fun h => (by decide : (2 : Fin 4) ≠ 0) (e.injective (h.trans he₀.symm))
  have he₃ : e 3 ≠ 0 := fun h => (by decide : (3 : Fin 4) ≠ 0) (e.injective (h.trans he₀.symm))
  have he₁' : e 1 ≠ 0 := he₁ ▸ hr
  have hf₂ : f 2 ≠ 0 := fun h => (by decide : (2 : Fin 4) ≠ 1) (f.injective (h.trans hf₁.symm))
  have hf₃ : f 3 ≠ 0 := fun h => (by decide : (3 : Fin 4) ≠ 1) (f.injective (h.trans hf₁.symm))
  have htwist (j : Fin 4) :
      anchoredTwist σ (e j) = f (Equiv.swap 2 3 j) := by
    simp only [anchoredTwist, hσ, if_false, Equiv.Perm.mul_apply, f]
    exact congrArg (fun i => σ (e (Equiv.swap 2 3 i))) (e.symm_apply_apply j)
  have hL : matchingProduct a b (anchoredTwist σ) =
      a (f 0) * b (e 1) * (a (f 3) + b (e 2)) * (a (f 2) + b (e 3)) := by
    unfold matchingProduct
    rw [← Equiv.prod_comp e (fun j => a (anchoredTwist σ j) + b j), Fin.prod_univ_four]
    simp only [htwist, show Equiv.swap (2 : Fin 4) 3 0 = 0 by decide,
      show Equiv.swap (2 : Fin 4) 3 1 = 1 by decide, Equiv.swap_apply_left,
      Equiv.swap_apply_right, hf₁, he₀, ha, hb, add_zero, zero_add]
    simp only [anchoredTwist_apply_zero, f, Equiv.Perm.mul_apply, he₀]
  rw [hL, ← Equiv.sum_comp e (fun j => twistCoefficient a b j (σ j)), Fin.sum_univ_four]
  change _ = twistCoefficient a b (e 0) (f 0) + twistCoefficient a b (e 1) (f 1) +
    twistCoefficient a b (e 2) (f 2) + twistCoefficient a b (e 3) (f 3)
  simp only [twistCoefficient, he₀, if_pos rfl, he₁', he₂, he₃, if_false, hf₁, hf₂, hf₃]
  rw [anchoredProduct_reindex a f 1 hf₁, anchoredProduct_reindex b e 0 he₀,
    anchoredExcept_reindex a f 1 2 hf₁, anchoredExcept_reindex a f 1 3 hf₁,
    anchoredExcept_reindex b e 0 2 he₀, anchoredExcept_reindex b e 0 3 he₀]
  simp only [Fin.prod_univ_four]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp only [h01, h02, h03, h12, h13, h23, h01.symm, h02.symm, h03.symm,
    h12.symm, h13.symm, h23.symm, eq_self, or_false, false_or, true_or, or_true,
    if_false, if_true, one_mul, mul_one]
  ring

private def anchorWeight (U : Matrix (Fin 4) (Fin 4) ℂ) (σ : Perm4) : ℝ :=
  if σ 0 = 0 then 0 else realSignedWeight U (anchoredTwist σ)

private def realMarginal4 (w : Perm4 → ℝ) (j i : Fin 4) : ℝ :=
  ∑ σ, if σ j = i then w σ else 0

private theorem anchorWeight_fibre_eval (U : Matrix (Fin 4) (Fin 4) ℂ)
    (p : Perm4 → Prop) [DecidablePred p] :
    (∑ σ, if p σ then anchorWeight U σ else 0) =
      ∑ σ, if σ 0 ≠ 0 ∧ p (anchoredTwist σ) then realSignedWeight U σ else 0 := by
  rw [← Equiv.sum_comp twistEquiv (fun σ => if p σ then anchorWeight U σ else 0)]
  apply Finset.sum_congr rfl
  intro σ _
  change (if p (anchoredTwist σ) then anchorWeight U (anchoredTwist σ) else 0) = _
  simp only [anchorWeight, anchoredTwist_apply_zero, anchoredTwist_involutive]
  by_cases h : σ 0 = 0 <;> by_cases hp : p (anchoredTwist σ) <;> simp [h, hp]

private theorem anchorWeight_marginal_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (j i : Fin 4) : 0 ≤ realMarginal4 (anchorWeight U) j i := by
  unfold realMarginal4
  rw [anchorWeight_fibre_eval]
  rcases eq_or_ne j 0 with (rfl | hj)
  · rcases eq_or_ne i 0 with (rfl | hi)
    · simp [anchoredTwist_apply_zero]
    have he (σ : Perm4) : (σ 0 ≠ 0 ∧ anchoredTwist σ 0 = i) ↔ σ 0 = i := by
      rw [anchoredTwist_apply_zero]
      exact ⟨And.right, fun h => ⟨by simpa [h] using hi, h⟩⟩
    simpa only [he, marginal_realSignedWeight U hU] using Complex.normSq_nonneg (U i 0)
  rcases eq_or_ne i 0 with (rfl | hi)
  · have he (σ : Perm4) : (σ 0 ≠ 0 ∧ anchoredTwist σ j = 0) ↔ σ j = 0 := by
      rw [anchoredTwist_zero_image]
      exact ⟨And.right, fun h => ⟨fun h' => hj (σ.injective (h.trans h'.symm)), h⟩⟩
    simpa only [he, marginal_realSignedWeight U hU] using Complex.normSq_nonneg (U 0 j)
  have he (σ : Perm4) : (σ 0 ≠ 0 ∧ anchoredTwist σ j = i) ↔
      ({0, j} : Finset (Fin 4)).map σ.toEmbedding = ({0, i} : Finset (Fin 4))ᶜ := by
    simpa only [anchoredTwist_apply_zero, anchoredTwist_involutive] using
      anchoredTwist_fibre (anchoredTwist σ) i j hi hj
  simp_rw [he, ← Finset.sum_filter]
  have hmass := congrArg Complex.re
    (sum_signedWeight_image_eq_subsetMinorSq U hU ({0, i}ᶜ) {0, j})
  rw [Complex.re_sum, Complex.ofReal_re] at hmass
  exact hmass ▸ subsetMinorSq_nonneg U _ _

private theorem anchorWeight_total (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∑ σ, anchorWeight U σ = 1 - Complex.normSq (U 0 0) := by
  have htransport : (∑ σ, anchorWeight U σ) =
      ∑ σ : Perm4, if σ 0 ≠ 0 then realSignedWeight U σ else 0 := by
    simpa only [if_true, and_true] using anchorWeight_fibre_eval U (fun _ => True)
  have hpart : (∑ σ : Perm4, if σ 0 ≠ 0 then realSignedWeight U σ else 0) +
      (∑ σ : Perm4, if σ 0 = 0 then realSignedWeight U σ else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← sum_realSignedWeight U hU]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases h : σ 0 = 0 <;> simp [h]
  rw [htransport]
  linarith only [hpart, marginal_realSignedWeight U hU 0 0]

private theorem realMarginal4_rows (w : Perm4 → ℝ) (j : Fin 4) :
    ∑ i, realMarginal4 w j i = ∑ σ, w σ := by
  unfold realMarginal4
  rw [Finset.sum_comm]
  simp

private theorem realMarginal4_cols (w : Perm4 → ℝ) (i : Fin 4) :
    ∑ j, realMarginal4 w j i = ∑ σ, w σ := by
  unfold realMarginal4
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have he (j : Fin 4) : σ j = i ↔ j = σ.symm i := by
    exact ⟨fun h => by rw [← h, Equiv.symm_apply_apply],
      fun h => by rw [h, Equiv.apply_symm_apply]⟩
  simp_rw [he]
  simp

private theorem replace_by_nonnegative_weights (w : Perm4 → ℝ)
    (hm : ∀ j i, 0 ≤ realMarginal4 w j i) :
    ∃ p : Perm4 → ℝ, (∀ σ, 0 ≤ p σ) ∧ (∑ σ, p σ = ∑ σ, w σ) ∧
      ∀ j i, realMarginal4 p j i = realMarginal4 w j i := by
  let mass := ∑ σ, w σ
  have hmass : 0 ≤ mass := by
    change 0 ≤ ∑ σ, w σ
    rw [← realMarginal4_rows w 0]
    exact Finset.sum_nonneg (fun i _ => hm 0 i)
  rcases eq_or_lt_of_le hmass with hzero | hpos
  · have hzero' : ∑ σ, w σ = 0 := hzero.symm
    refine ⟨fun _ => 0, fun _ => le_rfl, by simp [hzero'], ?_⟩
    intro j i
    have hz : ∑ k, realMarginal4 w j k = 0 := by rw [realMarginal4_rows, hzero']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hm j k)).mp hz i
      (Finset.mem_univ i)
    rw [hi]
    simp [realMarginal4]
  let W : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun j i => realMarginal4 w j i / mass
  have hW : W ∈ doublyStochastic ℝ (Fin 4) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun j i => div_nonneg (hm j i) hpos.le, ?_, ?_⟩
    · intro j
      change (∑ i, realMarginal4 w j i / mass) = 1
      rw [← Finset.sum_div, realMarginal4_rows, div_self hpos.ne']
    · intro i
      change (∑ j, realMarginal4 w j i / mass) = 1
      rw [← Finset.sum_div, realMarginal4_cols, div_self hpos.ne']
  obtain ⟨p, hp, hs, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hW
  have hentry (j i : Fin 4) : realMarginal4 p j i = realMarginal4 w j i / mass := by
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M j i) he
    simpa [W, realMarginal4, Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, mul_ite, eq_comm] using h
  refine ⟨fun σ => mass * p σ, fun σ => mul_nonneg hmass (hp σ), ?_, ?_⟩
  · rw [← Finset.mul_sum, hs, mul_one]
  intro j i
  have hscale : realMarginal4 (fun σ => mass * p σ) j i = mass * realMarginal4 p j i := by
    simp [realMarginal4, Finset.mul_sum, mul_ite]
  rw [hscale, hentry, mul_div_cancel₀ _ hpos.ne']

private theorem anchoredProduct_zero_of_fixes (a b : Fin 4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (σ : Perm4) (hσ : σ 0 = 0) : matchingProduct a b σ = 0 := by
  unfold matchingProduct
  apply Finset.prod_eq_zero (Finset.mem_univ 0)
  simp [hσ, ha, hb]

private theorem weighted_twist_matching (a b : Fin 4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (w : Perm4 → ℝ) (hw : ∀ σ, σ 0 = 0 → w σ = 0) :
    (∑ σ, (w σ : ℂ) * matchingProduct a b (anchoredTwist σ)) =
      ∑ j, ∑ i, (realMarginal4 w j i : ℂ) * twistCoefficient a b j i := by
  calc
    _ = ∑ σ, (w σ : ℂ) * ∑ j, twistCoefficient a b j (σ j) := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hσ : σ 0 = 0
      · simp [hw σ hσ]
      · rw [matching_twist_expansion a b ha hb σ hσ]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_weighted_evaluation]
      simp [marginal, realMarginal4, Complex.ofReal_sum, apply_ite]

/-- In order four a zero on each diagonal summand at label zero admits
positive common weights, independent of the remaining eigenvalues. -/
theorem exists_four_zero_pair_weights (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      (∑ σ, if σ 0 = 0 then w σ else 0) = Complex.normSq (U 0 0) ∧
      ∀ (a b : Fin 4 → ℂ), a 0 = 0 → b 0 = 0 →
        ∑ σ, (w σ : ℂ) * matchingProduct a b σ = determinantValue a b U := by
  let w := anchorWeight U
  let mass := ∑ σ, w σ
  obtain ⟨p, hp, hpsum, hm⟩ := replace_by_nonnegative_weights w (anchorWeight_marginal_nonneg U hU)
  have hfix (σ : Perm4) (hσ : σ 0 = 0) : p σ = 0 := by
    have hw00 : realMarginal4 w 0 0 = 0 := by
      unfold realMarginal4
      apply Finset.sum_eq_zero
      intro τ _
      by_cases ht : τ 0 = 0 <;> simp [w, anchorWeight, ht]
    have hsum : (∑ τ : Perm4, if τ 0 = 0 then p τ else 0) = 0 :=
      (hm 0 0).trans hw00
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => by
      by_cases ht : τ 0 = 0 <;> simp [ht, hp])).mp hsum σ (Finset.mem_univ σ)
    simpa [hσ] using h
  have hm_le : mass ≤ 1 := by
    change (∑ σ, anchorWeight U σ) ≤ 1
    rw [anchorWeight_total U hU]
    exact sub_le_self _ (Complex.normSq_nonneg _)
  let finalWeight : Perm4 → ℝ := fun σ => p (anchoredTwist σ) + if σ = 1 then 1 - mass else 0
  refine ⟨finalWeight, fun σ => add_nonneg (hp _) (by split_ifs <;> linarith), ?_, ?_, ?_⟩
  · unfold finalWeight
    rw [Finset.sum_add_distrib]
    change (∑ σ, p (twistEquiv σ)) + _ = 1
    rw [Equiv.sum_comp twistEquiv, hpsum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change mass + (1 - mass) = 1
    ring
  · have hcalc : (∑ σ, if σ 0 = 0 then finalWeight σ else 0) =
        ∑ σ : Perm4, if σ = 1 then 1 - mass else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hσ : σ 0 = 0
      · simp [hσ, finalWeight, hfix _ ((anchoredTwist_apply_zero σ).trans hσ)]
      · have hne : σ ≠ 1 := by rintro rfl; exact hσ rfl
        simp [hσ, hne]
    rw [hcalc]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change 1 - (∑ σ, anchorWeight U σ) = _
    rw [anchorWeight_total U hU]
    ring
  intro a b ha hb
  have hstart : determinantValue a b U =
      ∑ σ, (w σ : ℂ) * matchingProduct a b (anchoredTwist σ) := by
    rw [← real_signed_determinant a b U hU]
    rw [← Equiv.sum_comp twistEquiv (fun σ => (realSignedWeight U σ : ℂ) * matchingProduct a b σ)]
    apply Finset.sum_congr rfl
    intro σ _
    change (realSignedWeight U (anchoredTwist σ) : ℂ) *
      matchingProduct a b (anchoredTwist σ) = _
    by_cases hσ : σ 0 = 0
    · rw [anchoredProduct_zero_of_fixes a b ha hb _ ((anchoredTwist_apply_zero σ).trans hσ)]
      simp
    · simp [w, anchorWeight, hσ]
  calc
    _ = ∑ σ, (p (anchoredTwist σ) : ℂ) * matchingProduct a b σ := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hσ : σ = 1
      · subst σ
        simp [anchoredProduct_zero_of_fixes a b ha hb 1 rfl]
      · simp [finalWeight, hσ]
    _ = ∑ σ, (p σ : ℂ) * matchingProduct a b (anchoredTwist σ) := by
      rw [← Equiv.sum_comp twistEquiv (fun σ => (p (anchoredTwist σ) : ℂ) * matchingProduct a b σ)]
      simp only [twistEquiv, Equiv.coe_fn_mk, anchoredTwist_involutive]
    _ = ∑ σ, (w σ : ℂ) * matchingProduct a b (anchoredTwist σ) := by
      rw [weighted_twist_matching a b ha hb p hfix, weighted_twist_matching a b ha hb w]
      · simp_rw [hm]
      · intro σ hσ
        simp [w, anchorWeight, hσ]
    _ = _ := hstart.symm

/-- Zheng's common weights depend only on the relative eigenbasis and
work simultaneously for all opposite eigenvalues at label zero. -/
theorem exists_four_opposite_pair_weights (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      (∑ σ, if σ 0 = 0 then w σ else 0) = Complex.normSq (U 0 0) ∧
      ∀ (a b : Fin 4 → ℂ), a 0 + b 0 = 0 →
        ∑ σ, (w σ : ℂ) * matchingProduct a b σ = determinantValue a b U := by
  obtain ⟨w, hw, hs, hfixed, hv⟩ := exists_four_zero_pair_weights U hU
  refine ⟨w, hw, hs, hfixed, fun a b hab => ?_⟩
  have h := hv (fun i => a i + b 0) (fun i => b i - b 0) hab (sub_self _)
  simpa only [matchingProduct_shift, determinantValue_shift a b hU] using h

theorem holds_four_zero_pair (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (ha : a 0 = 0) (hb : b 0 = 0) : Holds a b U := by
  obtain ⟨w, hw, hs, _, h⟩ := exists_four_zero_pair_weights U hU
  exact holds_of_weights w hw hs (h a b ha hb)

theorem holds_four_opposite_at_zero (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hab : a 0 + b 0 = 0) : Holds a b U := by
  apply (holds_shift_iff a b hU (b 0)).mp
  exact holds_four_zero_pair _ _ U hU hab (sub_self _)

/-- An opposite pair of eigenvalues at arbitrary row and column labels suffices
for the order-four determinant inclusion. -/
theorem holds_four_of_opposite_entries (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    {i j : Fin 4} (hij : a i + b j = 0) : Holds a b U := by
  let er : Perm4 := Equiv.swap 0 i
  let ec : Perm4 := Equiv.swap 0 j
  apply (holds_reindex_iff er ec a b U).mp
  apply holds_four_opposite_at_zero _ _ _ (unitary_reindex er ec hU)
  simpa [er, ec, Function.comp_apply] using hij

/-- If one permutation product vanishes, order-four MOC holds at these spectra. -/
theorem holds_four_of_zero_matchingProduct (a b : Fin 4 → ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    {σ : Equiv.Perm (Fin 4)} (hσ : matchingProduct a b σ = 0) : Holds a b U := by
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hσ
  exact holds_four_of_opposite_entries a b U hU hj


end

end MOC
