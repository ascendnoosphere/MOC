import MOC.SegreConvexity

/-! Cross partial trace on the two-state tensor permutation algebra. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Contract an output bit and an input bit, then reinsert the identity on
those two bits. The two terms are the trace over the two bit values. -/
def tensorCrossContraction (i j : ι) :
    Matrix (Finset ι) (Finset ι) ℂ →ₗ[ℂ] Matrix (Finset ι) (Finset ι) ℂ where
  toFun T := Matrix.of fun I J => if (i ∈ I ↔ j ∈ J) then
    T (I.erase i) (J.erase j) + T (insert i I) (insert j J) else 0
  map_add' T R := by
    ext I J
    by_cases h : i ∈ I ↔ j ∈ J <;> simp [h] <;> abel
  map_smul' z T := by
    ext I J
    by_cases h : i ∈ I ↔ j ∈ J <;> simp [h, mul_add]

private theorem erase_insert_same (i : ι) (I K : Finset ι) (h : i ∈ I ↔ i ∈ K) :
    (K.erase i = I.erase i ↔ K = I) ∧ (insert i K = insert i I ↔ K = I) := by
  constructor
  · refine ⟨fun he => ?_, fun he => by rw [he]⟩
    ext x
    by_cases hx : x = i
    · subst x
      exact h.symm
    · have hh : x ∈ K.erase i ↔ x ∈ I.erase i := by rw [he]
      simpa only [Finset.mem_erase, hx, not_false_eq_true, true_and] using hh
  · refine ⟨fun he => ?_, fun he => by rw [he]⟩
    ext x
    by_cases hx : x = i
    · subst x
      exact h.symm
    · have hh : x ∈ insert i K ↔ x ∈ insert i I := by rw [he]
      simpa only [Finset.mem_insert, hx, false_or] using hh

private theorem erase_different (i k : ι) (I K : Finset ι) (hik : i ≠ k) :
    K.erase k = I.erase i ↔
      k ∉ I ∧ i ∉ K ∧ ∀ x, x ≠ i → x ≠ k → (x ∈ K ↔ x ∈ I) := by
  constructor
  · intro h
    have h₁ : k ∈ K.erase k ↔ k ∈ I.erase i := by rw [h]
    have h₂ : i ∈ K.erase k ↔ i ∈ I.erase i := by rw [h]
    refine ⟨by simpa [Finset.mem_erase, Ne.symm hik] using h₁,
      by simpa [Finset.mem_erase, hik] using h₂, ?_⟩
    intro x hxi hxk
    have hx : x ∈ K.erase k ↔ x ∈ I.erase i := by rw [h]
    simpa [Finset.mem_erase, hxi, hxk] using hx
  · rintro ⟨h₁, h₂, h⟩
    ext x
    by_cases hxi : x = i
    · subst x
      simp [Finset.mem_erase, hik, h₂]
    · by_cases hxk : x = k
      · subst x
        simp [Finset.mem_erase, hxi, h₁]
      · simpa [Finset.mem_erase, hxi, hxk] using h x hxi hxk

private theorem insert_different (i k : ι) (I K : Finset ι) (hik : i ≠ k) :
    insert k K = insert i I ↔
      k ∈ I ∧ i ∈ K ∧ ∀ x, x ≠ i → x ≠ k → (x ∈ K ↔ x ∈ I) := by
  constructor
  · intro h
    have h₁ : k ∈ insert k K ↔ k ∈ insert i I := by rw [h]
    have h₂ : i ∈ insert k K ↔ i ∈ insert i I := by rw [h]
    refine ⟨by simpa [Finset.mem_insert, Ne.symm hik] using h₁,
      by simpa [Finset.mem_insert, hik] using h₂, ?_⟩
    intro x hxi hxk
    have hx : x ∈ insert k K ↔ x ∈ insert i I := by rw [h]
    simpa [Finset.mem_insert, hxi, hxk] using hx
  · rintro ⟨h₁, h₂, h⟩
    ext x
    by_cases hxi : x = i
    · subst x
      simp [Finset.mem_insert, hik, h₂]
    · by_cases hxk : x = k
      · subst x
        simp [Finset.mem_insert, hxi, h₁]
      · simpa [Finset.mem_insert, hxi, hxk] using h x hxi hxk

private theorem map_swap_eq (i k : ι) (I K : Finset ι) (hik : i ≠ k) :
    K.map (Equiv.swap i k).toEmbedding = I ↔
      (i ∈ I ↔ k ∈ K) ∧ (k ∈ I ↔ i ∈ K) ∧
      ∀ x, x ≠ i → x ≠ k → (x ∈ K ↔ x ∈ I) := by
  constructor
  · intro h
    have ha : i ∈ K.map (Equiv.swap i k).toEmbedding ↔ i ∈ I := by rw [h]
    have hb : k ∈ K.map (Equiv.swap i k).toEmbedding ↔ k ∈ I := by rw [h]
    refine ⟨by simpa [Finset.mem_map_equiv, Equiv.symm_swap] using ha.symm,
      by simpa [Finset.mem_map_equiv, Equiv.symm_swap] using hb.symm, ?_⟩
    intro x hxi hxk
    have hx : x ∈ K.map (Equiv.swap i k).toEmbedding ↔ x ∈ I := by rw [h]
    simpa [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hxi hxk] using hx
  · rintro ⟨ha, hb, h⟩
    ext x
    simp only [Finset.mem_map_equiv, Equiv.symm_swap]
    by_cases hxi : x = i
    · subst x
      simpa using ha.symm
    · by_cases hxk : x = k
      · subst x
        simpa using hb.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxk]
        exact h x hxi hxk

private theorem contraction_entry (i k : ι) (I K : Finset ι) :
    (if (i ∈ I ↔ k ∈ K) then
      (if K.erase k = I.erase i then (1 : ℂ) else 0) +
        (if insert k K = insert i I then 1 else 0) else 0) =
    if i = k then 2 * (if K = I then 1 else 0)
      else if K.map (Equiv.swap i k).toEmbedding = I then 1 else 0 := by
  by_cases hik : i = k
  · subst k
    rw [if_pos rfl]
    by_cases h : i ∈ I ↔ i ∈ K
    · obtain ⟨he, hi⟩ := erase_insert_same i I K h
      rw [if_pos h]
      by_cases hk : K = I <;> simp [he, hi, hk] <;> norm_num
    · have hk : K ≠ I := fun he => h (by rw [he])
      simp [h, hk]
  · rw [if_neg hik, erase_different i k I K hik, insert_different i k I K hik,
      map_swap_eq i k I K hik]
    by_cases h : i ∈ I ↔ k ∈ K
    · by_cases hi : i ∈ K <;> by_cases hk : k ∈ I <;>
        by_cases hr : ∀ x, x ≠ i → x ≠ k → (x ∈ K ↔ x ∈ I) <;>
        simp [h, hi, hk, hr]
    · simp [h]

private theorem subsetPermutationOperator_mul (σ τ : Equiv.Perm ι) :
    (subsetPermutationOperator (R := ℂ) σ) * subsetPermutationOperator τ =
      subsetPermutationOperator (σ * τ) := by
  ext I J
  have hm : (J.map τ.toEmbedding).map σ.toEmbedding = J.map (σ * τ).toEmbedding := by
    rw [Finset.map_map]
    rfl
  simp only [Matrix.mul_apply, subsetPermutationOperator, Matrix.of_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hm]

/-- At an existing connection the two bit values contribute the factor two.
At a different connection, contraction exchanges the two output positions. -/
theorem tensorCrossContraction_permutation (σ : Equiv.Perm ι) (i j : ι) :
    tensorCrossContraction i j (subsetPermutationOperator σ) =
      if i = σ j then (2 : ℂ) • subsetPermutationOperator σ
      else subsetPermutationOperator (Equiv.swap i (σ j) * σ) := by
  ext I J
  let K := J.map σ.toEmbedding
  have hk : σ j ∈ K ↔ j ∈ J := by
    exact Finset.mem_map' σ.toEmbedding
  have hm : K.map (Equiv.swap i (σ j)).toEmbedding =
      J.map (Equiv.swap i (σ j) * σ).toEmbedding := by
    rw [show K = J.map σ.toEmbedding from rfl, Finset.map_map]
    rfl
  have h := contraction_entry i (σ j) I K
  rw [hk, hm] at h
  simpa only [tensorCrossContraction, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply,
    subsetPermutationOperator, Finset.map_erase, Finset.map_insert, Equiv.toEmbedding_apply,
    Matrix.smul_apply, smul_eq_mul, apply_ite, K] using h

/-- The sum over ordered distinct pairs is twice the transposition sum. -/
def tensorOrderedTranspositions : Matrix (Finset ι) (Finset ι) ℂ :=
  ∑ i : ι, ∑ j : ι, if i = j then 0 else subsetPermutationOperator (Equiv.swap i j)

def tensorContractionSum :
    Matrix (Finset ι) (Finset ι) ℂ →ₗ[ℂ] Matrix (Finset ι) (Finset ι) ℂ :=
  ∑ i : ι, ∑ j : ι, tensorCrossContraction i j

private theorem tensorContractionSum_permutation (σ : Equiv.Perm ι) :
    let P := subsetPermutationOperator (R := ℂ) σ
    tensorContractionSum P = (2 * (Fintype.card ι : ℂ)) • P + tensorOrderedTranspositions * P := by
  classical
  intro P
  let q (i j : ι) := if i = j then (2 : ℂ) • P
    else subsetPermutationOperator (Equiv.swap i j * σ)
  have hex : ∀ i j, tensorCrossContraction i j P = q i (σ j) :=
    tensorCrossContraction_permutation σ
  have hsum : tensorContractionSum P = ∑ i : ι, ∑ j : ι, q i j := by
    simp only [tensorContractionSum, LinearMap.sum_apply, hex]
    exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (q i)
  have hq (i j : ι) : q i j = (if i = j then (2 : ℂ) • P else 0) +
      (if i = j then 0 else subsetPermutationOperator (Equiv.swap i j)) * P := by
    by_cases h : i = j
    · simp [q, h]
    · simp only [q, h, if_false, zero_add, P, subsetPermutationOperator_mul]
  have hid : (∑ i : ι, ∑ j : ι, if i = j then (2 : ℂ) • P else 0) =
      (2 * (Fintype.card ι : ℂ)) • P := by
    ext I J
    simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
  simp_rw [hsum, hq, Finset.sum_add_distrib, hid]
  simp only [tensorOrderedTranspositions, Finset.sum_mul]

/-- Summed contraction acts by a scalar identity term plus the random
transposition sum on every linear combination of permutation operators. -/
theorem tensorContractionSum_eq (w : Equiv.Perm ι → ℂ) :
    let T := ∑ σ, w σ • subsetPermutationOperator σ
    tensorContractionSum T =
      (2 * (Fintype.card ι : ℂ)) • T + tensorOrderedTranspositions * T := by
  dsimp only
  simp_rw [map_sum, map_smul, tensorContractionSum_permutation,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finset.mul_sum, Matrix.mul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_smul, smul_smul, mul_comm]

/-- One normalization of the contraction sum. For positive tensor order,
this gives the lazy random-transposition operator. -/
def tensorTranspositionRenormalization (T : Matrix (Finset ι) (Finset ι) ℂ) :
    Matrix (Finset ι) (Finset ι) ℂ :=
  (((Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) + 1))⁻¹ : ℂ) • tensorContractionSum T

theorem tensorTranspositionRenormalization_eq (w : Equiv.Perm ι → ℂ) :
    let T := ∑ σ, w σ • subsetPermutationOperator σ
    tensorTranspositionRenormalization T =
      (((Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) + 1))⁻¹ : ℂ) •
        ((2 * (Fintype.card ι : ℂ)) • T + tensorOrderedTranspositions * T) := by
  dsimp only [tensorTranspositionRenormalization]
  rw [tensorContractionSum_eq]

/-- The scalar from the two-row content formula, in the normalization of
the summed contraction. -/
def tensorTwoRowRenormalizationScalar (n k : ℝ) : ℝ :=
  1 - 2 * k * (n - k + 1) / (n * (n + 1))

theorem tensorTwoRowRenormalizationScalar_pos {n k : ℝ} (hn : 0 < n) (hk : 2 * k ≤ n) :
    0 < tensorTwoRowRenormalizationScalar n k := by
  unfold tensorTwoRowRenormalizationScalar
  apply sub_pos.mpr
  apply (div_lt_one (mul_pos hn (by positivity))).2
  nlinarith only [mul_pos hn hn, hk, sq_nonneg (n - 2 * k)]

theorem tensorTwoRowRenormalizationScalar_four_five :
    (tensorTwoRowRenormalizationScalar 4 0, tensorTwoRowRenormalizationScalar 4 1,
      tensorTwoRowRenormalizationScalar 4 2) = (1, 3 / 5, 2 / 5) ∧
    (tensorTwoRowRenormalizationScalar 5 0, tensorTwoRowRenormalizationScalar 5 1,
      tensorTwoRowRenormalizationScalar 5 2) = (1, 2 / 3, 7 / 15) := by
  norm_num [tensorTwoRowRenormalizationScalar]

end

end MOC
