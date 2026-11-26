import MOC.CommonWeights
import MOC.SegreConvexity

/-! The common matching law for three values is a finite subset-interval
problem. The interval equations test a single law for all opposing spectra. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Assign `b₁` on `J`, `b₂` on `K \ J`, and `b₀` outside `K`. -/
def threeValueIntervalSpectrum (J K : Finset ι) (b₀ b₁ b₂ : ℂ) (j : ι) : ℂ :=
  if j ∈ J then b₁ else if j ∈ K then b₂ else b₀

/-- The mass in row `I` from the columns between `J` and `K`. -/
def threeValueIntervalProfile (T : Matrix (Finset ι) (Finset ι) ℝ)
    (J K I : Finset ι) : ℝ :=
  ∑ S ∈ univ.filter (fun S => J ⊆ S ∧ S ⊆ K), T I S

private theorem prod_subset_indicator (A B : Finset ι) (z : ℂ) :
    (∏ i ∈ A, if i ∈ B then z else 0) = if A ⊆ B then z ^ A.card else 0 := by
  classical
  by_cases h : A ⊆ B
  · rw [if_pos h, ← Finset.prod_const (s := A) z]
    exact Finset.prod_congr rfl fun i hi => if_pos (h hi)
  · obtain ⟨i, hi, hib⟩ := Finset.not_subset.mp h
    rw [if_neg h, Finset.prod_eq_zero hi (if_neg hib)]

private theorem subsetProductCoordinates_interval (J K S : Finset ι) :
    subsetProductCoordinates (fun j => if j ∈ J then 0 else 1)
      (fun j => if j ∈ K then 1 else 0) S =
        if J ⊆ S ∧ S ⊆ K then 1 else 0 := by
  classical
  have hlow : Sᶜ ⊆ Jᶜ ↔ J ⊆ S := by simp
  have hx : (fun j : ι => if j ∈ J then (0 : ℂ) else 1) =
      fun j => if j ∈ Jᶜ then 1 else 0 := by
    funext j
    by_cases hj : j ∈ J <;> simp [hj]
  unfold subsetProductCoordinates
  rw [hx, prod_subset_indicator, prod_subset_indicator]
  simp only [hlow, one_pow]
  by_cases hlo : J ⊆ S <;> by_cases hhi : S ⊆ K <;> simp [hlo, hhi]

private theorem productTensorEvaluation_interval (T : Matrix (Finset ι) (Finset ι) ℝ)
    (J K : Finset ι) (x y : ι → ℂ) :
    productTensorEvaluation x y (fun j => if j ∈ J then 0 else 1)
        (fun j => if j ∈ K then 1 else 0) T =
      ∑ I, (threeValueIntervalProfile T J K I : ℂ) * subsetProductCoordinates x y I := by
  classical
  change (∑ S, ∑ I, (T I S : ℂ) * (subsetProductCoordinates x y I *
    subsetProductCoordinates (fun j => if j ∈ J then 0 else 1)
      (fun j => if j ∈ K then 1 else 0) S)) = _
  simp only [subsetProductCoordinates_interval]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [threeValueIntervalProfile, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : J ⊆ S ∧ S ⊆ K <;> simp [h]

private theorem intervalProfile_permutation (J K I : Finset ι) (σ : Equiv.Perm ι) :
    threeValueIntervalProfile (subsetPermutationOperator σ) J K I =
      if J.map σ.toEmbedding ⊆ I ∧ I ⊆ K.map σ.toEmbedding then 1 else 0 := by
  classical
  let S₀ := I.map σ.symm.toEmbedding
  have hmap (S : Finset ι) : S.map σ.toEmbedding = I ↔ S = S₀ := by
    constructor
    · intro h
      ext i
      rw [show i ∈ S₀ ↔ σ i ∈ I by simp only [S₀, Finset.mem_map_equiv, Equiv.symm_symm],
        ← h, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    · intro h
      subst S
      ext i
      simp only [S₀, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hInterval : (J ⊆ S₀ ∧ S₀ ⊆ K) ↔
      (J.map σ.toEmbedding ⊆ I ∧ I ⊆ K.map σ.toEmbedding) :=
    and_congr Finset.subset_map_symm Finset.map_symm_subset
  unfold threeValueIntervalProfile
  rw [Finset.sum_filter]
  simp only [subsetPermutationOperator, Matrix.of_apply, hmap]
  rw [Finset.sum_eq_single S₀]
  · simp only [if_true, hInterval]
  · intro S _ hS
    simp only [if_neg hS, ite_self]
  · simp

private theorem intervalProfile_weighted (J K I : Finset ι) (w : Equiv.Perm ι → ℝ) :
    threeValueIntervalProfile (∑ σ, w σ • subsetPermutationOperator σ) J K I =
      ∑ σ, if J.map σ.toEmbedding ⊆ I ∧ I ⊆ K.map σ.toEmbedding then w σ else 0 := by
  classical
  unfold threeValueIntervalProfile
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.mul_sum]
  change w σ * threeValueIntervalProfile (subsetPermutationOperator σ) J K I = _
  rw [intervalProfile_permutation, mul_ite, mul_one, mul_zero]

private theorem productTensorEvaluation_three_values (J K : Finset ι) (hJK : J ⊆ K)
    (b₀ b₁ b₂ : ℂ) (a : ι → ℂ) (σ : Equiv.Perm ι) :
    let x (i : ι) := (b₁ - b₂) * (a i + b₀)
    let y (i : ι) := (b₂ - b₀) * (a i + b₁)
    let t (j : ι) := if j ∈ J then b₂ - b₀ else if j ∈ K then b₁ - b₀ else b₁ - b₂
    productTensorEvaluation x y (fun j => if j ∈ J then 0 else 1)
        (fun j => if j ∈ K then 1 else 0) (subsetPermutationOperator σ) =
      (∏ j, t j) * matchingProduct a (threeValueIntervalSpectrum J K b₀ b₁ b₂) σ := by
  classical
  dsimp only
  rw [productTensorEvaluation_permutation, matchingProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j ∈ J
  · simp [hj, hJK hj, threeValueIntervalSpectrum]
  · by_cases hk : j ∈ K
    · simp only [hj, hk, threeValueIntervalSpectrum, if_false, if_true, mul_one]
      ring
    · simp [hj, hk, threeValueIntervalSpectrum]

private theorem scaled_weightedMatchingValue (J K : Finset ι) (hJK : J ⊆ K)
    (b₀ b₁ b₂ : ℂ) (a : ι → ℂ) (w : Equiv.Perm ι → ℝ) :
    let x (i : ι) := (b₁ - b₂) * (a i + b₀)
    let y (i : ι) := (b₂ - b₀) * (a i + b₁)
    let t (j : ι) := if j ∈ J then b₂ - b₀ else if j ∈ K then b₁ - b₀ else b₁ - b₂
    productTensorEvaluation x y (fun j => if j ∈ J then 0 else 1)
        (fun j => if j ∈ K then 1 else 0) (∑ σ, w σ • subsetPermutationOperator σ) =
      (∏ j, t j) * weightedMatchingValue a (threeValueIntervalSpectrum J K b₀ b₁ b₂) w := by
  dsimp only
  rw [map_sum, weightedMatchingValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_smul, Complex.real_smul, productTensorEvaluation_three_values J K hJK b₀ b₁ b₂ a σ]
  ring

private theorem three_value_partition_scale_ne_zero (J K : Finset ι)
    (b₀ b₁ b₂ : ℂ) (h₀₁ : b₀ ≠ b₁) (h₀₂ : b₀ ≠ b₂) (h₁₂ : b₁ ≠ b₂) :
    (∏ j, if j ∈ J then b₂ - b₀ else if j ∈ K then b₁ - b₀ else b₁ - b₂) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hj : j ∈ J
  · simpa only [if_pos hj] using sub_ne_zero.mpr h₀₂.symm
  · by_cases hk : j ∈ K
    · simpa only [if_neg hj, if_pos hk] using sub_ne_zero.mpr h₀₁.symm
    · simpa only [if_neg hj, if_neg hk] using sub_ne_zero.mpr h₁₂

private theorem subsetProductCoordinates_corner (I S : Finset ι) (c d : ℂ) :
    subsetProductCoordinates (fun i => if i ∈ Iᶜ then c else 0)
      (fun i => if i ∈ I then d else 0) S =
        if S = I then c ^ Iᶜ.card * d ^ I.card else 0 := by
  classical
  have hlow : Sᶜ ⊆ Iᶜ ↔ I ⊆ S := by simp
  unfold subsetProductCoordinates
  rw [prod_subset_indicator, prod_subset_indicator]
  simp only [hlow]
  by_cases hSI : S = I
  · subst S
    simp
  · by_cases hs : I ⊆ S
    · have ht : ¬ S ⊆ I := fun ht => hSI (Finset.Subset.antisymm ht hs)
      simp only [if_pos hs, if_neg ht, if_neg hSI, mul_zero]
    · simp only [if_neg hs, if_neg hSI, zero_mul]

/-- For three distinct values, one fixed law agrees with all opposing spectra
exactly when it has the required subset-interval masses. -/
theorem three_value_common_weights_iff_interval {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (J K : Finset ι) (hJK : J ⊆ K) (w : Equiv.Perm ι → ℝ)
    (b₀ b₁ b₂ : ℂ) (h₀₁ : b₀ ≠ b₁) (h₀₂ : b₀ ≠ b₂) (h₁₂ : b₁ ≠ b₂) :
    (∀ a : ι → ℂ, weightedMatchingValue a (threeValueIntervalSpectrum J K b₀ b₁ b₂) w =
      determinantValue a (threeValueIntervalSpectrum J K b₀ b₁ b₂) U) ↔
    ∀ I : Finset ι,
      (∑ σ, if J.map σ.toEmbedding ⊆ I ∧ I ⊆ K.map σ.toEmbedding then w σ else 0) =
        ∑ S ∈ univ.filter (fun S => J ⊆ S ∧ S ⊆ K), subsetMinorSq U I S := by
  classical
  let T : Matrix (Finset ι) (Finset ι) ℝ := ∑ σ, w σ • subsetPermutationOperator σ
  let V := exteriorTransportOperator U
  let x (a : ι → ℂ) (i : ι) := (b₁ - b₂) * (a i + b₀)
  let y (a : ι → ℂ) (i : ι) := (b₂ - b₀) * (a i + b₁)
  let F (a : ι → ℂ) := productTensorEvaluation (x a) (y a) (fun j => if j ∈ J then 0 else 1)
    (fun j => if j ∈ K then 1 else 0)
  let t := ∏ j, if j ∈ J then b₂ - b₀ else if j ∈ K then b₁ - b₀ else b₁ - b₂
  let b := threeValueIntervalSpectrum J K b₀ b₁ b₂
  have hprod : t ≠ 0 := three_value_partition_scale_ne_zero J K b₀ b₁ b₂ h₀₁ h₀₂ h₁₂
  have hT (a : ι → ℂ) : F a T = t * weightedMatchingValue a b w :=
    scaled_weightedMatchingValue J K hJK b₀ b₁ b₂ a w
  have hV (a : ι → ℂ) : F a V = t * determinantValue a b U := by
    have h := scaled_weightedMatchingValue J K hJK b₀ b₁ b₂ a (realSignedWeight U)
    rw [← exteriorTransportOperator_eq_sum U hU, weightedMatchingValue,
      real_signed_determinant _ _ U hU] at h
    exact h
  have hEval (a : ι → ℂ) (W : Matrix (Finset ι) (Finset ι) ℝ) :
      F a W = ∑ I, (threeValueIntervalProfile W J K I : ℂ) *
        subsetProductCoordinates (x a) (y a) I :=
    productTensorEvaluation_interval W J K (x a) (y a)
  have hcase (I : Finset ι) : threeValueIntervalProfile V J K I =
      ∑ S ∈ univ.filter (fun S => J ⊆ S ∧ S ⊆ K), subsetMinorSq U I S := rfl
  constructor
  · intro h I
    let a (i : ι) := if i ∈ I then -b₀ else -b₁
    let c := (b₁ - b₂) * (b₀ - b₁)
    let d := (b₂ - b₀) * (b₁ - b₀)
    have hx : x a = fun i => if i ∈ Iᶜ then c else 0 := by
      funext i
      by_cases hi : i ∈ I
      · simp [x, a, hi]
      · simp only [x, a, c, Finset.mem_compl, if_pos hi, if_neg hi, not_false_eq_true,
          if_true]
        ring
    have hy : y a = fun i => if i ∈ I then d else 0 := by
      funext i
      by_cases hi : i ∈ I
      · simp only [y, a, d, if_pos hi]
        ring
      · simp [y, a, hi]
    have hcorner (W : Matrix (Finset ι) (Finset ι) ℝ) :
        F a W = (threeValueIntervalProfile W J K I : ℂ) * (c ^ Iᶜ.card * d ^ I.card) := by
      rw [hEval, hx, hy]
      simp only [subsetProductCoordinates_corner, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hsame : F a T = F a V := by rw [hT, hV, h a]
    rw [hcorner, hcorner] at hsame
    have hcd : c ^ Iᶜ.card * d ^ I.card ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (mul_ne_zero (sub_ne_zero.mpr h₁₂) (sub_ne_zero.mpr h₀₁)))
        (pow_ne_zero _ (mul_ne_zero (sub_ne_zero.mpr h₀₂.symm) (sub_ne_zero.mpr h₀₁.symm)))
    have hp := Complex.ofReal_injective (mul_right_cancel₀ hcd hsame)
    change threeValueIntervalProfile (∑ σ, w σ • subsetPermutationOperator σ) J K I = _ at hp
    rw [intervalProfile_weighted, hcase] at hp
    exact hp
  · intro h a
    change weightedMatchingValue a b w = determinantValue a b U
    apply mul_left_cancel₀ hprod
    rw [← hT, ← hV, hEval, hEval]
    apply Finset.sum_congr rfl
    intro I _
    have he : threeValueIntervalProfile T J K I = threeValueIntervalProfile V J K I := by
      dsimp only [T]
      rw [intervalProfile_weighted, hcase]
      exact h I
    rw [he]

/-- A positive normalized interval law proves the inclusion on the column partition. -/
theorem holds_of_three_value_interval_law {U : Matrix ι ι ℂ} (hU : IsUnitary U)
    (J K : Finset ι) (hJK : J ⊆ K) (w : Equiv.Perm ι → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hs : ∑ σ, w σ = 1)
    (hinterval : ∀ I : Finset ι,
      (∑ σ, if J.map σ.toEmbedding ⊆ I ∧ I ⊆ K.map σ.toEmbedding then w σ else 0) =
        ∑ S ∈ univ.filter (fun S => J ⊆ S ∧ S ⊆ K), subsetMinorSq U I S)
    (b₀ b₁ b₂ : ℂ) (h₀₁ : b₀ ≠ b₁) (h₀₂ : b₀ ≠ b₂) (h₁₂ : b₁ ≠ b₂)
    (a : ι → ℂ) : Holds a (threeValueIntervalSpectrum J K b₀ b₁ b₂) U :=
  holds_of_weights w hw hs
    ((three_value_common_weights_iff_interval hU J K hJK w b₀ b₁ b₂ h₀₁ h₀₂ h₁₂).mpr hinterval a)

end

end MOC
