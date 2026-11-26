import MOC.MatchingDeterminantalRealization
import MOC.WeightedPermutationCycle
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! An exact determinant realization for a product of matrix entries.
Each state selects one entry. A cyclic permutation joins the states. -/

open BigOperators Matrix
open scoped Kronecker Matrix.L2OpNorm

namespace MOC

noncomputable section

variable {ι κ γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private def coordinateEmbedding (f : κ → ι) : Matrix (ι × κ) κ ℂ :=
  Matrix.of fun u s => if u = (f s, s) then 1 else 0

private theorem conj_coordinateEmbedding_mul_apply (f : κ → ι)
    (A : Matrix (ι × κ) γ ℂ) (s : κ) (v : γ) :
    ((coordinateEmbedding f)ᴴ * A) s v = A (f s, s) v := by
  rw [Matrix.mul_apply]
  calc
    _ = ∑ u : ι × κ, if u = (f s, s) then A u v else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : u = (f s, s)
      all_goals simp [coordinateEmbedding, Matrix.conjTranspose_apply, h]
    _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem mul_coordinateEmbedding_apply (f : κ → ι)
    (A : Matrix γ (ι × κ) ℂ) (v : γ) (s : κ) :
    (A * coordinateEmbedding f) v s = A v (f s, s) := by
  rw [Matrix.mul_apply]
  calc
    _ = ∑ u : ι × κ, if u = (f s, s) then A v u else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : u = (f s, s)
      all_goals simp [coordinateEmbedding, h]
    _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem norm_coordinateEmbedding [Nonempty κ] (f : κ → ι) :
    ‖coordinateEmbedding f‖ = 1 := by
  have he : (coordinateEmbedding f)ᴴ * coordinateEmbedding f = 1 := by
    ext s t : 1
    rw [conj_coordinateEmbedding_mul_apply]
    by_cases h : s = t
    · subst t
      simp [coordinateEmbedding]
    · have hp : (f s, s) ≠ (f t, t) := fun e => h (congrArg Prod.snd e)
      simp [coordinateEmbedding, Matrix.one_apply, h, hp]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self, he, norm_one, one_pow]

private theorem coordinateEmbedding_compress (f g : κ → ι) (Z : Matrix ι ι ℂ) :
    ((coordinateEmbedding f)ᴴ * (Z ⊗ₖ (1 : Matrix κ κ ℂ))) * coordinateEmbedding g =
      diagonal (fun s => Z (f s) (g s)) := by
  ext s t : 1
  rw [mul_coordinateEmbedding_apply, conj_coordinateEmbedding_mul_apply, Matrix.kronecker_apply]
  by_cases h : s = t
  · subst t
    simp
  · simp [Matrix.one_apply, Matrix.diagonal_apply_ne _ h, h]

private theorem norm_complex_perm_sign {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) : ‖((p.sign : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or p.sign with h | h <;> simp [h]

/-- The linear state pencil realizes a scalar multiple of any product of
`n` matrix entries. Its operator norm to the power `n` is at most the
modulus of the coefficient. -/
theorem exists_determinantal_realization_monomial {n : ℕ} (hn : 2 ≤ n)
    (f g : Fin n → ι) (q : ℂ) :
    ∃ K : Matrix (ι × Fin n) (ι × Fin n) ℂ, ‖K‖ ^ n ≤ ‖q‖ ∧
      ∀ Z : Matrix ι ι ℂ,
        (1 - K * (Z ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))).det =
          1 - q * ∏ s : Fin n, Z (f s) (g s) := by
  letI : NeZero n := ⟨by omega⟩
  letI : Nonempty (Fin n) := ⟨0⟩
  let p := finRotate n
  have hmove (s : Fin n) : p s ≠ s := by
    apply Equiv.Perm.mem_support.mp
    change s ∈ (finRotate n).support
    rw [support_finRotate_of_le hn]
    exact Finset.mem_univ s
  have hp : p ≠ 1 := by
    intro h
    apply hmove 0
    rw [h, Equiv.Perm.one_apply]
  have hcycle : TraversesAllIndices p := fun s t =>
    (isCycle_finRotate_of_le hn).exists_pow_eq (hmove s) (hmove t)
  let P := p.symm.permMatrix ℂ
  have hPE (s t : Fin n) : P s t = if s = p t then 1 else 0 := by
    by_cases h : s = p t
    · subst s
      simp [P, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    · have h' : t ≠ p.symm s := fun he => h (by rw [he, p.apply_symm_apply])
      simp [P, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, h, h', Ne.symm h']
  have hPn : ‖P‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff.mpr (isUnitary_permMatrix p.symm).1)
  let e := ((p.sign : ℤ) : ℂ)
  have hen : ‖e‖ = 1 := norm_complex_perm_sign p
  have he : e ≠ 0 := norm_pos_iff.mp (hen.symm ▸ zero_lt_one)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (-q / e) (show 0 < n by omega)
  have htn : ‖t‖ ^ n = ‖q‖ := by rw [← norm_pow, ht, norm_div, norm_neg, hen, div_one]
  let E := coordinateEmbedding f
  let F := coordinateEmbedding g
  have hEn : ‖E‖ = 1 := norm_coordinateEmbedding f
  have hFn : ‖F‖ = 1 := norm_coordinateEmbedding g
  let A := (-t) • (P * Eᴴ)
  let K := F * A
  have hA : ‖A‖ ≤ ‖t‖ := by
    change ‖(-t) • (P * Eᴴ)‖ ≤ ‖t‖
    rw [norm_smul, norm_neg]
    apply mul_le_of_le_one_right (norm_nonneg t)
    have hb := Matrix.l2_opNorm_mul P Eᴴ
    rw [Matrix.l2_opNorm_conjTranspose, hPn, hEn, one_mul] at hb
    exact hb
  have hK : ‖K‖ ≤ ‖t‖ := by
    change ‖F * A‖ ≤ ‖t‖
    have hb := Matrix.l2_opNorm_mul F A
    rw [hFn, one_mul] at hb
    exact hb.trans hA
  refine ⟨K, (pow_le_pow_left₀ (norm_nonneg K) hK n).trans_eq htn, fun Z => ?_⟩
  let V := Z ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)
  have hZ : (Eᴴ * V) * F = diagonal (fun s => Z (f s) (g s)) :=
    coordinateEmbedding_compress f g Z
  have hcycleMatrix : t • (P * diagonal (fun s => Z (f s) (g s))) =
      weightedPermutationMatrix p (fun s => t * Z (f s) (g s)) := by
    ext s u : 1
    rw [Matrix.smul_apply, Matrix.mul_diagonal, hPE, smul_eq_mul]
    simp only [weightedPermutationMatrix, Matrix.of_apply]
    split <;> simp
  have hmatrix : (A * V) * F = -weightedPermutationMatrix p (fun s => t * Z (f s) (g s)) := by
    change (((-t) • (P * Eᴴ)) * V) * F = _
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc (P * Eᴴ) V F,
      Matrix.mul_assoc P Eᴴ (V * F), ← Matrix.mul_assoc Eᴴ V F, hZ,
      neg_smul, hcycleMatrix]
  change (1 - (F * A) * V).det = _
  rw [Matrix.mul_assoc, Matrix.det_one_sub_mul_comm F (A * V), hmatrix, sub_neg_eq_add,
    ← Matrix.diagonal_one, det_diagonal_add_weightedPermutationMatrix _ _ hcycle hp]
  simp only [Finset.prod_const_one, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_pow, ht]
  change 1 + e * ((-q / e) * ∏ s : Fin n, Z (f s) (g s)) = _
  rw [← mul_assoc, mul_comm e (-q / e), div_mul_cancel₀ _ he, neg_mul, sub_eq_add_neg]

/-- If all other matching products equal the center, this pencil realizes
the centered matching polynomial. -/
theorem exists_matching_realization_of_single_coefficient {n : ℕ} (hn : 2 ≤ n)
    (a b : Fin n → ℂ) (c : ℂ) (σ : Equiv.Perm (Fin n))
    (hzero : ∀ τ : Equiv.Perm (Fin n), τ ≠ σ → matchingProduct a b τ = c) :
    ∃ K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
      ‖K‖ ^ n ≤ ‖matchingProduct a b σ - c‖ ∧
      ∀ Z : Matrix (Fin n) (Fin n) ℂ,
        1 - shiftedMatchingEvaluation a b c Z =
          (1 - K * (Z ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))).det := by
  let q := ((σ.sign : ℤ) : ℂ) * (matchingProduct a b σ - c)
  obtain ⟨K, hK, hdet⟩ := exists_determinantal_realization_monomial hn σ id q
  have hq : ‖q‖ = ‖matchingProduct a b σ - c‖ := by
    rw [q, norm_mul, norm_complex_perm_sign, one_mul]
  refine ⟨K, hK.trans_eq hq, fun Z => ?_⟩
  rw [hdet, shiftedMatchingEvaluation_eq_sum,
    Finset.sum_eq_single σ (fun τ _ hτ => by rw [hzero τ hτ, sub_self, mul_zero])
      (fun hs => (hs (Finset.mem_univ σ)).elim)]
  simp only [leibnizTerm, id, q]
  ring

/-- A single centered matching coefficient has a strict realization at
every budget whose `n`th power exceeds its modulus. -/
theorem exists_strict_matching_realization_of_single_coefficient {n : ℕ} (hn : 2 ≤ n)
    (a b : Fin n → ℂ) (c : ℂ) (σ : Equiv.Perm (Fin n))
    (hzero : ∀ τ : Equiv.Perm (Fin n), τ ≠ σ → matchingProduct a b τ = c)
    (r : ℝ) (hr : 0 < r) (hbudget : ‖matchingProduct a b σ - c‖ < r ^ n) :
    ∃ K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, ‖K‖ < r ∧
      ∀ Z : Matrix (Fin n) (Fin n) ℂ,
        1 - shiftedMatchingEvaluation a b c Z =
          (1 - K * (Z ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))).det := by
  obtain ⟨K, hK, hrep⟩ := exists_matching_realization_of_single_coefficient hn a b c σ hzero
  exact ⟨K, lt_of_pow_lt_pow_left₀ n hr.le (hK.trans_lt hbudget), hrep⟩

/-- The cyclic pencil attains the optimal norm for a single centered
matching coefficient. -/
theorem matchingRealizationRadius_eq_single_coefficient {n : ℕ} (hn : 2 ≤ n)
    (a b : Fin n → ℂ) (c : ℂ) (σ : Equiv.Perm (Fin n))
    (hzero : ∀ τ : Equiv.Perm (Fin n), τ ≠ σ → matchingProduct a b τ = c) :
    matchingRealizationRadius a b c = ‖matchingProduct a b σ - c‖ ^ ((n : ℝ)⁻¹) := by
  letI : NeZero n := ⟨by omega⟩
  letI : Nonempty (Fin n) := ⟨0⟩
  have hn' : n ≠ 0 := by omega
  let M := ‖matchingProduct a b σ - c‖
  let r := M ^ ((n : ℝ)⁻¹)
  have hr : 0 ≤ r := Real.rpow_nonneg (norm_nonneg _) _
  have hrpow : r ^ n = M := Real.rpow_inv_natCast_pow (norm_nonneg _) hn'
  obtain ⟨U, hU, hval⟩ := matchingProduct_mem_determinantRange a b σ
  let S := matchingRealizationNorms a b c
  have hl (s : ℝ) (hs : s ∈ S) : r ≤ s := by
    obtain ⟨k, hk, K, rfl, hrep⟩ := hs
    have hh := norm_shiftedMatchingEvaluation_le_of_realization a b c hk K hrep U hU
    rw [norm_shiftedMatchingEvaluation_unitary a b c U hU, hval, Fintype.card_fin] at hh
    exact le_of_pow_le_pow_left₀ hn' (norm_nonneg K) (hrpow.trans_le hh)
  obtain ⟨K, hK, hrep⟩ := exists_matching_realization_of_single_coefficient hn a b c σ hzero
  have hmem : ‖K‖ ∈ S := ⟨n, by omega, K, rfl, hrep⟩
  have hKr : ‖K‖ ≤ r := le_of_pow_le_pow_left₀ hn' hr (hK.trans_eq hrpow.symm)
  change sInf S = r
  exact le_antisymm ((csInf_le ⟨r, hl⟩ hmem).trans hKr) (le_csInf ⟨‖K‖, hmem⟩ hl)

end

end MOC
