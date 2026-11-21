import MOC.Weights
import Mathlib.Tactic.Linarith

/-! A Birkhoff law can give any supported permutation strictly positive weight. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A permutation using only positive entries of a doubly stochastic
matrix occurs with positive weight in some Birkhoff decomposition. -/
theorem exists_birkhoff_weight_pos {D : Matrix ι ι ℝ} (hD : D ∈ doublyStochastic ℝ ι)
    (σ : Equiv.Perm ι) (hσ : ∀ j, 0 < D j (σ j)) :
    ∃ w : Equiv.Perm ι → ℝ,
      (∀ τ, 0 ≤ w τ) ∧ 0 < w σ ∧ (∑ τ, w τ) = 1 ∧
        D = ∑ τ, w τ • τ.permMatrix ℝ := by
  classical
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_min_image Finset.univ (fun j => D j (σ j))
    Finset.univ_nonempty
  let ε := D j₀ (σ j₀) / 2
  let P := σ.permMatrix ℝ
  have hε : 0 < ε := div_pos (hσ j₀) (by norm_num)
  have hεlt : ε < 1 := by
    dsimp only [ε]
    have h := le_one_of_mem_doublyStochastic hD (i := j₀) (j := σ j₀)
    linarith only [h]
  have h₁ε : 0 < 1 - ε := sub_pos.mpr hεlt
  let E := (1 - ε)⁻¹ • (D - ε • P)
  have hP : P ∈ doublyStochastic ℝ ι := permMatrix_mem_doublyStochastic
  have hperm (j i : ι) : P j i = (if σ j = i then 1 else 0) := by
    simp [P, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]
  have hE : E ∈ doublyStochastic ℝ ι := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun j i => ?_, fun j => ?_, fun i => ?_⟩
    · change 0 ≤ (1 - ε)⁻¹ * (D j i - ε * P j i)
      refine mul_nonneg (inv_pos.mpr h₁ε).le (sub_nonneg.mpr ?_)
      rw [hperm]
      split_ifs with he
      · subst i
        rw [mul_one]
        have hle := hj₀ j (Finset.mem_univ j)
        dsimp only [ε] at hε ⊢
        linarith only [hle, hε]
      · simpa using (nonneg_of_mem_doublyStochastic hD (i := j) (j := i))
    · change (∑ i, (1 - ε)⁻¹ * (D j i - ε * P j i)) = 1
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib,
        sum_row_of_mem_doublyStochastic hD, sum_row_of_mem_doublyStochastic hP,
        mul_one, inv_mul_cancel₀ h₁ε.ne']
    · change (∑ j, (1 - ε)⁻¹ * (D j i - ε * P j i)) = 1
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib,
        sum_col_of_mem_doublyStochastic hD, sum_col_of_mem_doublyStochastic hP,
        mul_one, inv_mul_cancel₀ h₁ε.ne']
  obtain ⟨v, hv, hs, hsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hE
  let w (τ : Equiv.Perm ι) := (1 - ε) * v τ + if τ = σ then ε else 0
  refine ⟨w, fun τ => ?_, ?_, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg h₁ε.le (hv τ)) (by split_ifs <;> positivity)
  · simpa only [w, if_pos rfl] using add_pos_of_nonneg_of_pos (mul_nonneg h₁ε.le (hv σ)) hε
  · simp only [w, Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_one]
    rw [show (∑ τ : Equiv.Perm ι, if τ = σ then ε else 0) = ε by simp]
    ring
  · have hp : (∑ τ : Equiv.Perm ι, (if τ = σ then ε else 0) • τ.permMatrix ℝ) = ε • P := by
      simp [P, ite_smul]
    have hD' : D = (1 - ε) • E + ε • P := by
      simp only [E, smul_smul, mul_inv_cancel₀ h₁ε.ne', one_smul, sub_add_cancel]
    rw [hD', ← hsum, Finset.smul_sum, ← hp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro τ _
    rw [smul_smul, ← add_smul]

/-- A full-support unitary admits one singleton law assigning positive weight
to every permutation at once. -/
theorem exists_pos_singleton_weights (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hUpos : ∀ i j, U i j ≠ 0) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 < w σ) ∧ (∑ σ, w σ) = 1 ∧
      ∀ i j, marginal (fun σ => (w σ : ℂ)) i j = (Complex.normSq (U i j) : ℂ) := by
  classical
  let D : Matrix ι ι ℝ := Matrix.of (fun j i => Complex.normSq (U i j))
  have hD : D ∈ doublyStochastic ℝ ι := normSq_transpose_doublyStochastic U hU
  have h (σ : Equiv.Perm ι) := exists_birkhoff_weight_pos hD σ
    (fun j => Complex.normSq_pos.mpr (hUpos (σ j) j))
  choose f hf using h
  let N : ℝ := Fintype.card (Equiv.Perm ι)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  let w (τ : Equiv.Perm ι) := (∑ σ, f σ τ) / N
  have havg (g : Equiv.Perm ι → Equiv.Perm ι → ℝ) (c : ℝ)
      (hg : ∀ σ, (∑ τ, g σ τ) = c) : ((∑ τ, (∑ σ, g σ τ) / N)) = c := by
    rw [← Finset.sum_div, Finset.sum_comm]
    simp only [hg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change N * c / N = c
    field_simp [hN.ne'] <;> ring
  refine ⟨w, fun τ => ?_, havg f 1 (fun σ => (hf σ).2.2.1), fun i j => ?_⟩
  · exact div_pos ((hf τ).2.1.trans_le (Finset.single_le_sum
      (fun σ _ => (hf σ).1 τ) (Finset.mem_univ τ))) hN
  · have hfm (σ : Equiv.Perm ι) :
        (∑ τ, if τ j = i then f σ τ else 0) = Complex.normSq (U i j) := by
      have he := congrArg (fun M : Matrix ι ι ℝ => M j i) (hf σ).2.2.2
      simpa [D, Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply, mul_ite, eq_comm] using he.symm
    have hterm (τ : Equiv.Perm ι) : (if τ j = i then w τ else 0) =
        (∑ σ, if τ j = i then f σ τ else 0) / N := by
      split_ifs <;> simp [w]
    have hwavg : (∑ τ, if τ j = i then w τ else 0) = Complex.normSq (U i j) := by
      simp only [hterm]
      exact havg (fun σ τ => if τ j = i then f σ τ else 0) _ hfm
    unfold marginal
    simpa only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using
      congrArg Complex.ofReal hwavg

/-- If a linear functional is minimized over all permutation matrices at
a doubly stochastic matrix, every supported permutation has the same value. -/
theorem linearMap_eq_of_birkhoff_min {D : Matrix ι ι ℝ} (hD : D ∈ doublyStochastic ℝ ι)
    (F : Matrix ι ι ℝ →ₗ[ℝ] ℝ) (hmin : ∀ τ : Equiv.Perm ι, F D ≤ F (τ.permMatrix ℝ))
    (σ : Equiv.Perm ι) (hσ : ∀ j, 0 < D j (σ j)) :
    F (σ.permMatrix ℝ) = F D := by
  obtain ⟨w, hw, hwσ, hs, hD'⟩ := exists_birkhoff_weight_pos hD σ hσ
  have he := congrArg F hD'
  simp only [map_sum, map_smul, smul_eq_mul] at he
  have hz : (∑ τ : Equiv.Perm ι, w τ * (F (τ.permMatrix ℝ) - F D)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul, ← he, sub_self]
  have hnonneg (τ : Equiv.Perm ι) (_ : τ ∈ Finset.univ) :
      0 ≤ w τ * (F (τ.permMatrix ℝ) - F D) := mul_nonneg (hw τ) (sub_nonneg.mpr (hmin τ))
  have h := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz σ (Finset.mem_univ σ)
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hwσ.ne')

end

end MOC
