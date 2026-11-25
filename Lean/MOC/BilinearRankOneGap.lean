import MOC.Weights
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Along a line between two rank-one kernels, matching laws with identical
singleton marginals can differ only in the middle subset terms. -/

open BigOperators Finset

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem prod_compl_singleton (f : ι → ℂ) (j : ι) :
    (∏ i ∈ ({j} : Finset ι)ᶜ, f i) = exceptProduct f j := by
  have he : ({j} : Finset ι)ᶜ = univ.filter (fun i => i ≠ j) := by
    ext i
    simp
  rw [he, Finset.prod_filter]
  unfold exceptProduct
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i = j <;> simp [h]

private theorem weighted_middle_coefficient_eq_zero_of_card_le_one
    (l m r n : ι → ℂ) (μ : Equiv.Perm ι → ℂ)
    (h₀ : ∑ σ, μ σ = 0) (h₁ : ∀ i j, marginal μ i j = 0)
    (S : Finset ι) (hS : S.card ≤ 1) :
    (∑ σ, μ σ * ((∏ j ∈ S, m (σ j) * n j) * ∏ j ∈ Sᶜ, l (σ j) * r j)) = 0 := by
  rcases (show S.card = 0 ∨ S.card = 1 by omega) with h | h
  · rw [Finset.card_eq_zero.mp h]
    have hconst (σ : Equiv.Perm ι) :
        (∏ j ∈ (∅ : Finset ι), m (σ j) * n j) * ∏ j ∈ (∅ : Finset ι)ᶜ, l (σ j) * r j =
          (∏ j, l j) * ∏ j, r j := by
      simp only [Finset.prod_empty, Finset.compl_empty, one_mul, Finset.prod_mul_distrib,
        Equiv.prod_comp σ l]
    simp only [hconst, ← Finset.sum_mul, h₀, zero_mul]
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h
    have ht (σ : Equiv.Perm ι) :
        (∏ k ∈ ({j} : Finset ι), m (σ k) * n k) * ∏ k ∈ ({j} : Finset ι)ᶜ, l (σ k) * r k =
          (m (σ j) * n j) * (exceptProduct l (σ j) * exceptProduct r j) := by
      rw [Finset.prod_singleton, Finset.prod_mul_distrib,
        prod_compl_singleton (fun k => l (σ k)) j, prod_compl_singleton r j]
      exact congrArg (fun z => (m (σ j) * n j) * (z * exceptProduct r j)) (exceptProduct_comp l σ j)
    simp only [ht]
    rw [sum_weighted_evaluation μ j (fun i => (m i * n j) * (exceptProduct l i * exceptProduct r j))]
    simp only [h₁, zero_mul, Finset.sum_const_zero]

/-- Matching laws that agree on mass and singleton assignments have no gap
terms with fewer than two factors from either of the two rank-one kernels. -/
theorem rankOne_matching_gap_eq_middle_subsets (l m r n : ι → ℂ) (μ : Equiv.Perm ι → ℂ)
    (h₀ : ∑ σ, μ σ = 0) (h₁ : ∀ i j, marginal μ i j = 0) (t : ℂ) :
    (∑ σ, μ σ * ∏ j, (l (σ j) * r j + t * (m (σ j) * n j))) =
      ∑ S ∈ (univ : Finset (Finset ι)).filter (fun S => 2 ≤ S.card ∧ 2 ≤ (Sᶜ).card),
        t ^ S.card * ∑ σ, μ σ * ((∏ j ∈ S, m (σ j) * n j) * ∏ j ∈ Sᶜ, l (σ j) * r j) := by
  classical
  let C (S : Finset ι) := ∑ σ, μ σ * ((∏ j ∈ S, m (σ j) * n j) * ∏ j ∈ Sᶜ, l (σ j) * r j)
  have hp (σ : Equiv.Perm ι) :
      (∏ j, (l (σ j) * r j + t * (m (σ j) * n j))) =
        ∑ S : Finset ι, t ^ S.card * ((∏ j ∈ S, m (σ j) * n j) * ∏ j ∈ Sᶜ, l (σ j) * r j) := calc
    _ = ∏ j, (t * (m (σ j) * n j) + l (σ j) * r j) :=
      Finset.prod_congr rfl (fun _ _ => add_comm _ _)
    _ = _ := by
      rw [Fintype.prod_add]
      simp only [Finset.prod_mul_distrib, Finset.prod_const, mul_assoc]
  have hsum : (∑ σ, μ σ * ∏ j, (l (σ j) * r j + t * (m (σ j) * n j))) =
      ∑ S : Finset ι, t ^ S.card * C S := by
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    dsimp only [C]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [hsum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : 2 ≤ S.card ∧ 2 ≤ (Sᶜ).card
  · simp [hS, C]
  · simp only [hS, if_false]
    have hz : C S = 0 := by
      rcases (show S.card ≤ 1 ∨ (Sᶜ).card ≤ 1 by omega) with h | h
      · exact weighted_middle_coefficient_eq_zero_of_card_le_one l m r n μ h₀ h₁ S h
      · have hg := weighted_middle_coefficient_eq_zero_of_card_le_one m l n r μ h₀ h₁ Sᶜ h
        simpa only [C, compl_compl, mul_comm] using hg
    rw [hz, mul_zero]

end

end MOC
