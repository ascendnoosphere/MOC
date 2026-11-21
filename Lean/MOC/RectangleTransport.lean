import MOC.WeightedHall
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.BooleanAlgebra

/-! Rectangle inequalities split a nonnegative table into a transport plan
with prescribed margins and a remainder with constant margins. -/

open BigOperators Finset
open scoped Classical

namespace MOC

/-- In a square nonnegative table with row sums `p i + t` and column sums
`q j + t`, rectangle bounds provide a dominated plan with margins `p,q`. -/
theorem exists_margin_split_of_rectangle_bounds {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (p q : ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hA : ∀ i j, 0 ≤ A i j) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hr : ∀ i, ∑ j, A i j = p i + t) (hc : ∀ j, ∑ i, A i j = q j + t)
    (hrect : ∀ I J : Finset ι, ∑ i ∈ I, ∑ j ∈ J, A i j ≤ (I.card : ℝ) * t + ∑ j ∈ J, q j) :
    ∃ N : ι → ι → ℝ, (∀ i j, 0 ≤ N i j ∧ N i j ≤ A i j) ∧
      (∀ i, ∑ j, N i j = p i) ∧ (∀ j, ∑ i, N i j = q j) := by
  classical
  let supply : ι ⊕ ι → ℝ := Sum.elim p (fun _ => t)
  let demand (ij : ι × ι) := A ij.1 ij.2
  let R : (ι ⊕ ι) → (ι × ι) → Prop :=
    Sum.elim (fun i ij => i = ij.1) (fun j ij => j = ij.2)
  let M := ∑ ij : ι × ι, demand ij
  have hsup : (∑ k, supply k) = M := by
    simp only [M, demand, supply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Sum.elim_inl, Sum.elim_inr, hr, sum_add_distrib]
  have hsup0 : ∀ k, 0 ≤ supply k := fun k => Sum.rec (fun i => hp i) (fun _ => ht) k
  have hdem0 (ij : ι × ι) : 0 ≤ demand ij := hA _ _
  have hM0 : 0 ≤ M := sum_nonneg fun ij _ => hdem0 ij
  by_cases hM : M = 0
  · have hz (i j : ι) : A i j = 0 := by
      have hle : demand (i, j) ≤ M :=
        single_le_sum (fun ij _ => hdem0 ij) (mem_univ (i, j))
      rw [hM] at hle
      exact le_antisymm hle (hA i j)
    have hpz (i : ι) : p i = 0 := by
      have h := hr i
      simp only [hz, sum_const_zero] at h
      linarith only [h, hp i, ht]
    have hqz (j : ι) : q j = 0 := by
      have h := hc j
      simp only [hz, sum_const_zero] at h
      linarith only [h, hq j, ht]
    exact ⟨fun _ _ => 0, fun i j => ⟨le_rfl, hA i j⟩,
      fun i => by simp [hpz], fun j => by simp [hqz]⟩
  have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
  have hall (S : Finset (ι ⊕ ι)) :
      ∑ k ∈ S, supply k ≤ ∑ ij ∈ univ.filter (fun ij => ∃ k ∈ S, R k ij), demand ij := by
    let I := univ.filter fun i : ι => Sum.inl i ∈ S
    let J := univ.filter fun j : ι => Sum.inr j ∈ S
    have left : (∑ k ∈ S, supply k) = (∑ i ∈ I, p i) + ∑ j ∈ J, t := by
      calc
        _ = ∑ k, if k ∈ S then supply k else 0 := by
          rw [← Finset.sum_filter, Finset.filter_univ_mem]
        _ = _ := by
          simp only [I, J, Fintype.sum_sum_type, supply, Sum.elim_inl, Sum.elim_inr, Finset.sum_filter]
    have hR (i j : ι) : (∃ k ∈ S, R k (i, j)) ↔ Sum.inl i ∈ S ∨ Sum.inr j ∈ S := by
      constructor
      · rintro ⟨k, hk, hr⟩
        cases k with
        | inl i' => exact Or.inl ((show i' = i from hr) ▸ hk)
        | inr j' => exact Or.inr ((show j' = j from hr) ▸ hk)
      · rintro (hi | hj)
        · exact ⟨Sum.inl i, hi, rfl⟩
        · exact ⟨Sum.inr j, hj, rfl⟩
    have count (i j : ι) :
        (if ∃ k ∈ S, R k (i, j) then A i j else 0) =
          (if Sum.inl i ∈ S then A i j else 0) + (if Sum.inr j ∈ S then A i j else 0) -
            (if Sum.inl i ∈ S then (if Sum.inr j ∈ S then A i j else 0) else 0) := by
      rw [if_congr (hR i j) rfl rfl]
      by_cases hi : Sum.inl i ∈ S <;> by_cases hj : Sum.inr j ∈ S <;> simp [hi, hj]
    have right :
        (∑ ij ∈ univ.filter (fun ij => ∃ k ∈ S, R k ij), demand ij) =
          (∑ i ∈ I, ∑ j, A i j) + (∑ j ∈ J, ∑ i, A i j) - ∑ i ∈ I, ∑ j ∈ J, A i j := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      simp only [demand, count, sum_sub_distrib, sum_add_distrib, I, J, sum_filter]
      congr 1
      · congr 1
        · apply sum_congr rfl
          intro i _
          by_cases hi : Sum.inl i ∈ S <;> simp [hi]
        · rw [sum_comm]
          apply sum_congr rfl
          intro j _
          by_cases hj : Sum.inr j ∈ S <;> simp [hj]
      · apply sum_congr rfl
        intro i _
        by_cases hi : Sum.inl i ∈ S <;> simp [hi]
    rw [left, right]
    simp only [hr, hc, sum_add_distrib, sum_const, nsmul_eq_mul]
    linarith only [hrect I J]
  obtain ⟨μ, hμ, hrel, hμrow, hμcol⟩ := exists_transport_of_weighted_hall R
    (fun k => supply k / M) (fun ij => demand ij / M)
    (fun k => div_nonneg (hsup0 k) hM0) (fun ij => div_nonneg (hdem0 ij) hM0)
    (by rw [← sum_div, hsup, div_self hM])
    (by rw [← sum_div, show (∑ ij : ι × ι, demand ij) = M from rfl, div_self hM])
    (fun S => by simp only [← sum_div]; exact div_le_div_of_nonneg_right (hall S) hM0)
  let flow (k : ι ⊕ ι) (ij : ι × ι) := M * μ k ij
  have hflow0 (k : ι ⊕ ι) (ij : ι × ι) : 0 ≤ flow k ij := mul_nonneg hM0 (hμ k ij)
  have hflowRow (k : ι ⊕ ι) : (∑ ij, flow k ij) = supply k := by
    change (∑ ij, M * μ k ij) = supply k
    rw [← mul_sum, hμrow, ← mul_div_assoc, mul_div_cancel_left₀ _ hM]
  have hflowCol (ij : ι × ι) : (∑ k, flow k ij) = demand ij := by
    change (∑ k, M * μ k ij) = demand ij
    rw [← mul_sum, hμcol, ← mul_div_assoc, mul_div_cancel_left₀ _ hM]
  have hzero (k : ι ⊕ ι) (ij : ι × ι) (h : ¬ R k ij) : flow k ij = 0 := by
    have hz : μ k ij = 0 := Classical.byContradiction fun hne => h (hrel k ij hne)
    simp [flow, hz]
  let N (i j : ι) := flow (.inl i) (i, j)
  let Q (i j : ι) := flow (.inr j) (i, j)
  have hsplit (i j : ι) : N i j + Q i j = A i j := by
    have h := hflowCol (i, j)
    rw [Fintype.sum_sum_type] at h
    have hl : (∑ k : ι, flow (.inl k) (i, j)) = N i j := by
      change (∑ k : ι, flow (.inl k) (i, j)) = flow (.inl i) (i, j)
      apply Finset.sum_eq_single
      · intro k _ hne; exact hzero (.inl k) (i, j) hne
      · simp
    have hr : (∑ k : ι, flow (.inr k) (i, j)) = Q i j := by
      change (∑ k : ι, flow (.inr k) (i, j)) = flow (.inr j) (i, j)
      apply Finset.sum_eq_single
      · intro k _ hne; exact hzero (.inr k) (i, j) hne
      · simp
    rwa [hl, hr] at h
  have hrows (i : ι) : (∑ j, N i j) = p i := by
    have h := hflowRow (.inl i)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i] at h
    · exact h
    · intro i' _ hne
      exact sum_eq_zero (fun j _ => hzero (.inl i) (i', j) (Ne.symm hne))
    · simp
  have hcols (j : ι) : (∑ i, Q i j) = t := by
    have h := hflowRow (.inr j)
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single j] at h
    · exact h
    · intro j' _ hne
      exact sum_eq_zero (fun i _ => hzero (.inr j) (i, j') (Ne.symm hne))
    · simp
  refine ⟨N, fun i j => ⟨hflow0 _ _, ?_⟩, hrows, ?_⟩
  · rw [← hsplit i j]
    exact le_add_of_nonneg_right (hflow0 _ _)
  · intro j
    have h := Finset.sum_congr (rfl : (univ : Finset ι) = univ) (fun i _ => hsplit i j)
    rw [sum_add_distrib, hcols, hc] at h
    exact add_right_cancel h

end MOC
