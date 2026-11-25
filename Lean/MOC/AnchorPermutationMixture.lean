import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! One probability law realizes the anchor entry, the adjoining row and
column, and every two-by-two minor containing both of them. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem anchored_fixed_weights (A N : ι → ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hle : ∀ i j, N i j ≤ A i j)
    (hr : ∀ i, ∑ j, (A i j - N i j) = t)
    (hc : ∀ j, ∑ i, (A i j - N i j) = t) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = t) ∧
      ∀ i j, (∑ σ, if σ j = i then w σ else 0) = A i j - N i j := by
  by_cases hz : t = 0
  · have hA (i j : ι) : A i j - N i j = 0 := by
      have h : A i j - N i j ≤ ∑ l, (A i l - N i l) :=
        single_le_sum (fun k _ => sub_nonneg.mpr (hle i k)) (mem_univ j)
      rw [hr, hz] at h
      exact le_antisymm h (sub_nonneg.mpr (hle i j))
    exact ⟨fun _ => 0, fun _ => le_rfl, by simp [hz], fun i j => by simp [hA i j]⟩
  let D : Matrix ι ι ℝ := Matrix.of fun j i => (A i j - N i j) / t
  have hD : D ∈ doublyStochastic ℝ ι := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun j i => div_nonneg (sub_nonneg.mpr (hle i j)) ht, ?_, ?_⟩
    · intro j
      change (∑ i, (A i j - N i j) / t) = 1
      rw [← sum_div, hc, div_self hz]
    · intro i
      change (∑ j, (A i j - N i j) / t) = 1
      rw [← sum_div, hr, div_self hz]
  obtain ⟨v, hv, hv₁, hD'⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  refine ⟨fun σ => t * v σ, fun σ => mul_nonneg ht (hv σ), ?_, fun i j => ?_⟩
  · rw [← mul_sum, hv₁, mul_one]
  · have h := congrArg (fun L : Matrix ι ι ℝ => L j i) hD'
    have h' : (∑ σ, if σ j = i then v σ else 0) = (A i j - N i j) / t := by
      simpa [D, Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        mul_ite, eq_comm] using h
    calc
      _ = t * ∑ σ, if σ j = i then v σ else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro σ _
        by_cases hs : σ j = i <;> simp [hs]
      _ = _ := by rw [h', ← mul_div_assoc, mul_div_cancel_left₀ _ hz]

private def anchoredFix (σ : Equiv.Perm ι) : Equiv.Perm (Unit ⊕ ι) :=
  Equiv.sumCongr (Equiv.refl Unit) σ

private def anchoredMove (k l : ι) : Equiv.Perm (Unit ⊕ ι) :=
  (anchoredFix (Equiv.swap l k)).trans (Equiv.swap (.inl ()) (.inr k))

private theorem anchoredMove_anchor (k l : ι) :
    anchoredMove k l (.inl ()) = .inr k := by
  change Equiv.swap (Sum.inl () : Unit ⊕ ι) (.inr k) (.inl ()) = .inr k
  simp

private theorem anchoredMove_tail_eq_anchor_iff (k l j : ι) :
    anchoredMove k l (.inr j) = .inl () ↔ j = l := by
  change Equiv.swap (Sum.inl () : Unit ⊕ ι) (.inr k) (.inr (Equiv.swap l k j)) =
    .inl () ↔ j = l
  have hk : Equiv.swap (Sum.inl () : Unit ⊕ ι) (.inr k) (.inr k) = .inl () := by simp
  constructor
  · intro h
    have h' := Sum.inr.inj ((Equiv.swap (Sum.inl ()) (.inr k)).injective (h.trans hk.symm))
    exact (Equiv.swap l k).injective (h'.trans (Equiv.swap_apply_left l k).symm)
  · rintro rfl
    rw [Equiv.swap_apply_left]
    exact hk

/-- A dominated plan with the two opposite singleton margins gives one
matching distribution for the corresponding anchored pair events. -/
theorem exists_anchored_permutation_mixture_of_split
    (A N : ι → ι → ℝ) (p q : ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hn : ∀ i j, 0 ≤ N i j ∧ N i j ≤ A i j)
    (hNr : ∀ i, ∑ j, N i j = p i) (hNc : ∀ j, ∑ i, N i j = q j)
    (hr : ∀ i, ∑ j, A i j = p i + t) (hc : ∀ j, ∑ i, A i j = q j + t)
    (hmass : t + ∑ i, p i = 1) :
    ∃ (σ : (Equiv.Perm ι ⊕ (ι × ι)) → Equiv.Perm (Unit ⊕ ι))
      (w : (Equiv.Perm ι ⊕ (ι × ι)) → ℝ),
      (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧
      (∑ a, if σ a (.inl ()) = .inl () then w a else 0) = t ∧
      (∀ i, (∑ a, if σ a (.inl ()) = .inr i then w a else 0) = p i) ∧
      (∀ j, (∑ a, if σ a (.inr j) = .inl () then w a else 0) = q j) ∧
      ∀ i j, (∑ a, if
        (σ a (.inl ()) = .inl () ∧ σ a (.inr j) = .inr i) ∨
        (σ a (.inl ()) = .inr i ∧ σ a (.inr j) = .inl ())
        then w a else 0) = A i j := by
  classical
  obtain ⟨v, hv, hv₁, hvpair⟩ := anchored_fixed_weights A N t ht (fun i j => (hn i j).2)
    (fun i => by rw [sum_sub_distrib, hr, hNr]; ring)
    (fun j => by rw [sum_sub_distrib, hc, hNc]; ring)
  let σ : Equiv.Perm ι ⊕ (ι × ι) → Equiv.Perm (Unit ⊕ ι) :=
    Sum.elim anchoredFix (fun kl => anchoredMove kl.1 kl.2)
  let w : Equiv.Perm ι ⊕ (ι × ι) → ℝ := Sum.elim v (fun kl => N kl.1 kl.2)
  have hfix₀ (τ : Equiv.Perm ι) : σ (.inl τ) (.inl ()) = .inl () := rfl
  have hfix₁ (τ : Equiv.Perm ι) (j : ι) : σ (.inl τ) (.inr j) = .inr (τ j) := rfl
  have hmove₀ (kl : ι × ι) : σ (.inr kl) (.inl ()) = .inr kl.1 := anchoredMove_anchor _ _
  have hmove₁ (kl : ι × ι) (j : ι) : σ (.inr kl) (.inr j) = .inl () ↔ j = kl.2 :=
    anchoredMove_tail_eq_anchor_iff _ _ _
  refine ⟨σ, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (τ | kl)
    · exact hv τ
    · exact (hn kl.1 kl.2).1
  · simp only [w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      hv₁, hNr, hmass]
  · simp [w, Fintype.sum_sum_type, hfix₀, hmove₀, hv₁]
  · intro i
    simp only [w, Fintype.sum_sum_type, Fintype.sum_prod_type, hfix₀, hmove₀,
      Sum.elim_inr, Sum.inl_ne_inr, Sum.inr.injEq, if_false, sum_const_zero, zero_add]
    rw [sum_comm]
    simp [hNr]
  · intro j
    simp only [w, Fintype.sum_sum_type, Fintype.sum_prod_type, hfix₁, hmove₁,
      Sum.elim_inr, Sum.inr_ne_inl, if_false, sum_const_zero, zero_add]
    simp [hNc]
  · intro i j
    simp only [w, Fintype.sum_sum_type, Fintype.sum_prod_type, hfix₀, hfix₁, hmove₀, hmove₁,
      Sum.elim_inl, Sum.elim_inr, Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inr.injEq,
      true_and, false_and, or_false, false_or, hvpair, ite_and]
    have hinner (k : ι) : (∑ l, if k = i then (if j = l then N k l else 0) else 0) =
        if k = i then N k j else 0 := by
      by_cases h : k = i <;> simp [h]
    simp [hinner]

end

end MOC
