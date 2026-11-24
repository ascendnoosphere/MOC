import MOC.FourParityCorrection

/-! Alternating parity kernels with several pinned domain positions.
Fixing two positions leaves three free in order five. -/

open Finset BigOperators

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_swap_outside_pins (S J : Finset ι) (hS : 3 ≤ Sᶜ.card) :
    ∃ u v : ι, u ≠ v ∧ u ∉ S ∧ v ∉ S ∧ (u ∈ J ↔ v ∈ J) := by
  let A := J \ S
  let B := Jᶜ \ S
  have hU : A ∪ B = Sᶜ := by
    ext x
    simp [A, B]
    tauto
  have hD : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hx).1
  have hc := Finset.card_union_of_disjoint hD
  rw [hU] at hc
  by_cases hA : 1 < A.card
  · obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hA
    obtain ⟨huJ, huS⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hvJ, hvS⟩ := Finset.mem_sdiff.mp hv
    exact ⟨u, v, huv, huS, hvS, iff_of_true huJ hvJ⟩
  · have hB : 1 < B.card := by omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hB
    obtain ⟨huJ, huS⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨hvJ, hvS⟩ := Finset.mem_sdiff.mp hv
    exact ⟨u, v, huv, huS, hvS, iff_of_false (Finset.mem_compl.mp huJ)
      (Finset.mem_compl.mp hvJ)⟩

/-- The parity kernel pinning any fixed set of source assignments has zero
every subset-image marginal if at least three labels are not pinned. -/
theorem sum_parity_at_pinned_assignments_subsetImage (S : Finset ι)
    (hS : 3 ≤ Sᶜ.card) (target : ι → ι) (I J : Finset ι) :
    ∑ σ : Equiv.Perm ι,
      (if (∀ j ∈ S, σ j = target j) ∧ J.map σ.toEmbedding = I
       then parityReal σ else 0) = 0 := by
  classical
  obtain ⟨u, v, huv, huS, hvS, hmem⟩ := exists_swap_outside_pins S J hS
  let τ : Equiv.Perm ι := Equiv.swap u v
  have hτS (j : ι) (hj : j ∈ S) : τ j = j :=
    Equiv.swap_apply_of_ne_of_ne
      (by rintro rfl; exact huS hj) (by rintro rfl; exact hvS hj)
  have hτJ : J.map τ.toEmbedding = J := by
    ext x
    rw [Finset.mem_map_equiv]
    change Equiv.swap u v x ∈ J ↔ x ∈ J
    by_cases hxu : x = u
    · subst x
      simpa using hmem.symm
    by_cases hxv : x = v
    · subst x
      simpa using hmem
    rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
  let f := fun σ : Equiv.Perm ι =>
    if (∀ j ∈ S, σ j = target j) ∧ J.map σ.toEmbedding = I then parityReal σ else 0
  have hf (σ : Equiv.Perm ι) : f (σ * τ) = -f σ := by
    have hJ : J.map (σ * τ).toEmbedding = J.map σ.toEmbedding := by
      rw [show (σ * τ).toEmbedding = τ.toEmbedding.trans σ.toEmbedding from rfl,
        ← Finset.map_map, hτJ]
    have hs : (∀ j ∈ S, (σ * τ) j = target j) ↔ ∀ j ∈ S, σ j = target j := by
      constructor <;> intro h j hj
      · simpa only [Equiv.Perm.mul_apply, hτS j hj] using h j hj
      · simpa only [Equiv.Perm.mul_apply, hτS j hj] using h j hj
    have hp : parityReal (σ * τ) = -parityReal σ := by
      simp [τ, parityReal, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap huv]
    change (if (∀ j ∈ S, (σ * τ) j = target j) ∧ J.map (σ * τ).toEmbedding = I
      then parityReal (σ * τ) else 0) =
      -(if (∀ j ∈ S, σ j = target j) ∧ J.map σ.toEmbedding = I then parityReal σ else 0)
    simp only [hs, hJ, hp]
    split_ifs <;> simp
  have he := Equiv.sum_comp (Equiv.mulRight τ) f
  change (∑ σ, f (σ * τ)) = ∑ σ, f σ at he
  simp_rw [hf, Finset.sum_neg_distrib] at he
  change ∑ σ, f σ = 0
  linarith

/-- In order five, any two assignment pins give a parity kernel. -/
theorem sum_parity_at_two_assignments_five (j k : Fin 5) (target : Fin 5 → Fin 5)
    (I J : Finset (Fin 5)) :
    ∑ σ : Equiv.Perm (Fin 5),
      (if (σ j = target j ∧ σ k = target k) ∧ J.map σ.toEmbedding = I
       then parityReal σ else 0) = 0 := by
  have hpair : ({j,k} : Finset (Fin 5)).card ≤ 2 := Finset.card_insert_le _ _
    |>.trans (by simp)
  have hc : 3 ≤ ({j,k} : Finset (Fin 5))ᶜ.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  simpa using sum_parity_at_pinned_assignments_subsetImage {j,k} hc target I J

end

end MOC
