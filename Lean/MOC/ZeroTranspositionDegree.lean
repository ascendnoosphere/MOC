import MOC.Core
import MOC.OppositePair
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Finset.Prod

/-! Forbidden cross-entries control the number of vanished transposition
neighbors of any nonzero matching, without enumerating permutations. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distinct transpositions that kill a nonzero matching can be charged to
distinct zero cross-entries. This applies to any pattern of zero rectangles. -/
theorem card_zero_swap_neighbors_le_cross_zeros
    (a b : ι → ℂ) (r : Equiv.Perm ι) (hr : matchingProduct a b r ≠ 0) :
    (Finset.univ.filter (fun σ : Equiv.Perm ι =>
      σ.support.card = 2 ∧ matchingProduct a b (r * σ) = 0)).card ≤
    (Finset.univ.filter (fun ij : ι × ι => a ij.1 + b ij.2 = 0)).card := by
  classical
  let T := Finset.univ.filter (fun σ : Equiv.Perm ι =>
    σ.support.card = 2 ∧ matchingProduct a b (r * σ) = 0)
  let Z := Finset.univ.filter (fun ij : ι × ι => a ij.1 + b ij.2 = 0)
  have hzero (σ : Equiv.Perm ι) (hσ : σ ∈ T) : ∃ j, a (r (σ j)) + b j = 0 := by
    have hz := (Finset.mem_filter.mp hσ).2.2
    rw [matchingProduct] at hz
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hz
    exact ⟨j, hj⟩
  choose j hj using hzero
  let f (σ : Equiv.Perm ι) (hσ : σ ∈ T) : ι × ι := (r (σ (j σ hσ)), j σ hσ)
  have hfZ (σ : Equiv.Perm ι) (hσ : σ ∈ T) : f σ hσ ∈ Z := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj σ hσ⟩
  have hjmove (σ : Equiv.Perm ι) (hσ : σ ∈ T) : σ (j σ hσ) ≠ j σ hσ := by
    intro h
    have hz := hj σ hσ
    rw [h] at hz
    exact Finset.prod_ne_zero_iff.mp hr _ (Finset.mem_univ _) hz
  have hswap (σ : Equiv.Perm ι) (hσ : σ ∈ T) :
      σ = Equiv.swap (j σ hσ) (σ (j σ hσ)) := by
    obtain ⟨u, v, huv, he⟩ := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ).2.1
    let x := j σ hσ
    change σ = Equiv.swap x (σ x)
    have hx : σ x ≠ x := hjmove σ hσ
    have hap := congrArg (fun p : Equiv.Perm ι => p x) he
    change σ x = (Equiv.swap u v) x at hap
    by_cases hu : x = u
    · rw [hap, hu, Equiv.swap_apply_left]
      exact he
    by_cases hv : x = v
    · rw [hap, hv, Equiv.swap_apply_right, Equiv.swap_comm v u]
      exact he
    · exact (hx (hap.trans (Equiv.swap_apply_of_ne_of_ne hu hv))).elim
  let F : T → Z := fun σ => ⟨f σ σ.property, hfZ σ σ.property⟩
  apply Finset.card_le_card_of_injective (f := F)
  intro σ τ h
  have h1 := congrArg (fun x : Z => x.val.1) h
  have h2 := congrArg (fun x : Z => x.val.2) h
  change r (σ.val (j σ σ.property)) = r (τ.val (j τ τ.property)) at h1
  change j σ σ.property = j τ τ.property at h2
  apply Subtype.ext
  exact (hswap σ σ.property).trans
    ((congrArg₂ Equiv.swap h2 (r.injective h1)).trans (hswap τ τ.property).symm)


private theorem card_all_transpositions :
    (Finset.univ.filter (fun σ : Equiv.Perm ι => σ.support.card = 2)).card =
      (Fintype.card ι).choose 2 := by
  classical
  let f : ι × ι → Equiv.Perm ι := fun ij => Equiv.swap ij.1 ij.2
  let T := Finset.univ.filter (fun σ : Equiv.Perm ι => σ.support.card = 2)
  let E := (Finset.univ : Finset ι).offDiag
  have hE : ∀ ij : ι × ι, ij ∈ E ↔ ij.1 ≠ ij.2 := by
    intro ij
    simp [E, Finset.mem_offDiag]
  have hTE : T = E.image f := by
    ext σ
    constructor
    · intro hσ
      obtain ⟨i, j, hij, he⟩ := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ).2
      exact Finset.mem_image.mpr ⟨(i,j), (hE _).mpr hij, he.symm⟩
    · intro hσ
      obtain ⟨⟨i,j⟩, hij, rfl⟩ := Finset.mem_image.mp hσ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Equiv.Perm.card_support_swap ((hE _).mp hij)⟩
  have hpair (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
      (h : Equiv.swap i j = Equiv.swap k l) :
      (i, j) = (k, l) ∨ (i, j) = (l, k) := by
    have he' := congrArg Equiv.Perm.support h
    rw [Equiv.Perm.support_swap hij, Equiv.Perm.support_swap hkl] at he'
    have hik : i = k ∨ i = l := by
      have hi : i ∈ ({k,l} : Finset ι) := he' ▸ (by simp : i ∈ ({i,j} : Finset ι))
      simpa using hi
    have hjk : j = k ∨ j = l := by
      have hj : j ∈ ({k,l} : Finset ι) := he' ▸ (by simp : j ∈ ({i,j} : Finset ι))
      simpa using hj
    rcases hik with rfl | rfl
    · exact Or.inl (congrArg (Prod.mk i) (hjk.resolve_left hij.symm))
    · exact Or.inr (congrArg (Prod.mk i) (hjk.resolve_right hij.symm))
  have hfib (σ : Equiv.Perm ι) (hσ : σ ∈ T) :
      (E.filter fun p => f p = σ).card = 2 := by
    obtain ⟨i, j, hij, rfl⟩ := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ).2
    have he : (E.filter fun p => f p = Equiv.swap i j) = {(i,j), (j,i)} := by
      ext ⟨k,l⟩
      simp only [Finset.mem_filter, hE, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => hpair k l i j h.1 hij h.2
      · rintro (h | h)
        · cases h
          exact ⟨hij, rfl⟩
        · cases h
          exact ⟨hij.symm, Equiv.swap_comm j i⟩
    rw [he, Finset.card_pair]
    intro h
    exact hij (congrArg Prod.fst h)
  have hsplit : E.card = T.card * 2 := by
    rw [Finset.card_eq_sum_card_image f E, ← hTE]
    exact Finset.sum_const_nat hfib
  change T.card = _
  have hcardE : E.card = Fintype.card ι * Fintype.card ι - Fintype.card ι := by
    simp [E, Finset.offDiag_card]
  rw [hcardE] at hsplit
  rw [Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one, hsplit]
  omega

/-- The nonzero transposition degree is at least the full transposition
degree minus the number of zero cross-entries. -/
theorem transposition_degree_lower_bound
    (a b : ι → ℂ) (r : Equiv.Perm ι) (hr : matchingProduct a b r ≠ 0) :
    (Fintype.card ι).choose 2 ≤
      (Finset.univ.filter (fun σ : Equiv.Perm ι =>
        σ.support.card = 2 ∧ matchingProduct a b (r * σ) ≠ 0)).card +
      (Finset.univ.filter (fun ij : ι × ι => a ij.1 + b ij.2 = 0)).card := by
  classical
  let T := Finset.univ.filter (fun σ : Equiv.Perm ι => σ.support.card = 2)
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := T)
    (fun σ => matchingProduct a b (r * σ) ≠ 0)
  simp only [T, Finset.filter_filter, not_not, card_all_transpositions] at h
  have hz := card_zero_swap_neighbors_le_cross_zeros a b r hr
  omega

/-- Path 07 multiplicity bound, stated directly for an actual zero entry of
an allegedly violating pair, without a nonzero-stratum assumption. -/
theorem opposite_pair_multiplicities_add_two_lt_of_not_holds
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hbad : ¬ Holds a b U) {i j : ι} (h : a i + b j = 0) :
    (Finset.univ.filter fun k => a k = a i).card +
      (Finset.univ.filter fun k => b k = b j).card + 2 < Fintype.card ι :=
  lt_of_not_ge (fun hc => hbad (holds_of_opposite_pair_multiplicities a b U hU h hc))

end

end MOC
