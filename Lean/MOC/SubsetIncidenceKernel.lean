import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-! The unsigned incidence map between consecutive subset levels has full row rank
strictly below the middle level, over any field of characteristic zero. -/

open Finset

namespace MOC

abbrev SubsetsOfSize (α : Type*) [Fintype α] (k : ℕ) := {S : Finset α // S.card = k}

variable {α K : Type*} [Fintype α] [DecidableEq α] [Field K]

/-- Sum the upper-level coordinates over all one-element extensions. -/
def subsetIncidenceDown (k : ℕ) :
    (SubsetsOfSize α (k + 1) → K) →ₗ[K] (SubsetsOfSize α k → K) where
  toFun f S := ∑ x, if hx : x ∈ S.val then 0 else
    f ⟨insert x S.val, by rw [card_insert_of_not_mem hx, S.property]⟩
  map_add' f g := by
    ext S
    simp only [Pi.add_apply, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by split <;> simp
  map_smul' c f := by
    ext S
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_sum]
    exact sum_congr rfl fun x _ => by split <;> simp

/-- For a lower-level basis vector at R, its preimage depends only on the number
of elements of R absent from the upper-level subset. -/
private def incidenceInverseCoefficient (K : Type*) [Field K] (h : ℕ) : ℕ → K
  | 0 => (h : K)⁻¹
  | m + 1 => -((m + 1 : ℕ) : K) * incidenceInverseCoefficient K h m / (h - (m + 1) : ℕ)

private theorem incidenceDistanceSum {k : ℕ} (R S : SubsetsOfSize α k) (f : ℕ → K) :
    subsetIncidenceDown k (fun T : SubsetsOfSize α (k + 1) => f (R.val \ T.val).card) S =
      ((R.val \ S.val).card : K) * f ((R.val \ S.val).card - 1) +
      ((Fintype.card α - k - (R.val \ S.val).card : ℕ) : K) * f (R.val \ S.val).card := by
  classical
  let Q := R.val \ S.val
  have hQ : Q ⊆ S.valᶜ := fun x hx => mem_compl.mpr (mem_sdiff.mp hx).2
  have herase (x : α) : R.val \ insert x S.val = Q.erase x := by
    ext y
    simp only [Q, mem_sdiff, mem_insert, mem_erase]
    tauto
  change (∑ x, if hx : x ∈ S.val then 0 else f (R.val \ insert x S.val).card) = _
  calc
    _ = ∑ x ∈ S.valᶜ, f (R.val \ insert x S.val).card := by
      have hu : univ.filter (fun x : α => x ∈ S.valᶜ) = S.valᶜ := by ext x; simp
      rw [← hu, sum_filter]
      apply sum_congr rfl
      intro x _
      by_cases hx : x ∈ S.val <;> simp [hx]
    _ = ∑ x ∈ S.valᶜ, if x ∈ Q then f (Q.card - 1) else f Q.card := by
      apply sum_congr rfl
      intro x _
      rw [herase]
      by_cases hx : x ∈ Q
      · rw [if_pos hx, card_erase_of_mem hx]
      · rw [if_neg hx, erase_eq_of_not_mem hx]
    _ = _ := by
      rw [sum_ite]
      have hyes : S.valᶜ.filter (· ∈ Q) = Q := by
        ext x
        simp only [mem_filter]
        exact ⟨And.right, fun hx => ⟨hQ hx, hx⟩⟩
      have hno : S.valᶜ.filter (· ∉ Q) = S.valᶜ \ Q := by
        ext x
        simp only [mem_filter, mem_sdiff]
      rw [hyes, hno, sum_const, sum_const, card_sdiff hQ, card_compl, S.property]
      simp only [Q, nsmul_eq_mul]

/-- The consecutive-level incidence map is onto in the lower half of the subset lattice. -/
theorem subsetIncidenceDown_surjective [CharZero K] (k : ℕ) (hk : 2 * k < Fintype.card α) :
    Function.Surjective (subsetIncidenceDown (α := α) (K := K) k) := by
  classical
  let h := Fintype.card α - k
  have hk' : k < h := by dsimp [h]; omega
  let D := subsetIncidenceDown (α := α) (K := K) k
  have hbas (R : SubsetsOfSize α k) : Pi.single R (1 : K) ∈ LinearMap.range D := by
    refine ⟨fun T => incidenceInverseCoefficient K h (R.val \ T.val).card, ?_⟩
    funext S
    rw [show D = subsetIncidenceDown (α := α) (K := K) k from rfl, incidenceDistanceSum]
    by_cases hRS : R = S
    · subst S
      have hne : (h : K) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
      simp only [sdiff_self, card_empty, Nat.cast_zero, zero_mul, zero_add, Nat.sub_zero,
        incidenceInverseCoefficient, Pi.single_eq_same]
      exact mul_inv_cancel₀ hne
    · have hds : R.val \ S.val ≠ ∅ := by
        intro hempty
        have hle : R.val ⊆ S.val := sdiff_eq_empty_iff_subset.mp hempty
        exact hRS (Subtype.ext (eq_of_subset_of_card_le hle (by rw [R.property, S.property])))
      have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hds)
      have hsmall : (R.val \ S.val).card ≤ k :=
        (card_le_card sdiff_subset).trans R.property.le
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      have hne : ((h - (m + 1) : ℕ) : K) ≠ 0 := by
        exact_mod_cast (show h - (m + 1) ≠ 0 by omega)
      rw [hm, show Pi.single R (1 : K) S = 0 by simp [Pi.single_apply, hRS, Ne.symm hRS]]
      change ((m + 1 : ℕ) : K) * incidenceInverseCoefficient K h m +
        ((h - (m + 1) : ℕ) : K) *
          (-((m + 1 : ℕ) : K) * incidenceInverseCoefficient K h m / (h - (m + 1) : ℕ)) = 0
      field_simp
      <;> ring
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← (Pi.basisFun K (SubsetsOfSize α k)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨R, rfl⟩
  simpa only [Pi.basisFun_apply] using hbas R

/-- The dimension of the harmonic subspace on level k+1 is the difference
of the two consecutive binomial coefficients. -/
theorem finrank_subsetIncidenceDown_ker [CharZero K] (k : ℕ) (hk : 2 * k < Fintype.card α) :
    Module.finrank K (LinearMap.ker (subsetIncidenceDown (α := α) (K := K) k)) =
      (Fintype.card α).choose (k + 1) - (Fintype.card α).choose k := by
  have h := (subsetIncidenceDown (α := α) (K := K) k).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (subsetIncidenceDown_surjective k hk),
    finrank_top, Module.finrank_pi, Module.finrank_pi,
    Fintype.card_finset_len, Fintype.card_finset_len] at h
  omega

end MOC
