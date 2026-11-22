import MOC.ContactCensus
import MOC.DisjointContactRectangle
import MOC.MatchingRectangleSupport
import MOC.TriangleRectangleContact
import Mathlib.Data.Fintype.Powerset

/-! An order-four gap with at least eleven regular contacts cannot
dominate a positive multiple of a relabeled mixed profile. -/

namespace MOC

private def mixedContactPatterns : Fin 6 → Finset (Fin 24) :=
  ![{3, 7, 9, 13, 20, 22}, {3, 12, 13, 17, 18, 23}, {3, 9, 10, 11, 16, 17},
    {7, 9, 18, 23}, {7, 10, 13, 16}, {10, 12, 16, 18, 20, 22}]

private theorem mixedContactPatterns_cover :
    ∀ T : ↥(referenceNonminorFacetZeroIndices.powersetCard 11),
      ∃ k : Fin 6, mixedContactPatterns k ⊆ T.val := by
  decide +kernel

private theorem height_eq_zero_of_mixedContactPattern
    (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0) (H : ℝ)
    (hinj : Function.Injective (matchingProduct a b)) (k : Fin 6)
    (hc : ∀ i ∈ mixedContactPatterns k, (η * matchingProduct a b (fourPerm i)).re = H) :
    H = 0 := by
  let P := (mixedContactPatterns k).map fourPermEquiv.toEmbedding
  have hP (σ : FourPerm) (hσ : σ ∈ P) : (η * matchingProduct a b σ).re = H := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hσ
    exact hc i hi
  have hTR (r : FourPerm) (i j m n : Fin 4)
      (hij : i ≠ j) (him : i ≠ m) (hin : i ≠ n)
      (hjm : j ≠ m) (hjn : j ≠ n) (hmn : m ≠ n)
      (hsub : ({r * Equiv.swap m n, r * Equiv.swap j m,
        r * Equiv.swap j m * Equiv.swap m n, r * Equiv.swap m n * Equiv.swap j m,
        r * Equiv.swap i j, r * Equiv.swap i j * Equiv.swap m n} : Finset FourPerm) ⊆ P) :
      H = 0 :=
    matchingProduct_triangle_rectangle_contact_height_eq_zero a b r i j m n
      hij him hin hjm hjn hmn η hη H hinj (fun σ hσ => hP σ (hsub hσ))
  have hR (r s t : FourPerm) (hst : ∀ i, s i = i ∨ t i = i) (hs : s ≠ 1) (ht : t ≠ 1)
      (hsub : ({r, r * s, r * t, r * s * t} : Finset FourPerm) ⊆ P) : H = 0 :=
    matchingProduct_disjoint_perms_contact_height_eq_zero a b r s t hst hs ht hinj η hη H
      (hP _ (hsub (by simp))) (hP _ (hsub (by simp)))
      (hP _ (hsub (by simp))) (hP _ (hsub (by simp)))
  fin_cases k
  · exact hTR (fourPerm 1) 2 0 1 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  · exact hTR (fourPerm 2) 2 3 0 1
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  · exact hTR (fourPerm 5) 1 2 0 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  · exact hR (fourPerm 7) (Equiv.swap 0 2) (Equiv.swap 1 3)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact hR (fourPerm 7) (Equiv.swap 0 3) (Equiv.swap 1 2)
      (by decide) (by decide) (by decide) (by decide +kernel)
  · exact hTR (fourPerm 14) 2 1 3 0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem matchingProduct_relabel_four (a b : Fin 4 → ℂ) (r c σ : FourPerm) :
    matchingProduct (a ∘ r) (b ∘ c.symm) σ = matchingProduct a b (r * σ * c) := by
  unfold matchingProduct
  rw [← Equiv.prod_comp c.symm (fun j => a ((r * σ * c) j) + b j)]
  simp only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Function.comp_apply]

/-- At nonzero height, at most ten labels from the reference mixed zero
set can be contacts under any independent row and column relabeling. -/
theorem four_mixed_zero_set_contact_card_le_ten
    (a b : Fin 4 → ℂ) (r c : FourPerm) (η : ℂ) (hη : η ≠ 0) (H : ℝ) (hH : H ≠ 0)
    (hinj : Function.Injective (matchingProduct a b)) (T : Finset (Fin 24))
    (hT : T ⊆ referenceNonminorFacetZeroIndices)
    (hc : ∀ i ∈ T, (η * matchingProduct a b (r * fourPerm i * c)).re = H) :
    T.card ≤ 10 := by
  by_contra! hcard
  obtain ⟨S, hST, hS⟩ := Finset.exists_subset_card_eq (s := T) (n := 11) (by omega)
  obtain ⟨k, hk⟩ := mixedContactPatterns_cover ⟨S, Finset.mem_powersetCard.mpr ⟨hST.trans hT, hS⟩⟩
  let hrel := matchingProduct_relabel_four a b r c
  have hinj' : Function.Injective (matchingProduct (a ∘ r) (b ∘ c.symm)) := by
    intro σ τ h
    exact mul_left_cancel (mul_right_cancel (hinj ((hrel σ).symm.trans (h.trans (hrel τ)))))
  refine hH (height_eq_zero_of_mixedContactPattern (a ∘ r) (b ∘ c.symm) η hη H hinj' k ?_)
  intro i hi
  rw [hrel]
  exact hc i (hST (hk hi))

private def mixedZeroHeightTriggers : Fin 3 → Finset (Fin 24) :=
  ![{3, 9, 11}, {7, 12, 13, 18}, {10, 16, 20, 22}]

private theorem mixedZeroHeightTriggers_cover :
    ∀ T : ↥(referenceNonminorFacetZeroIndices.powersetCard 11),
      ∃ k : Fin 3, mixedZeroHeightTriggers k ⊆ T.val := by
  decide +kernel

private theorem exterior_contact_of_mixedZeroHeightTrigger
    (a b : Fin 4 → ℂ) (η : ℂ) (hη : η ≠ 0)
    (hinj : Function.Injective (matchingProduct a b)) (hnz : ∀ i j, a i + b j ≠ 0)
    (k : Fin 3) (hc : ∀ i ∈ mixedZeroHeightTriggers k, (η * matchingProduct a b (fourPerm i)).re = 0) :
    ∃ i ∉ referenceNonminorFacetZeroIndices, (η * matchingProduct a b (fourPerm i)).re = 0 := by
  have hprod (σ : FourPerm) : matchingProduct a b σ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hnz (σ j) j
  fin_cases k
  · have hs : fourPerm 9 * Equiv.swap 0 3 = fourPerm 3 := by decide +kernel
    have ht : fourPerm 9 * Equiv.swap 1 2 = fourPerm 11 := by decide +kernel
    have hst : fourPerm 9 * Equiv.swap 0 3 * Equiv.swap 1 2 = fourPerm 5 := by decide +kernel
    refine ⟨5, by decide, ?_⟩
    rw [← hst]
    exact matching_disjoint_swaps_contact_of_zero_height a b η (fourPerm 9) 0 3 1 2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (mul_ne_zero hη (hprod _)) (hc 9 (by decide))
      (by rw [hs]; exact hc 3 (by decide)) (by rw [ht]; exact hc 11 (by decide))
  · have hs : fourPerm 7 * Equiv.swap 0 3 = fourPerm 13 := by decide +kernel
    have ht : fourPerm 7 * Equiv.swap 0 2 = fourPerm 18 := by decide +kernel
    have hst : fourPerm 7 * Equiv.swap 0 3 * Equiv.swap 3 2 = fourPerm 12 := by decide +kernel
    have hts : fourPerm 7 * Equiv.swap 3 2 * Equiv.swap 0 3 = fourPerm 19 := by decide +kernel
    refine ⟨19, by decide, ?_⟩
    rw [← hts]
    exact (matchingProduct_triangle_complete_zero_height a b (fourPerm 7) 0 3 2
      (by decide) (by decide) (by decide) η hη hinj hprod (hc 7 (by decide))
      (by rw [hst]; exact hc 12 (by decide)) (by rw [hs]; exact hc 13 (by decide))
      (by rw [ht]; exact hc 18 (by decide))).1
  · have hs : fourPerm 10 * Equiv.swap 0 1 = fourPerm 20 := by decide +kernel
    have ht : fourPerm 10 * Equiv.swap 0 3 = fourPerm 16 := by decide +kernel
    have hst : fourPerm 10 * Equiv.swap 0 1 * Equiv.swap 1 3 = fourPerm 22 := by decide +kernel
    have hts : fourPerm 10 * Equiv.swap 1 3 * Equiv.swap 0 1 = fourPerm 14 := by decide +kernel
    refine ⟨14, by decide, ?_⟩
    rw [← hts]
    exact (matchingProduct_triangle_complete_zero_height a b (fourPerm 10) 0 1 3
      (by decide) (by decide) (by decide) η hη hinj hprod (hc 10 (by decide))
      (by rw [hst]; exact hc 22 (by decide)) (by rw [hs]; exact hc 20 (by decide))
      (by rw [ht]; exact hc 16 (by decide))).1

/-- If every contact lies in a relabeled order-four mixed zero set, then
at most ten contacts are possible at any height under regularity. -/
theorem four_mixed_contact_card_le_ten
    (a b : Fin 4 → ℂ) (r c : FourPerm) (η : ℂ) (hη : η ≠ 0) (H : ℝ)
    (hinj : Function.Injective (matchingProduct a b)) (hnz : ∀ i j, a i + b j ≠ 0)
    (T : Finset (Fin 24)) (hc : ∀ i ∈ T, (η * matchingProduct a b (r * fourPerm i * c)).re = H)
    (hbound : ∀ i, (η * matchingProduct a b (r * fourPerm i * c)).re = H →
      i ∈ referenceNonminorFacetZeroIndices) : T.card ≤ 10 := by
  have hT : T ⊆ referenceNonminorFacetZeroIndices := fun i hi => hbound i (hc i hi)
  by_cases hH : H = 0
  · subst H
    by_contra! hcard
    obtain ⟨S, hST, hS⟩ := Finset.exists_subset_card_eq (s := T) (n := 11) (by omega)
    obtain ⟨k, hk⟩ := mixedZeroHeightTriggers_cover ⟨S, Finset.mem_powersetCard.mpr ⟨hST.trans hT, hS⟩⟩
    let hrel := matchingProduct_relabel_four a b r c
    have hinj' : Function.Injective (matchingProduct (a ∘ r) (b ∘ c.symm)) := by
      intro σ τ h
      exact mul_left_cancel (mul_right_cancel (hinj ((hrel σ).symm.trans (h.trans (hrel τ)))))
    obtain ⟨i, hnot, hnew⟩ := exterior_contact_of_mixedZeroHeightTrigger (a ∘ r) (b ∘ c.symm)
      η hη hinj' (fun i j => hnz (r i) (c.symm j)) k (fun i hi => by
        rw [hrel]; exact hc i (hST (hk hi)))
    rw [hrel] at hnew
    exact hnot (hbound i hnew)
  · exact four_mixed_zero_set_contact_card_le_ten a b r c η hη H hH hinj T hT hc

/-- A regular order-four gap dominating a positive multiple of a relabeled
mixed profile has at most ten active matching labels. -/
theorem four_contact_card_le_ten_of_mixed_profile_le
    (a b : Fin 4 → ℂ) (r c : FourPerm) (η : ℂ) (hη : η ≠ 0) (H : ℝ)
    (hinj : Function.Injective (matchingProduct a b)) (hnz : ∀ i j, a i + b j ≠ 0)
    (t : ℝ) (ht : 0 < t)
    (hgap : ∀ i : Fin 24, t * (referenceNonminorFacetTwice (fourPerm i) : ℝ) ≤
      H - (η * matchingProduct a b (r * fourPerm i * c)).re) :
    (Finset.univ.filter fun i : Fin 24 => (η * matchingProduct a b (r * fourPerm i * c)).re = H).card ≤ 10 := by
  apply four_mixed_contact_card_le_ten a b r c η hη H hinj hnz
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi
    have hnonneg : ∀ j : Fin 24, 0 ≤ referenceNonminorFacetTwice (fourPerm j) := by decide +kernel
    have hnn : (0 : ℝ) ≤ (referenceNonminorFacetTwice (fourPerm i) : ℝ) := by
      exact_mod_cast hnonneg i
    have hle := hgap i
    rw [hi, sub_self] at hle
    have hz := (mul_eq_zero.mp (le_antisymm hle (mul_nonneg ht.le hnn))).resolve_left ht.ne'
    exact (mem_referenceNonminorFacetZeroIndices i).mpr (by exact_mod_cast hz)

end MOC
