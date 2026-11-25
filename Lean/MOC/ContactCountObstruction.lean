import MOC.ContactCensus
import Mathlib.Data.Fintype.Powerset
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.NormNum

/-! Exact regular spectra with eight zero-height contacts in order four.
Their contacts admit no common proper block even though eight exceeds the
six-contact threshold. -/

open BigOperators

namespace MOC

private def leftInt : Fin 4 → GaussianInt := ![⟨1, 1⟩, 100, 283, 345]

private def rightInt : Fin 4 → GaussianInt := ![⟨1, -1⟩, 100, 60, 74]

private def matchingInt (i : Fin 24) : GaussianInt :=
  ∏ j, (leftInt (fourPerm i j) + rightInt j)

private def zeroContactsInt : Finset (Fin 24) :=
  Finset.univ.filter fun i => (matchingInt i).im = 0

private theorem entry_sum_ne_zero : ∀ i j : Fin 4, leftInt i + rightInt j ≠ 0 := by
  decide +kernel

private theorem matchingInt_injective : Function.Injective matchingInt := by
  change ∀ i j : Fin 24, matchingInt i = matchingInt j → i = j
  decide +kernel

private theorem matchingInt_im_nonneg : ∀ i : Fin 24, 0 ≤ (matchingInt i).im := by
  decide +kernel

private theorem zeroContactsInt_card : zeroContactsInt.card = 8 := by
  decide +kernel

private theorem zeroContactsInt_no_partition (s : Finset (Fin 4))
    (h : ∀ i : Fin 24, (matchingInt i).im = 0 → s.map (fourPerm i).toEmbedding = s) :
    s = ∅ ∨ s = Finset.univ := by
  have hdec : ∀ s : Finset (Fin 4),
      (∀ i : Fin 24, (matchingInt i).im = 0 → s.map (fourPerm i).toEmbedding = s) →
        s = ∅ ∨ s = Finset.univ := by decide +kernel
  exact hdec s h

/-- The eight maximizing matchings at these regular order-four spectra
have no common nontrivial block. The identity itself is a contact, so any
common setwise assignment would have to fix its block. -/
theorem exists_eight_regular_contacts_without_common_block :
    ∃ (a b : Fin 4 → ℂ) (T : Finset FourPerm),
      (∀ i j, a i + b j ≠ 0) ∧ Function.Injective (matchingProduct a b) ∧
      (∀ σ, (Complex.I * matchingProduct a b σ).re ≤ 0) ∧
      (∀ σ, σ ∈ T ↔ (Complex.I * matchingProduct a b σ).re = 0) ∧
      T.card = 8 ∧
      (∀ s : Finset (Fin 4), (∀ σ ∈ T, s.map σ.toEmbedding = s) →
        s = ∅ ∨ s = Finset.univ) := by
  let a := GaussianInt.toComplex ∘ leftInt
  let b := GaussianInt.toComplex ∘ rightInt
  let T := zeroContactsInt.map fourPermEquiv.toEmbedding
  have hmap (i : Fin 24) :
      GaussianInt.toComplex (matchingInt i) = matchingProduct a b (fourPerm i) := by
    simp only [matchingInt, matchingProduct, a, b, map_prod, map_add, Function.comp_apply]
  have hproj (i : Fin 24) :
      (Complex.I * matchingProduct a b (fourPerm i)).re = -((matchingInt i).im : ℝ) := by
    rw [← hmap, Complex.I_mul_re, GaussianInt.to_real_im]
  have hmem (i : Fin 24) : fourPerm i ∈ T ↔ (matchingInt i).im = 0 := by
    change fourPermEquiv i ∈ zeroContactsInt.map fourPermEquiv.toEmbedding ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨j, hj, he⟩
      have hji : j = i := fourPermEquiv.injective he
      subst j
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  refine ⟨a, b, T, ?_, ?_, ?_, ?_, by simpa only [T, Finset.card_map] using zeroContactsInt_card, ?_⟩
  · intro i j h
    apply entry_sum_ne_zero i j
    exact GaussianInt.toComplex_injective (by
      simpa only [map_add, map_zero, a, b, Function.comp_apply] using h)
  · intro σ τ h
    obtain ⟨i, rfl⟩ := fourPerm_surjective σ
    obtain ⟨j, rfl⟩ := fourPerm_surjective τ
    rw [← hmap i, ← hmap j] at h
    exact congrArg fourPerm (matchingInt_injective (GaussianInt.toComplex_injective h))
  · intro σ
    obtain ⟨i, rfl⟩ := fourPerm_surjective σ
    rw [hproj, neg_nonpos]
    exact_mod_cast matchingInt_im_nonneg i
  · intro σ
    obtain ⟨i, rfl⟩ := fourPerm_surjective σ
    rw [hmem, hproj, neg_eq_zero]
    exact_mod_cast (Iff.rfl : (matchingInt i).im = 0 ↔ (matchingInt i).im = 0)
  · intro s hs
    apply zeroContactsInt_no_partition s
    intro i hi
    exact hs (fourPerm i) ((hmem i).mpr hi)

end MOC
