import MOC.Reformulations.Common
import MOC.Hermitian
import MOC.Singular
import MOC.Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Native positive-spectrum and invertible-representative restrictions

The positive-spectrum assertions here apply to actual finite real spectra,
not arbitrary labelled complex evaluations. They give the common finite determinant/log-determinant
calculation used by the positive operator versions of the atlas. Nothing here
identifies the native log, entropy, valuation or tropical limit with the complex
MOC, and nothing about infinite-dimensional limits is asserted. The final theorem
is a separate exact comparison for complex invertible representatives.
-/

open BigOperators Matrix

namespace MOC.Reformulations

noncomputable section

private theorem matchingProduct_ofReal_re {n : ℕ} (a b : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    (matchingProduct (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) σ).re =
      ∏ j, (a (σ j) + b j) := by
  unfold matchingProduct
  simp only [← Complex.ofReal_add, ← Complex.ofReal_prod, Complex.ofReal_re]

/-- Native finite log-determinant bounds for positive spectra. The extrema can
be witnessed by individual matching labels. The real part of the determinant
is strictly positive, so the logarithm evaluated here is well-defined. -/
theorem positiveRealSpectra_log_bounds {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    let d := (determinantValue (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) U).re
    0 < d ∧ ∃ lo hi : Equiv.Perm (Fin n),
      (∑ j, Real.log (a (lo j) + b j)) ≤ Real.log d ∧
      Real.log d ≤ ∑ j, Real.log (a (hi j) + b j) := by
  dsimp only
  have hv := holds_of_real_spectra a b U hU
  have hd := (holds_iff_directional _ _ _).mp hv
  obtain ⟨lo, hlo⟩ := hd (-1)
  obtain ⟨hi, hhi⟩ := hd 1
  simp only [neg_one_mul, Complex.neg_re, neg_le_neg_iff, matchingProduct_ofReal_re] at hlo
  simp only [one_mul, matchingProduct_ofReal_re] at hhi
  have hp (σ : Equiv.Perm (Fin n)) : 0 < ∏ j, (a (σ j) + b j) :=
    Finset.prod_pos fun j _ => add_pos (ha (σ j)) (hb j)
  have hpos := (hp lo).trans_le hlo
  refine ⟨hpos, lo, hi, ?_, ?_⟩
  · rw [← Real.log_prod _ _ (fun j _ => (add_pos (ha (lo j)) (hb j)).ne')]
    exact Real.log_le_log (hp lo) hlo
  · rw [← Real.log_prod _ _ (fun j _ => (add_pos (ha (hi j)) (hb j)).ne')]
    exact Real.log_le_log hpos hhi

/-- E.g. Atlas 166 and 192, where the native finite spectral values are
positive exponentials of finite, real data. This is before any limiting or
phase-sensitive comparison. -/
theorem exponentialSpectra_log_bounds {n : ℕ} (a b : Fin n → ℝ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    let d := (determinantValue (fun i => (Real.exp (a i) : ℂ))
      (fun i => (Real.exp (b i) : ℂ)) U).re
    0 < d ∧ ∃ lo hi : Equiv.Perm (Fin n),
      (∑ j, Real.log (Real.exp (a (lo j)) + Real.exp (b j))) ≤ Real.log d ∧
      Real.log d ≤ ∑ j, Real.log (Real.exp (a (hi j)) + Real.exp (b j)) :=
  positiveRealSpectra_log_bounds (fun i => Real.exp (a i)) (fun i => Real.exp (b i))
    (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _) U hU

/-- Atlas 213: the actual unevaluated mixture of density spectra. The proof is
stronger than needed for the native determinant statement: it uses only reality
of the weights and spectra, not nonnegativity or a trace-one condition. -/
theorem densityMixtureHolds {n : ℕ} (p q : Fin n → ℝ) (t : ℝ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds (fun j => ((t * p j : ℝ) : ℂ)) (fun j => (((1 - t) * q j : ℝ) : ℂ)) U :=
  holds_of_real_spectra _ _ U hU

/-- Atlas 218: native spectral form for a real regularized kernel determinant.
Nonnegativity is not needed for hull membership. It is needed for the native
positive logarithm interpretation. -/
theorem regularizedRealKernelHolds {n : ℕ} (a b : Fin n → ℝ) (α : ℝ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    Holds (fun j => ((1 + a j / α : ℝ) : ℂ)) (fun j => ((b j / α : ℝ) : ℂ)) U :=
  holds_of_real_spectra _ _ U hU

/-- Finite representative comparison in Atlas 224. This is not a determinant of
the abstract sum of two K-theory classes. -/
def InvertibleRepresentativeForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    (∀ i, a i ≠ 0) → (∀ j, b j ≠ 0) →
    determinantValue a b U ≠ 0 → Holds a b U

theorem invertibleRepresentativeForm_iff : InvertibleRepresentativeForm ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    by_cases hz : determinantValue a b U = 0
    · exact holds_of_singular a b hU hz
    · have hf : (Set.range (fun i => -a i) ∪ Set.range b).Finite :=
        (Set.finite_range _).union (Set.finite_range _)
      obtain ⟨t, _, ht⟩ := Set.infinite_univ.exists_not_mem_finite hf
      have ha : ∀ i, a i + t ≠ 0 := by
        intro i hi
        exact ht (Or.inl ⟨i, (eq_neg_of_add_eq_zero_right hi).symm⟩)
      have hb : ∀ j, b j - t ≠ 0 := by
        intro j hj
        exact ht (Or.inr ⟨j, sub_eq_zero.mp hj⟩)
      have hc : determinantValue (fun i => a i + t) (fun i => b i - t) U ≠ 0 := by
        rwa [determinantValue_shift a b hU t]
      exact (holds_shift_iff a b hU t).mp (h n _ _ U hU ha hb hc)
  · intro h n a b U hU _ _ _
    exact h n a b U hU

end

end MOC.Reformulations
