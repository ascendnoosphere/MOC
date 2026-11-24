import MOC.Reformulations.Common
import MOC.FiniteMinorLaw
import MOC.StrongSupport

open BigOperators Matrix
open scoped Finset

namespace MOC.Reformulations

noncomputable section

/-- Evaluate a squared-minor table against one pair of spectra. Terms with
unequal subset sizes vanish. -/
def compoundValue {n : ℕ} (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ J : Finset (Fin n), ∑ I : Finset (Fin n), (subsetMinorSq U I J : ℂ) *
    ((∏ i ∈ Iᶜ, a i) * ∏ j ∈ J, b j)

theorem compoundValue_permMatrix {n : ℕ} (a b : Fin n → ℂ) (p : Equiv.Perm (Fin n)) :
    compoundValue a b (p.permMatrix ℂ) = matchingProduct a b p.symm := by
  unfold compoundValue
  rw [← determinantValue_eq_sum_subsetMinors a b _ (isUnitary_permMatrix p),
    determinantValue, permMatrix_conjugates, Matrix.submatrix_diagonal_equiv,
    Matrix.diagonal_add, Matrix.det_diagonal, matchingProduct_inverse]
  rfl

/-- C★ 9: a scalar projection, not containment of full minor tables. -/
def CompoundForm : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    compoundValue a b U ∈ convexHull ℝ
      (Set.range (fun p : Equiv.Perm (Fin n) => compoundValue a b (p.permMatrix ℂ)))

theorem compoundForm_iff : CompoundForm ↔ MOCIsTrue := by
  have hr (n : ℕ) (a b : Fin n → ℂ) :
      Set.range (fun p : Equiv.Perm (Fin n) => compoundValue a b (p.permMatrix ℂ)) =
        Set.range (matchingProduct a b) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.symm, (compoundValue_permMatrix a b p).symm⟩
    · rintro ⟨p, rfl⟩
      refine ⟨p.symm, ?_⟩
      change compoundValue a b (Equiv.Perm.permMatrix ℂ p.symm) = matchingProduct a b p
      rw [compoundValue_permMatrix, Equiv.symm_symm]
  constructor
  · intro h n a b U hU
    have g := h n a b U hU
    rw [hr, compoundValue, ← determinantValue_eq_sum_subsetMinors a b U hU] at g
    exact g
  · intro h n a b U hU
    rw [hr, compoundValue, ← determinantValue_eq_sum_subsetMinors a b U hU]
    exact h n a b U hU

/-- Original C★ 10, with permutations oriented from rows to columns.
One weight vector must work for the whole minor table. -/
def StrongCompoundForm : Prop :=
  ∀ (n : ℕ) (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p) = 1 ∧
      ∀ I J : Finset (Fin n),
        (∑ p, w p * (if I.map p.toEmbedding = J then 1 else 0)) =
          subsetMinorSq U I J

private theorem columnRow_map_iff {n : ℕ} (I J : Finset (Fin n))
    (p : Equiv.Perm (Fin n)) : J.map p.symm.toEmbedding = I ↔ I.map p.toEmbedding = J := by
  constructor
  · intro h
    rw [← h]
    ext k
    simp [Finset.mem_map_equiv]
  · intro h
    rw [← h]
    ext k
    simp [Finset.mem_map_equiv]

theorem moc_of_strongCompoundForm (h : StrongCompoundForm) : MOCIsTrue := by
  classical
  intro n a b U hU
  obtain ⟨w, hw, hs, hm⟩ := h n U hU
  apply holds_of_indexed_minor_law a b U hU (fun p : Equiv.Perm (Fin n) => p.symm) w hw hs
  intro I J
  rw [← hm I J, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  simp only [columnRow_map_iff]
  split_ifs <;> simp_all


end

end MOC.Reformulations
