import MOC.SparseRow
import MOC.UniversalMatchingWeights

/-! Universal permutation weights propagated through sparse-row deletion. -/

open BigOperators Matrix

namespace MOC

/-- Mix the universal laws of the normalized minors using the squared pivot magnitudes. -/
theorem hasUniversalMatchingWeights_of_two_supported_row_of_minors {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : IsUnitary U)
    (i j k : Fin (n + 1)) (hzero : ∀ l, l ≠ j → l ≠ k → U i l = 0)
    (hSmall : ∀ p, U i p ≠ 0 → IsUnitary (normalizedSparseRowMinor U i p (if p = j then k else j)) →
      HasUniversalMatchingWeights (normalizedSparseRowMinor U i p (if p = j then k else j))) :
    HasUniversalMatchingWeights U := by
  classical
  let S := Finset.univ.filter (fun p => U i p ≠ 0)
  let V (p : Fin (n + 1)) := normalizedSparseRowMinor U i p (if p = j then k else j)
  have hMinor (p : Fin (n + 1)) (hp : p ∈ S) : HasUniversalMatchingWeights (V p) := by
    have hnz := (Finset.mem_filter.mp hp).2
    exact hSmall p hnz (unitary_normalizedSparseRowMinor_at_pivot hU i j k p hzero hnz)
  choose w hw using fun p : S => hMinor p p.property
  let weight (τ : Equiv.Perm (Fin (n + 1))) : ℝ :=
    ∑ p ∈ S.attach, ∑ σ,
      if extendSparseRowMatching i p.val σ = τ then Complex.normSq (U i p.val) * w p σ else 0
  refine ⟨weight, ?_, ?_, ?_⟩
  · intro τ
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro σ _
    exact ite_nonneg (mul_nonneg (Complex.normSq_nonneg _) ((hw p).1 σ)) le_rfl
  · unfold weight
    rw [Finset.sum_comm]
    calc
      _ = ∑ p ∈ S.attach, Complex.normSq (U i p.val) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum,
          (hw p).2.1, mul_one]
      _ = 1 := by
        exact (Finset.sum_attach S (fun p => Complex.normSq (U i p))).trans
          (sum_normSq_sparseRow_pivots hU i)
  · intro a b
    rw [determinantValue_two_supported_row a b hU i j k hzero]
    change (∑ p ∈ S, Complex.normSq (U i p) •
      ((a i + b p) * determinantValue (a ∘ i.succAbove) (b ∘ p.succAbove) (V p))) = _
    rw [← Finset.sum_attach]
    simp only [weightedMatchingValue, weight, Complex.ofReal_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [(hw p).2.2]
    simp only [weightedMatchingValue, Finset.mul_sum, Complex.real_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, matchingProduct_extendSparseRowMatching,
      Complex.ofReal_mul, Complex.real_smul]
    ring

/-- Reduce at a row of degree at most two, using the universal law for each nonzero-pivot minor. -/
theorem hasUniversalMatchingWeights_of_row_degree_le_two_of_minors {n : ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hU : IsUnitary U)
    (i : Fin (n + 1)) (hc : (supportColumns U {i}).card ≤ 2)
    (hSmall : ∀ p q, U i p ≠ 0 → IsUnitary (normalizedSparseRowMinor U i p q) →
      HasUniversalMatchingWeights (normalizedSparseRowMinor U i p q)) :
    HasUniversalMatchingWeights U := by
  obtain ⟨j, k, hjk⟩ := exists_row_support_pair i hc
  exact hasUniversalMatchingWeights_of_two_supported_row_of_minors hU i j k hjk
    (fun p hp hV => hSmall p _ hp hV)

end MOC
