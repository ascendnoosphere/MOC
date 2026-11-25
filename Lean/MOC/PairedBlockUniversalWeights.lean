import MOC.UniversalMatchingWeights
import MOC.SupportBlocks

/-! Universal determinant weights combine across paired blocks and transport
across independent row and column relabelings. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Combine weights with the same permutation to obtain a universal law. -/
theorem universalMatchingWeights_of_indexed {α : Type*} [Fintype α]
    {U : Matrix ι ι ℂ} (p : α → Equiv.Perm ι) (w : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hd : ∀ a b, determinantValue a b U = ∑ i, (w i : ℂ) * matchingProduct a b (p i)) :
    HasUniversalMatchingWeights U := by
  classical
  let v (σ : Equiv.Perm ι) := ∑ i ∈ univ.filter (fun i => p i = σ), w i
  refine ⟨v, fun σ => sum_nonneg (fun i _ => hw i), ?_, ?_⟩
  · exact (sum_fiberwise univ p w).trans hs
  · intro a b
    rw [hd a b, weightedMatchingValue, ← sum_fiberwise univ p]
    apply sum_congr rfl
    intro σ _
    rw [show v σ = ∑ i ∈ univ.filter (fun i => p i = σ), w i from rfl,
      Complex.ofReal_sum, sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [(mem_filter.mp hi).2]

/-- Universal laws on the two diagonal blocks give a universal law on their
direct sum. The product weights are assigned to the block-preserving permutations. -/
theorem universal_matching_weights_directSum {U : Matrix ι ι ℂ} {V : Matrix κ κ ℂ}
    (hU : HasUniversalMatchingWeights U) (hV : HasUniversalMatchingWeights V) :
    HasUniversalMatchingWeights (fromBlocks U 0 0 V) := by
  obtain ⟨w, hw, hsw, hdw⟩ := hU
  obtain ⟨v, hv, hsv, hdv⟩ := hV
  apply universalMatchingWeights_of_indexed
    (fun p : Equiv.Perm ι × Equiv.Perm κ => Equiv.sumCongr p.1 p.2)
    (fun p => w p.1 * v p.2) (fun p => mul_nonneg (hw _) (hv _))
  · simp [Fintype.sum_prod_type, ← mul_sum, hsv, hsw]
  · intro a b
    let a₁ := a ∘ Sum.inl
    let a₂ := a ∘ Sum.inr
    let b₁ := b ∘ Sum.inl
    let b₂ := b ∘ Sum.inr
    have ha : Sum.elim a₁ a₂ = a := by funext x; cases x <;> rfl
    have hb : Sum.elim b₁ b₂ = b := by funext x; cases x <;> rfl
    have hd : determinantValue (Sum.elim a₁ a₂) (Sum.elim b₁ b₂)
        (fromBlocks U 0 0 V) = determinantValue a₁ b₁ U * determinantValue a₂ b₂ V := by
      unfold determinantValue
      rw [← Matrix.fromBlocks_diagonal, ← Matrix.fromBlocks_diagonal,
        Matrix.fromBlocks_conjTranspose]
      simp only [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.det_fromBlocks_zero₂₁,
        Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [← ha, ← hb, hd, hdw, hdv, weightedMatchingValue, weightedMatchingValue,
      Fintype.sum_prod_type, sum_mul]
    apply sum_congr rfl
    intro σ _
    rw [mul_sum]
    apply sum_congr rfl
    intro τ _
    rw [matchingProduct_sum, Complex.ofReal_mul]
    ring

private theorem pairedBlock_row_support_card {m n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (r c : Fin m → Fin n)
    (hc : Function.Injective c) (i : Fin m) :
    (supportColumns (U.submatrix r c) {i}).card ≤ (supportColumns U {r i}).card := by
  classical
  refine card_le_card_of_injOn c (fun j hj => ?_) hc.injOn
  simpa [supportColumns, submatrix_apply] using hj

/-- Proper paired blocks both inherit the row-degree bound and have smaller
order. Universal laws supplied at smaller orders give a law on the full matrix. -/
theorem universal_matching_weights_of_proper_paired_blocks {n : ℕ}
    (hbelow : ∀ m < n, ∀ V : Matrix (Fin m) (Fin m) ℂ, IsUnitary V →
      (∀ r, (supportColumns V {r}).card ≤ 3) → HasUniversalMatchingWeights V)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hrows : ∀ r, (supportColumns U {r}).card ≤ 3)
    (hblocks : HasProperPairedBlocks U) : HasUniversalMatchingWeights U := by
  obtain ⟨m, k, eRow, eCol, V, W, hm, hk, hsplit⟩ := hblocks
  obtain ⟨hm', hk'⟩ := paired_block_orders_lt eRow hm hk
  have hVeq : U.submatrix (eRow ∘ Sum.inl) (eCol ∘ Sum.inl) = V := by
    ext i j : 1
    exact congrFun (congrFun hsplit (.inl i)) (.inl j)
  have hWeq : U.submatrix (eRow ∘ Sum.inr) (eCol ∘ Sum.inr) = W := by
    ext i j : 1
    exact congrFun (congrFun hsplit (.inr i)) (.inr j)
  have hV (i : Fin m) : (supportColumns V {i}).card ≤ 3 := by
    rw [← hVeq]
    exact (pairedBlock_row_support_card U _ _ (eCol.injective.comp Sum.inl_injective) i).trans
      (hrows _)
  have hW (i : Fin k) : (supportColumns W {i}).card ≤ 3 := by
    rw [← hWeq]
    exact (pairedBlock_row_support_card U _ _ (eCol.injective.comp Sum.inr_injective) i).trans
      (hrows _)
  have hUnitary := unitary_reindex eRow eCol hU
  rw [hsplit] at hUnitary
  obtain ⟨hVU, hWU⟩ := unitary_directSum_iff.mp hUnitary
  apply (hasUniversalMatchingWeights_reindex_iff eRow eCol U).mp
  rw [hsplit]
  exact universal_matching_weights_directSum (hbelow m hm' V hVU hV) (hbelow k hk' W hWU hW)

end

end MOC
