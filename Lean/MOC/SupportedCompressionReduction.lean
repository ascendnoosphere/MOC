import MOC.Normal
import MOC.NormalCompressionDensity
import MOC.NormalCompressionReduction
import MOC.SupportedCompressionInterlacing

/-! A normal compression can reduce the determinant problem by one order
while keeping all untouched labels in the matching vertices. -/

open BigOperators Matrix

namespace MOC

noncomputable section

/-- The matching hull for a normal principal compression lies inside the
rectangular matching hull of its original spectrum. Untouched labels may repeat. -/
theorem exists_compression_spectrum_with_matchingHull_subset {n : ℕ}
    (a : Fin n → ℂ) (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (hβ : Set.InjOn β {j | U p j ≠ 0})
    (hC : IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    ∃ b : Fin n → ℂ,
      ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).charpoly.roots =
        (Finset.univ : Finset (Fin n)).val.map b ∧
      convexHull ℝ (Set.range (matchingProduct a b)) ⊆
        convexHull ℝ (Set.range (rectangularMatchingProduct a β)) := by
  classical
  let S := Finset.univ.filter (fun j => U p j ≠ 0)
  let c := (U * diagonal β * Uᴴ) p p
  let C := (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove
  obtain ⟨r, E, d, lam, δ, hE, hd, _, hparam, hδ, hroots⟩ :=
    exists_interlaced_spectral_roots_of_normalCompression β U hU p hβ hC
  let T := (Finset.univ : Finset (Fin (n + 1))) \ S
  let K := ↥T ⊕ Fin r
  have hE' : Finset.univ.map E = S := hE
  have hS : S.card = r + 1 := by
    rw [← hE', Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hT : T.card + S.card = n + 1 := by
    simpa only [T, Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have hcard : Fintype.card K = Fintype.card (Fin n) := by
    simp only [K, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
    omega
  let e : K ≃ Fin n := Fintype.equivOfCardEq hcard
  let g : K → ℂ := Sum.elim (β ∘ Subtype.val) (fun j => c + d * (δ j : ℂ))
  let b : Fin n → ℂ := g ∘ e.symm
  have hTmap : (Finset.univ : Finset ↥T).val.map (β ∘ Subtype.val) = T.val.map β := by
    rw [Finset.univ_eq_attach, Finset.attach_val, ← Multiset.map_map, Multiset.attach_map_val]
  have hroots' : C.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b := by
    have hmap : (Finset.univ : Finset (Fin n)).val.map b = (Finset.univ : Finset K).val.map g := by
      dsimp only [b]
      rw [← Multiset.map_map, Multiset.map_univ_val_equiv e.symm]
    rw [hmap]
    change C.charpoly.roots = (Finset.univ : Finset (↥T ⊕ Fin r)).val.map g
    rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_disjSum]
    change C.charpoly.roots = (Finset.univ : Finset ↥T).val.map (β ∘ Subtype.val) +
      (Finset.univ : Finset (Fin r)).val.map (fun i => c + d * (δ i : ℂ))
    rw [hTmap]
    exact hroots
  refine ⟨b, hroots', convexHull_min ?_ (convex_convexHull ℝ _)⟩
  rintro _ ⟨σ, rfl⟩
  let aK (k : K) := a (σ (e k))
  let m : ℂ := ∏ j : ↥T, (aK (Sum.inl j) + β j.val)
  let L : ℂ →ₗ[ℝ] ℂ := LinearMap.mulLeft ℝ m
  have hv : matchingProduct a b σ = L (∏ j : Fin r, (aK (Sum.inr j) + (c + d * (δ j : ℂ)))) := by
    unfold matchingProduct
    rw [← Equiv.prod_comp e (fun i => a (σ i) + b i)]
    simp only [b, Function.comp_apply, Equiv.symm_apply_apply]
    change (∏ k : ↥T ⊕ Fin r, (aK k + g k)) = _
    rw [Fintype.prod_sum_type] <;> rfl
  rw [hv]
  apply convexHull_min _ ((convex_convexHull ℝ _).linear_preimage L)
    (affine_interlacing_prod_mem_rectangular_hull (fun j => aK (Sum.inr j)) lam δ
      (fun i => (hδ i).1.le) (fun i => (hδ i).2.le) c d hd)
  rintro _ ⟨s, rfl⟩
  change m * (∏ j, (aK (Sum.inr j) + (c + d * (lam (s j) : ℂ)))) ∈
    convexHull ℝ (Set.range (rectangularMatchingProduct a β))
  have hpar (j : Fin (r + 1)) : β (E j) = c + d * (lam j : ℂ) := hparam j
  simp_rw [← hpar]
  have hE_mem (j : Fin (r + 1)) : E j ∈ S := by
    rw [← hE']
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let f : K ↪ Fin (n + 1) := ⟨Sum.elim Subtype.val (fun i => E (s i)), by
    rintro (x | i) (y | j) he
    · exact congrArg Sum.inl (Subtype.ext he)
    · exfalso
      apply (Finset.mem_sdiff.mp x.property).2
      change x.val = E (s j) at he
      rw [he]
      exact hE_mem _
    · exfalso
      apply (Finset.mem_sdiff.mp y.property).2
      change E (s i) = y.val at he
      rw [← he]
      exact hE_mem _
    · exact congrArg Sum.inr (s.injective (E.injective he))⟩
  let F := (σ.symm.trans e.symm).toEmbedding.trans f
  have hF (k : K) : F (σ (e k)) = f k := by
    simp [F]
  apply subset_convexHull ℝ _
  refine ⟨F, ?_⟩
  unfold rectangularMatchingProduct
  rw [← Equiv.prod_comp (e.trans σ) (fun i => a i + β (F i))]
  simp only [Equiv.trans_apply, hF]
  change (∏ k : ↥T ⊕ Fin r, (aK k + β (f k))) = _
  rw [Fintype.prod_sum_type] <;> rfl

/-- The smaller-order conjecture covers a normal principal compression whose
deleted row meets distinct spectral labels. -/
theorem holds_normal_compression_of_injOn_support {n : ℕ} (hSmall : Conjecture (Fin n))
    (a : Fin n → ℂ) (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (hβ : Set.InjOn β {j | U p j ≠ 0})
    (hC : IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    (diagonal a + (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).det ∈
      convexHull ℝ (Set.range (rectangularMatchingProduct a β)) := by
  obtain ⟨b, hb, hsub⟩ := exists_compression_spectrum_with_matchingHull_subset a β U hU p hβ hC
  have hA : IsStarNormal (diagonal a) := by
    constructor
    change (diagonal a)ᴴ * diagonal a = diagonal a * (diagonal a)ᴴ
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun j => mul_comm _ _)
  have hAroots : (diagonal a).charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a := by
    simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one] using
      (roots_unitary_diagonalization a (U := 1) isUnitary_one)
  exact hsub (conjecture_iff_normalConjecture.mp hSmall _ _ a b hA hC hAroots hb)

/-- The smaller-order conjecture covers every normal principal compression. -/
theorem holds_normal_compression {n : ℕ} (hSmall : Conjecture (Fin n))
    (a : Fin n → ℂ) (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (hC : IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    (diagonal a + (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove).det ∈
      convexHull ℝ (Set.range (rectangularMatchingProduct a β)) :=
  holds_normal_compression_of_distinct_support_test a U hU p
    (fun b hb hbC => holds_normal_compression_of_injOn_support hSmall a b U hU p hb hbC) β hC

/-- A normal compression at a regular spectral pole suffices to reduce the
determinant inclusion to the conjecture in the smaller order. -/
theorem holds_of_normal_poleCompression {n : ℕ} (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : IsUnitary U) (p : Fin (n + 1)) (ha : ∀ k ≠ p, a k - a p ≠ 0)
    (hb : ∀ j, b j + a p ≠ 0)
    (hC : IsStarNormal (poleCompression a b U p)) : Holds a b U := by
  let α : Fin n → ℂ := fun k => (a (p.succAbove k) - a p)⁻¹
  let β : Fin (n + 1) → ℂ := fun j => (b j + a p)⁻¹
  have h := holds_normal_compression hSmall α β U hU p hC
  rw [← rectangular_matching_range α β p] at h
  apply (holds_iff_poleCompression a b U hU p ha hb).mpr
  simpa only [α, β, poleCompression, poleMatchingProduct] using h

end

end MOC
