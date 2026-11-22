import MOC.TwoValues
import Mathlib.Tactic.FinCases

/-! A common subset-image law transfers to determinants, and complementary
minors reduce the number of identities the law needs to verify. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

/-- A subset-image law gives the same weights in the determinant expansion. -/
theorem determinantValue_eq_sum_of_indexed_minor_law
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (p : κ → Equiv.Perm ι) (w : κ → ℝ)
    (hm : ∀ I J : Finset ι, subsetMinorSq U I J =
      ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k) :
    (∑ k, (w k : ℂ) * matchingProduct a b (p k)) = determinantValue a b U := by
  classical
  rw [determinantValue_eq_sum_subsetMinors a b U hU]
  simp_rw [matchingProduct_expand_subsets, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [← Finset.sum_fiberwise univ (fun k => J.map (p k).toEmbedding)]
  apply Finset.sum_congr rfl
  intro I _
  rw [hm, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [(Finset.mem_filter.mp hk).2]

/-- A single probability law giving every subset-image marginal proves the
determinant inclusion for all spectral labels. -/
theorem holds_of_indexed_minor_law
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (p : κ → Equiv.Perm ι) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hm : ∀ I J : Finset ι, subsetMinorSq U I J =
      ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k) :
    Holds a b U := by
  classical
  unfold Holds
  refine mem_convexHull_of_exists_fintype w (fun k => matchingProduct a b (p k)) hw hs
    (fun k => ⟨p k, rfl⟩) ?_
  simpa only [Complex.real_smul] using
    determinantValue_eq_sum_of_indexed_minor_law a b U hU p w hm

private theorem map_compl_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (p : Equiv.Perm ι) :
    Jᶜ.map p.toEmbedding = (J.map p.toEmbedding)ᶜ := by
  ext j
  simp [Finset.mem_map_equiv]

/-- Complementary minors of a unitary have the same squared norm. -/
theorem subsetMinorSq_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (I J : Finset ι) :
    subsetMinorSq U Iᶜ Jᶜ = subsetMinorSq U I J := by
  apply Complex.ofReal_injective
  simp_rw [← sum_signedWeight_image_eq_subsetMinorSq U hU, map_compl_perm, compl_inj_iff]

private theorem pairIndexEquiv {ι : Type*} [DecidableEq ι] (x y : ι) (hxy : x ≠ y) :
    ∃ e : Fin 2 ≃ ({x,y} : Finset ι), (e 0).val = x ∧ (e 1).val = y := by
  let f : Fin 2 → ({x,y} : Finset ι) :=
    ![⟨x, Finset.mem_insert_self _ _⟩, ⟨y, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have he := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp [f, hxy, hxy.symm] at he ⊢
    · rintro ⟨z, hz⟩
      rcases Finset.mem_insert.mp hz with h | h
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext (Finset.mem_singleton.mp h).symm⟩
  exact ⟨Equiv.ofBijective f hf, rfl, rfl⟩

theorem subsetMinorSq_singleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (i j : ι) :
    subsetMinorSq U {i} {j} = Complex.normSq (U i j) := by
  let e : Fin 1 ≃ ({i} : Finset ι) := Fintype.equivOfCardEq (by simp)
  let f : Fin 1 ≃ ({j} : Finset ι) := Fintype.equivOfCardEq (by simp)
  have hi : (e 0).val = i := Finset.mem_singleton.mp (e 0).property
  have hj : (f 0).val = j := Finset.mem_singleton.mp (f 0).property
  rw [subsetMinorSq_eq_normSq_det_submatrix _ hU _ _ e f, Matrix.det_fin_one]
  simp only [Matrix.submatrix_apply, Function.comp_apply, hi, hj]

theorem subsetMinorSq_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) {i k j l : ι} (hik : i ≠ k) (hjl : j ≠ l) :
    subsetMinorSq U {i,k} {j,l} = Complex.normSq (U i j * U k l - U i l * U k j) := by
  obtain ⟨e,e₀,e₁⟩ := pairIndexEquiv i k hik
  obtain ⟨f,f₀,f₁⟩ := pairIndexEquiv j l hjl
  rw [subsetMinorSq_eq_normSq_det_submatrix _ hU _ _ e f, Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Function.comp_apply, e₀,e₁,f₀,f₁]

/-- It suffices to check equal-cardinality minors of size at most half the
matrix order. The same indexed law then gives every squared minor. -/
theorem indexed_minor_law_of_small {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (p : κ → Equiv.Perm ι) (w : κ → ℝ)
    (hm : ∀ I J : Finset ι, I.card = J.card → I.card ≤ Fintype.card ι / 2 →
      subsetMinorSq U I J = ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k) :
    ∀ I J : Finset ι, subsetMinorSq U I J =
      ∑ k ∈ univ.filter (fun k => J.map (p k).toEmbedding = I), w k := by
  intro I J
  by_cases hc : I.card = J.card
  · by_cases hs : I.card ≤ Fintype.card ι / 2
    · exact hm I J hc hs
    have hcc : Iᶜ.card = Jᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hc]
    have hsc : Iᶜ.card ≤ Fintype.card ι / 2 := by
      rw [Finset.card_compl]
      omega
    simpa only [subsetMinorSq_compl _ hU, map_compl_perm, compl_inj_iff] using
      hm Iᶜ Jᶜ hcc hsc
  · have hout : (univ.filter (fun k => J.map (p k).toEmbedding = I)) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro k _ he
      exact hc (by rw [← he, Finset.card_map])
    simp [subsetMinorSq, hc, hout]

end

end MOC
