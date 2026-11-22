import MOC.Obstruction
import MOC.TwoValues

/-! The three retained columns of a four-dimensional rotation cannot share
a positive, spectra-independent law for all compressed minor coefficients. -/

open BigOperators Matrix

namespace MOC

private theorem map_complement_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (σ : Equiv.Perm ι) : Sᶜ.map σ.toEmbedding = (S.map σ.toEmbedding)ᶜ := by
  ext i
  simp [Finset.mem_map_equiv]

private theorem subsetMinorSq_compl_fourRotation (I J : Finset (Fin 4)) :
    subsetMinorSq fourRotation Iᶜ Jᶜ = subsetMinorSq fourRotation I J := by
  classical
  have hfilter : (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) => Jᶜ.map σ.toEmbedding = Iᶜ) =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I) := by
    ext σ
    simp [map_complement_eq]
  apply Complex.ofReal_injective
  rw [← sum_signedWeight_image_eq_subsetMinorSq _ fourRotation_unitary Iᶜ Jᶜ,
    ← sum_signedWeight_image_eq_subsetMinorSq _ fourRotation_unitary I J, hfilter]

private theorem singleton_minor_fourRotation (i j : Fin 4) :
    subsetMinorSq fourRotation {i} {j} = Complex.normSq (fourRotation i j) := by
  let e : Fin 1 ≃ ({i} : Finset (Fin 4)) := Fintype.equivOfCardEq (by simp)
  let f : Fin 1 ≃ ({j} : Finset (Fin 4)) := Fintype.equivOfCardEq (by simp)
  rw [subsetMinorSq_eq_normSq_det_submatrix _ fourRotation_unitary _ _ e f, Matrix.det_fin_one]
  have hi : (e 0).val = i := Finset.mem_singleton.mp (e 0).property
  have hj : (f 0).val = j := Finset.mem_singleton.mp (f 0).property
  simpa only [Matrix.submatrix_apply, Function.comp_apply, hi, hj]

private theorem pair_equiv {i j : Fin 4} (hij : i ≠ j) :
    ∃ e : Fin 2 ≃ ({i, j} : Finset (Fin 4)), (e 0).val = i ∧ (e 1).val = j := by
  let f : Fin 2 → ({i, j} : Finset (Fin 4)) :=
    ![⟨i, Finset.mem_insert_self _ _⟩, ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hval := congrArg Subtype.val hab
      fin_cases a <;> fin_cases b <;> simp [f, hij, hij.symm] at hval ⊢
    · rintro ⟨k, hk⟩
      rcases Finset.mem_insert.mp hk with h | h
      · subst k
        exact ⟨0, Subtype.ext rfl⟩
      · have hkj := Finset.mem_singleton.mp h
        subst k
        exact ⟨1, Subtype.ext rfl⟩
  exact ⟨Equiv.ofBijective f hf, rfl, rfl⟩

private theorem pair_minor_fourRotation {i k j l : Fin 4} (hi : i ≠ k) (hj : j ≠ l) :
    subsetMinorSq fourRotation {i, k} {j, l} = minorSq fourRotation i k j l := by
  obtain ⟨e, e₀, e₁⟩ := pair_equiv hi
  obtain ⟨f, f₀, f₁⟩ := pair_equiv hj
  rw [subsetMinorSq_eq_normSq_det_submatrix _ fourRotation_unitary _ _ e f, Matrix.det_fin_two]
  simp only [minorSq, Matrix.submatrix_apply, Function.comp_apply, e₀, e₁, f₀, f₁]

private theorem map_pair_eq (σ : Equiv.Perm (Fin 4)) {i k j l : Fin 4} (hi : i ≠ k) :
    ({i, k} : Finset (Fin 4)).map σ.toEmbedding = {j, l} ↔
      (σ i = j ∧ σ k = l) ∨ (σ i = l ∧ σ k = j) := by
  rw [Finset.map_insert, Finset.map_singleton]
  constructor
  · intro h
    have h₀ : σ i ∈ ({j, l} : Finset (Fin 4)) := by
      rw [← h]
      exact Finset.mem_insert_self _ _
    have h₁ : σ k ∈ ({j, l} : Finset (Fin 4)) := by
      rw [← h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h₀ h₁
    rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁
    · exact False.elim (hi (σ.injective (h₀.trans h₁.symm)))
    · exact Or.inl ⟨h₀, h₁⟩
    · exact Or.inr ⟨h₀, h₁⟩
    · exact False.elim (hi (σ.injective (h₀.trans h₁.symm)))
  · rintro (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩) <;>
      simp [Equiv.toEmbedding_apply, h₀, h₁, Finset.pair_comm]

private noncomputable def imageMass (w : Equiv.Perm (Fin 4) → ℝ) (I J : Finset (Fin 4)) : ℝ :=
  ∑ σ, w σ * (if I.map σ.toEmbedding = J then 1 else 0)

private theorem imageMass_compl (w : Equiv.Perm (Fin 4) → ℝ) (I J : Finset (Fin 4)) :
    imageMass w Iᶜ Jᶜ = imageMass w I J := by
  classical
  simp only [imageMass, map_complement_eq, compl_inj_iff]

private theorem fourRotation_imageMass_contradiction (w : Equiv.Perm (Fin 4) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ)
    (h₀ : imageMass w {1} {0} = subsetMinorSq fourRotation {1} {0})
    (h₁ : imageMass w {3} {2} = subsetMinorSq fourRotation {3} {2})
    (h₂ : imageMass w {2,3} {0,3} = subsetMinorSq fourRotation {2,3} {0,3})
    (h₃ : imageMass w {1,2} {0,1} = subsetMinorSq fourRotation {1,2} {0,1}) : False := by
  classical
  simp only [imageMass, Finset.map_singleton, Finset.singleton_inj, Equiv.toEmbedding_apply,
    singleton_minor_fourRotation] at h₀ h₁
  have hpair (i k j l : Fin 4) (hi : i ≠ k) (hj : j ≠ l)
      (h : imageMass w {i,k} {j,l} = subsetMinorSq fourRotation {i,k} {j,l}) :
      (∑ σ, w σ * (if (σ i = j ∧ σ k = l) ∨ (σ i = l ∧ σ k = j) then 1 else 0)) =
        minorSq fourRotation i k j l := by
    rw [← pair_minor_fourRotation hi hj, ← h, imageMass]
    apply Finset.sum_congr rfl
    intro σ _
    exact congrArg (fun t : ℝ => w σ * t) (if_congr (map_pair_eq σ hi).symm rfl rfl)
  have hp₂ := hpair 2 3 0 3 (by decide) (by decide) h₂
  have hp₃ := hpair 1 2 0 1 (by decide) (by decide) h₃
  apply no_common_minor_weights_fourRotation
  refine ⟨w, hw, ?_⟩
  simp only [permutationCost, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    h₀, h₁, hp₂, hp₃, mixedCost]

/-- Two alternative insertions of columns into the same set can fail to
share a common law even when both endpoints are included. -/
theorem no_diamond_column_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      ∀ I J : Finset (Fin 4), J ∈ ({{0}, {0,1}, {0,3}, {0,1,3}} : Finset (Finset (Fin 4))) →
        (∑ σ, w σ * (if I.map σ.toEmbedding = J then 1 else 0)) =
          subsetMinorSq fourRotation I J := by
  classical
  rintro ⟨w, hw, hm⟩
  apply fourRotation_imageMass_contradiction w hw (hm _ _ (by decide)) ?_
    (hm _ _ (by decide)) (hm _ _ (by decide))
  have h : imageMass w ({3} : Finset (Fin 4))ᶜ ({2} : Finset (Fin 4))ᶜ =
      subsetMinorSq fourRotation ({3} : Finset (Fin 4))ᶜ ({2} : Finset (Fin 4))ᶜ :=
    hm _ _ (by decide)
  simpa only [imageMass_compl, subsetMinorSq_compl_fourRotation] using h

/-- Choosing three ordered distinct rows for columns zero, one, and two
extends uniquely to a four-permutation. Even the subset-image marginals
of those three columns need not be recoverable by one nonnegative law. -/
theorem no_three_column_common_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      ∀ I J : Finset (Fin 4), 3 ∉ J →
        (∑ σ, w σ * (if I.map σ.toEmbedding = J then 1 else 0)) =
          subsetMinorSq fourRotation I J := by
  classical
  rintro ⟨w, hw, hminor⟩
  have hfull (I J : Finset (Fin 4)) : imageMass w I J = subsetMinorSq fourRotation I J := by
    by_cases h : (3 : Fin 4) ∈ J
    · have he : imageMass w Iᶜ Jᶜ = subsetMinorSq fourRotation Iᶜ Jᶜ :=
        hminor Iᶜ Jᶜ (by simpa using h)
      simpa only [imageMass_compl, subsetMinorSq_compl_fourRotation] using he
    · exact hminor I J h
  exact fourRotation_imageMass_contradiction w hw (hfull _ _) (hfull _ _) (hfull _ _) (hfull _ _)

end MOC
