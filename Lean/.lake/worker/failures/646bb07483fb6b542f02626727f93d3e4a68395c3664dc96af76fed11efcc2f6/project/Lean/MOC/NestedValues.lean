import MOC.TwoValues

/-! A coupling of two nested subset-image laws covers a third value at a single label. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_two_values (a : ι → ℂ) (J : Finset ι) (c d : ℂ)
    (σ : Equiv.Perm ι) :
    matchingProduct a (fun j => if j ∈ J then c else d) σ =
      ∏ i, (a i + if i ∈ J.map σ.toEmbedding then c else d) := by
  unfold matchingProduct
  rw [← Equiv.prod_comp σ (fun i => a i + if i ∈ J.map σ.toEmbedding then c else d)]
  simp [Finset.mem_map_equiv]

private theorem determinantValue_two_values (a : ι → ℂ) (J : Finset ι) (c d : ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) :
    determinantValue a (fun j => if j ∈ J then c else d) U =
      ∑ I : Finset ι, (subsetMinorSq U I J : ℂ) * ∏ i, (a i + if i ∈ I then c else d) := by
  classical
  rw [← signed_determinant _ _ U hU]
  rw [← Finset.sum_fiberwise univ (fun σ : Equiv.Perm ι => J.map σ.toEmbedding)]
  apply Finset.sum_congr rfl
  intro I _
  rw [← sum_signedWeight_image_eq_subsetMinorSq U hU I J, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [matchingProduct_two_values, (Finset.mem_filter.mp hσ).2]

private theorem exists_perm_for_nested_images (J I I' : Finset ι) (j : ι)
    (hj : j ∉ J) (hsub : I ⊆ I') (hc : I.card = J.card) (hc' : I'.card = (insert j J).card) :
    ∃ σ : Equiv.Perm ι, J.map σ.toEmbedding = I ∧ (insert j J).map σ.toEmbedding = I' := by
  classical
  have hsize : I'.card = I.card + 1 := by rw [hc', Finset.card_insert_of_not_mem hj, hc]
  have hns : ¬ I' ⊆ I := fun h => by
    have := Finset.card_le_card h
    omega
  obtain ⟨i, hi', hi⟩ := Finset.not_subset.mp hns
  have hins : insert i I = I' := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hi' hsub) (by rw [Finset.card_insert_of_not_mem hi, hsize])
  let e : J ≃ I := Fintype.equivOfCardEq (by simpa using hc.symm)
  let q := e.toCompl.trans (Equiv.swap (e.toCompl ⟨j, hj⟩) ⟨i, hi⟩)
  let σ := Equiv.subtypeCongr e q
  have hσ (k : ι) (hk : k ∈ J) : σ k = e ⟨k, hk⟩ := by
    simp only [σ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
    rw [Equiv.sumCompl_apply_symm_of_pos _ _ hk, Sum.map_inl, Equiv.sumCompl_apply_inl]
  have hσj : σ j = i := by
    simp only [σ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
    rw [Equiv.sumCompl_apply_symm_of_neg _ _ hj, Sum.map_inr, Equiv.sumCompl_apply_inr]
    simp [q]
  have hmap : J.map σ.toEmbedding = I := by
    ext k
    rw [Finset.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      rw [Equiv.toEmbedding_apply, hσ _ hl]
      exact (e ⟨l, hl⟩).property
    · intro hk
      refine ⟨e.symm ⟨k, hk⟩, (e.symm ⟨k, hk⟩).property, ?_⟩
      rw [Equiv.toEmbedding_apply, hσ]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
  exact ⟨σ, hmap, by rw [Finset.map_insert, hmap, Equiv.toEmbedding_apply, hσj, hins]⟩

private theorem matchingProduct_update (a b : ι → ℂ) (j : ι) (t : ℂ)
    (σ : Equiv.Perm ι) :
    matchingProduct a (Function.update b j t) σ =
      (a (σ j) + t) * ∏ k ∈ univ.erase j, (a (σ k) + b k) := by
  unfold matchingProduct
  rw [← Finset.mul_prod_erase univ _ (mem_univ j), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

/-- An image coupling supported on nested sets gives MOC for a spectrum with two values
away from a single exceptional label. -/
theorem holds_update_of_nested_image_coupling (a : ι → ℂ) (J : Finset ι) (j : ι)
    (hj : j ∉ J) (c d t : ℂ) (hcd : c ≠ d) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (p : Finset ι → Finset ι → ℝ)
    (hp : ∀ I I', 0 ≤ p I I')
    (hnest : ∀ I I', p I I' ≠ 0 → I ⊆ I')
    (hrow : ∀ I, ∑ I', p I I' = subsetMinorSq U I J)
    (hcol : ∀ I', ∑ I, p I I' = subsetMinorSq U I' (insert j J)) :
    Holds a (Function.update (fun k => if k ∈ J then c else d) j t) U := by
  classical
  let b₀ : ι → ℂ := fun k => if k ∈ J then c else d
  let b₁ : ι → ℂ := fun k => if k ∈ insert j J then c else d
  let b := Function.update b₀ j t
  let θ := (t - d) / (c - d)
  have hθ : θ * (c - d) = t - d := div_mul_cancel₀ _ (sub_ne_zero.mpr hcd)
  have h₀ : Function.update b₀ j d = b₀ := by
    funext k
    by_cases h : k = j
    · subst k
      simp [b₀, hj]
    · simp [Function.update_of_ne h]
  have h₁ : Function.update b₀ j c = b₁ := by
    funext k
    by_cases h : k = j
    · subst k
      simp [b₁]
    · simp [Function.update_of_ne h, b₀, b₁, Finset.mem_insert, h]
  have haff (σ : Equiv.Perm ι) :
      matchingProduct a b σ =
        (1 - θ) * matchingProduct a b₀ σ + θ * matchingProduct a b₁ σ := by
    rw [← h₀, ← h₁]
    change matchingProduct a (Function.update b₀ j t) σ = _
    simp only [matchingProduct_update]
    have h (x : ℂ) : x + t = (1 - θ) * (x + d) + θ * (x + c) := by
      calc
        x + t = x + d + θ * (c - d) := by rw [hθ]; ring
        _ = _ := by ring
    rw [h (a (σ j))]
    ring
  have hdet :
      determinantValue a b U = (1 - θ) * determinantValue a b₀ U + θ * determinantValue a b₁ U := by
    rw [← signed_determinant a b U hU, ← signed_determinant a b₀ U hU,
      ← signed_determinant a b₁ U hU, mul_sum, mul_sum, ← sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    rw [haff]
    ring
  let v (I : Finset ι) := ∏ i, (a i + if i ∈ I then c else d)
  let r (q : Finset ι × Finset ι) := p q.1 q.2
  let z (q : Finset ι × Finset ι) := (1 - θ) * v q.1 + θ * v q.2
  let T := (univ : Finset (Finset ι × Finset ι)).filter (fun q => r q ≠ 0)
  have hT (q : Finset ι × Finset ι) (hq : q ∈ T) : r q ≠ 0 := (Finset.mem_filter.mp hq).2
  have hz (q : Finset ι × Finset ι) (hq : q ∈ T) :
      z q ∈ Set.range (matchingProduct a b) := by
    obtain ⟨I, I'⟩ := q
    have hp' : 0 < p I I' := lt_of_le_of_ne (hp I I') (hT _ hq).symm
    have hr : 0 < subsetMinorSq U I J := by
      rw [← hrow]
      exact hp'.trans_le (Finset.single_le_sum (fun k _ => hp I k) (mem_univ I'))
    have hc : 0 < subsetMinorSq U I' (insert j J) := by
      rw [← hcol]
      exact hp'.trans_le (Finset.single_le_sum (fun k _ => hp k I') (mem_univ I))
    have hr' : I.card = J.card := by
      by_cases hh : I.card = J.card
      · exact hh
      · have hz₀ : subsetMinorSq U I J = 0 := by simp [subsetMinorSq, hh]
        exact False.elim (hr.ne' hz₀)
    have hc' : I'.card = (insert j J).card := by
      by_cases hh : I'.card = (insert j J).card
      · exact hh
      · have hz₀ : subsetMinorSq U I' (insert j J) = 0 := by simp [subsetMinorSq, hh]
        exact False.elim (hc.ne' hz₀)
    obtain ⟨σ, hσ, hσ'⟩ := exists_perm_for_nested_images J I I' j hj
      (hnest I I' (hT _ hq)) hr' hc'
    refine ⟨σ, ?_⟩
    rw [haff]
    dsimp only [b₀, b₁]
    rw [matchingProduct_two_values, matchingProduct_two_values, hσ, hσ']
  have hsum : ∑ q ∈ T, r q = 1 := calc
    _ = ∑ q, r q := Finset.sum_filter_ne_zero _
    _ = ∑ I : Finset ι, ∑ I', p I I' := Fintype.sum_prod_type _
    _ = 1 := by simp_rw [hrow]; exact sum_subsetMinorSq U hU J
  have hleft : ∑ q : Finset ι × Finset ι, (r q : ℂ) * v q.1 = determinantValue a b₀ U := by
    rw [Fintype.sum_prod_type, determinantValue_two_values a J c d U hU]
    apply Finset.sum_congr rfl
    intro I _
    change (∑ K, (p I K : ℂ) * v I) = (subsetMinorSq U I J : ℂ) * v I
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hrow]
  have hright : ∑ q : Finset ι × Finset ι, (r q : ℂ) * v q.2 = determinantValue a b₁ U := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, determinantValue_two_values a (insert j J) c d U hU]
    apply Finset.sum_congr rfl
    intro I' _
    change (∑ K, (p K I' : ℂ) * v I') = (subsetMinorSq U I' (insert j J) : ℂ) * v I'
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hcol]
  have hweighted : ∑ q ∈ T, r q • z q = determinantValue a b U := calc
    _ = ∑ q, r q • z q := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hq
      by_cases h : r q = 0
      · simp [h]
      · exact False.elim (hq (Finset.mem_filter.mpr ⟨mem_univ _, h⟩))
    _ = (1 - θ) * (∑ q, (r q : ℂ) * v q.1) + θ * (∑ q, (r q : ℂ) * v q.2) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      simp [Complex.real_smul, z]
      ring
    _ = _ := by rw [hleft, hright, hdet]
  change determinantValue a b U ∈ convexHull ℝ (Set.range (matchingProduct a b))
  rw [← hweighted, ← T.centerMass_eq_of_sum_1 z hsum]
  exact T.centerMass_mem_convexHull (fun q _ => hp q.1 q.2) (hsum.symm ▸ zero_lt_one) hz

end

end MOC
