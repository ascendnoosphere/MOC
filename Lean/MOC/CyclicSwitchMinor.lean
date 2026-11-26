import MOC.CyclicSwitchMatrices

/-! Nontransversal minors factor through at most one intermediate subset. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
private theorem det_mul_sum_assignments (A : Matrix α β ℂ) (B : Matrix β α ℂ) :
    (A * B).det = ∑ f : α → β,
      (∏ j, B (f j) j) * (A.submatrix id f).det := by
  let D := (Matrix.detRowAlternating : (α → ℂ) [⋀^α]→ₗ[ℂ] ℂ).toMultilinearMap
  let g (j : α) (k : β) : α → ℂ := B k j • fun i => A i k
  have hd : (A * B)ᵀ = fun j => ∑ k, g j k := by
    ext j i : 1
    simp [Matrix.mul_apply, g, mul_comm]
  rw [← Matrix.det_transpose, hd]
  change D (fun j => ∑ k, g j k) = _
  rw [D.map_sum g]
  apply Finset.sum_congr rfl
  intro f _
  change D (fun j => B (f j) j • fun i => A i (f j)) = _
  rw [D.map_smul_univ]
  rw [smul_eq_mul, ← Matrix.det_transpose (A.submatrix id f)]
  rfl

omit [DecidableEq β] in
/-- If all nonzero products through intermediate columns use the chosen set,
the determinant factors through its two square minors. -/
theorem det_mul_eq_det_restrict_of_assignment_support (A : Matrix α β ℂ) (B : Matrix β α ℂ)
    (K : Finset β) (e : α ≃ K)
    (hf : ∀ f : α → β, Function.Injective f → (∀ j, B (f j) j ≠ 0) →
      (A.submatrix id f).det ≠ 0 → ∀ j, f j ∈ K) :
    (A * B).det = (A.submatrix id (Subtype.val ∘ e)).det *
      (B.submatrix (Subtype.val ∘ e) id).det := by
  classical
  let A' := A.submatrix id (Subtype.val ∘ e)
  let B' := B.submatrix (Subtype.val ∘ e) id
  let i : (α → α) ↪ (α → β) := ⟨fun f j => (e (f j)).val, fun f g h => by
    funext j
    exact e.injective (Subtype.ext (congrFun h j))⟩
  change _ = A'.det * B'.det
  rw [← Matrix.det_mul, det_mul_sum_assignments, det_mul_sum_assignments]
  let F (f : α → β) := (∏ j, B (f j) j) * (A.submatrix id f).det
  change (∑ f : α → β, F f) = ∑ f : α → α, F (i f)
  rw [← Finset.sum_map Finset.univ i F]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro f _ hout
  by_contra hF
  have hdet : (A.submatrix id f).det ≠ 0 := right_ne_zero_of_mul hF
  have hB (j : α) : B (f j) j ≠ 0 := by
    intro hz
    exact left_ne_zero_of_mul hF (Finset.prod_eq_zero (Finset.mem_univ j) hz)
  have hinj : Function.Injective f := by
    intro j k he
    by_contra hne
    exact hdet (Matrix.det_zero_of_column_eq hne (fun l => by simp [he]))
  let g (j : α) : α := e.symm ⟨f j, hf f hinj hB hdet j⟩
  have he : i g = f := by
    funext j
    change (e (e.symm ⟨f j, hf f hinj hB hdet j⟩)).val = f j
    rw [e.apply_symm_apply]
  exact hout (Finset.mem_map.mpr ⟨g, Finset.mem_univ _, he⟩)

omit [DecidableEq β] in
/-- The determinant is zero when every injective assignment has a zero factor. -/
theorem det_mul_eq_zero_of_assignment_support (A : Matrix α β ℂ) (B : Matrix β α ℂ)
    (hf : ∀ f : α → β, Function.Injective f → (∀ j, B (f j) j ≠ 0) →
      (A.submatrix id f).det = 0) :
    (A * B).det = 0 := by
  rw [det_mul_sum_assignments]
  apply Finset.sum_eq_zero
  intro f _
  by_contra hF
  have hdet : (A.submatrix id f).det ≠ 0 := right_ne_zero_of_mul hF
  have hB (j : α) : B (f j) j ≠ 0 := by
    intro hz
    exact left_ne_zero_of_mul hF (Finset.prod_eq_zero (Finset.mem_univ j) hz)
  have hinj : Function.Injective f := by
    intro j k he
    by_contra hne
    exact hdet (Matrix.det_zero_of_column_eq hne (fun l => by simp [he]))
  exact hdet (hf f hinj hB)

end

end MOC

namespace MOC

noncomputable section

variable {κ ι α : Type*} [DecidableEq κ] [DecidableEq ι]

theorem blockOccupancy_eq_sum (e : κ × Bool ≃ ι) (S : Finset ι) (k : κ) :
    blockOccupancy e S k = ∑ i ∈ S, if (e.symm i).1 = k then (1 : ℤ) else 0 := by
  have he (i : ι) : (if (e.symm i).1 = k then (1 : ℤ) else 0) =
      (if i = e (k, false) then 1 else 0) + (if i = e (k, true) then 1 else 0) := by
    obtain ⟨⟨j,b⟩, rfl⟩ := e.surjective i
    cases b <;> by_cases hj : j = k <;> simp [hj, e.apply_eq_iff_eq]
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_ite_eq', blockOccupancy, positionOccupancy]

/-- If two injective lists use the same block at each position, their images
have the same block count. -/
theorem blockOccupancy_map_eq_of_labels (e : κ × Bool ≃ ι)
    (S : Finset α) (f g : α ↪ ι)
    (h : ∀ j ∈ S, (e.symm (f j)).1 = (e.symm (g j)).1) (k : κ) :
    blockOccupancy e (S.map f) k = blockOccupancy e (S.map g) k := by
  rw [blockOccupancy_eq_sum, blockOccupancy_eq_sum, Finset.sum_map, Finset.sum_map]
  exact Finset.sum_congr rfl (fun j hj => by rw [h j hj])

theorem blockOccupancy_map_blockSwitch (e : κ × Bool ≃ ι)
    (S : Finset ι) (x : κ → Bool) (k : κ) :
    blockOccupancy e (S.map (blockSwitch e x).toEmbedding) k = blockOccupancy e S k := by
  have he : ∀ j ∈ S, (e.symm (blockSwitch e x j)).1 = (e.symm j).1 := by
    intro j _
    obtain ⟨⟨l,b⟩, rfl⟩ := e.surjective j
    simp [blockSwitch_apply]
  simpa only [Finset.map_refl] using
    blockOccupancy_map_eq_of_labels e S (blockSwitch e x).toEmbedding
      (Function.Embedding.refl ι) he k

end

end MOC

open BigOperators Matrix Finset

namespace MOC

noncomputable section

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

private def selectedEmbedding {α : Type*} {S : Finset ι} (e : α ≃ S) : α ↪ ι :=
  e.toEmbedding.trans (Function.Embedding.subtype _)

omit [Fintype ι] [DecidableEq ι] in
private theorem map_selectedEmbedding {α : Type*} [Fintype α] {S : Finset ι} (e : α ≃ S) :
    univ.map (selectedEmbedding e) = S := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact (e j).property
  · intro hi
    exact Finset.mem_map.mpr ⟨e.symm ⟨i,hi⟩, mem_univ _, by simp [selectedEmbedding]⟩

omit [Fintype κ] [Fintype ι] [DecidableEq ι] in
private theorem blockGateMatrix_label {e : κ × Bool ≃ ι} {Q : κ → Matrix Bool Bool ℂ}
    {i j : ι} (h : blockGateMatrix e Q i j ≠ 0) : (e.symm i).1 = (e.symm j).1 := by
  by_contra hn
  exact h (if_neg hn)

omit [Fintype κ] [Fintype ι] in
private theorem intermediate_assignment_occupancy {α : Type*} [Fintype α] [DecidableEq α]
    (eL eR : κ × Bool ≃ ι) (L R : κ → Matrix Bool Bool ℂ)
    (I J : Finset ι) (r : α ≃ I) (c : α ≃ J) (f : α → ι) (hf : Function.Injective f)
    (hB : ∀ j, blockGateMatrix eR R (f j) (c j).val ≠ 0)
    (hA : ((blockGateMatrix eL L).submatrix (Subtype.val ∘ r) f).det ≠ 0) :
    let K := univ.map (⟨f,hf⟩ : α ↪ ι)
    (∀ k, blockOccupancy eL K k = blockOccupancy eL I k) ∧
      (∀ k, blockOccupancy eR K k = blockOccupancy eR J k) := by
  classical
  rw [Matrix.det_apply'] at hA
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
  have hpterm (j : α) : blockGateMatrix eL L (r (p j)).val (f j) ≠ 0 := by
    intro hn
    exact (right_ne_zero_of_mul hp) (Finset.prod_eq_zero (mem_univ j) hn)
  intro K
  constructor
  · intro k
    let g : α ↪ ι := p.toEmbedding.trans (selectedEmbedding r)
    have hg : univ.map g = I := by
      change univ.map (p.toEmbedding.trans (selectedEmbedding r)) = I
      rw [← Finset.map_map, Finset.map_univ_equiv, map_selectedEmbedding]
    rw [← hg]
    exact blockOccupancy_map_eq_of_labels eL univ ⟨f,hf⟩ g
      (fun j _ => (blockGateMatrix_label (hpterm j)).symm) k
  · intro k
    rw [← map_selectedEmbedding c]
    exact blockOccupancy_map_eq_of_labels eR univ ⟨f,hf⟩ (selectedEmbedding c)
      (fun j _ => blockGateMatrix_label (hB j)) k

omit [Fintype κ] in
/-- In the nontransversal case, the intermediate compatible set is unique. -/
theorem cyclic_intermediate_eq_of_counts (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (I J S T : Finset (κ × Bool))
    (hSL : ∀ k, blockOccupancy (Equiv.refl _) S k = blockOccupancy (Equiv.refl _) I k)
    (hSR : ∀ k, blockOccupancy (cyclicRightChart s) S k = blockOccupancy (cyclicRightChart s) J k)
    (hTL : ∀ k, blockOccupancy (Equiv.refl _) T k = blockOccupancy (Equiv.refl _) I k)
    (hTR : ∀ k, blockOccupancy (cyclicRightChart s) T k = blockOccupancy (cyclicRightChart s) J k)
    (hn : ¬ BlockTransversal (Equiv.refl _) I ∨ ¬ BlockTransversal (cyclicRightChart s) J) :
    S = T := by
  apply cyclic_middle_eq_of_nontransversal s hs S T
    (fun k => (hSL k).trans (hTL k).symm) (fun k => (hSR k).trans (hTR k).symm)
  rcases hn with hn | hn
  · refine Or.inl (fun hS => hn fun k => ?_)
    exact (blockOccupancy_eq_one_iff _ _ _).mp
      ((hSL k).symm.trans ((blockOccupancy_eq_one_iff _ _ _).mpr (hS k)))
  · refine Or.inr (fun hS => hn fun k => ?_)
    exact (blockOccupancy_eq_one_iff _ _ _).mp
      ((hSR k).symm.trans ((blockOccupancy_eq_one_iff _ _ _).mpr (hS k)))

end

end MOC

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem sum_blockOccupancy {ι : Type*} [DecidableEq ι]
    (e : κ × Bool ≃ ι) (S : Finset ι) :
    (∑ k, blockOccupancy e S k) = (S.card : ℤ) := by
  simp_rw [blockOccupancy_eq_sum]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

omit [Fintype κ] in
private theorem twoLayerSwitch_event_with_middle (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (I J K : Finset (κ × Bool))
    (hKL : ∀ k, blockOccupancy (Equiv.refl _) K k = blockOccupancy (Equiv.refl _) I k)
    (hKR : ∀ k, blockOccupancy (cyclicRightChart s) K k = blockOccupancy (cyclicRightChart s) J k)
    (hn : ¬ BlockTransversal (Equiv.refl _) I ∨ ¬ BlockTransversal (cyclicRightChart s) J)
    (x : κ ⊕ κ → Bool) :
    J.map (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I ↔
      K.map (blockSwitch (Equiv.refl _) (x ∘ Sum.inl)).toEmbedding = I ∧
      J.map (blockSwitch (cyclicRightChart s) (x ∘ Sum.inr)).toEmbedding = K := by
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  have hm (h : J.map (twoLayerSwitch eL eR x).toEmbedding = I) :
      J.map (blockSwitch eR (x ∘ Sum.inr)).toEmbedding = K := by
    apply cyclic_intermediate_eq_of_counts s hs I J _ K _ _ hKL hKR hn
    · intro k
      rw [(twoLayerSwitch_event_iff eL eR x I J).mp h]
      exact blockOccupancy_map_blockSwitch eL I _ k
    · intro k
      exact blockOccupancy_map_blockSwitch eR J _ k
  change J.map (twoLayerSwitch eL eR x).toEmbedding = I ↔ _
  constructor
  · intro h
    refine ⟨?_, hm h⟩
    have hd : ((J.map (blockSwitch eR (x ∘ Sum.inr)).toEmbedding).map
      (blockSwitch eL (x ∘ Sum.inl)).toEmbedding) = I := by
      rw [Finset.map_map]
      exact h
    rwa [hm h] at hd
  · rintro ⟨hL,hR⟩
    change J.map (blockSwitch eL (x ∘ Sum.inl) * blockSwitch eR (x ∘ Sum.inr)).toEmbedding = I
    rw [show (blockSwitch eL (x ∘ Sum.inl) * blockSwitch eR (x ∘ Sum.inr)).toEmbedding =
      (blockSwitch eR (x ∘ Sum.inr)).toEmbedding.trans (blockSwitch eL (x ∘ Sum.inl)).toEmbedding
      from rfl, ← Finset.map_map, hR, hL]

private theorem sum_twoLayerSwitch_event_of_middle (s : Equiv.Perm κ)
    (hs : TraversesAllIndices s) (I J K : Finset (κ × Bool))
    (hKL : ∀ k, blockOccupancy (Equiv.refl _) K k = blockOccupancy (Equiv.refl _) I k)
    (hKR : ∀ k, blockOccupancy (cyclicRightChart s) K k = blockOccupancy (cyclicRightChart s) J k)
    (hn : ¬ BlockTransversal (Equiv.refl _) I ∨ ¬ BlockTransversal (cyclicRightChart s) J)
    (dL dR : (κ → Bool) → ℝ) :
    (∑ x ∈ univ.filter (fun x => J.map
        (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I), dL (x ∘ Sum.inl) * dR (x ∘ Sum.inr)) =
      (∑ x ∈ univ.filter (fun x => K.map (blockSwitch (Equiv.refl _) x).toEmbedding = I), dL x) *
      (∑ x ∈ univ.filter (fun x => J.map (blockSwitch (cyclicRightChart s) x).toEmbedding = K), dR x) := by
  classical
  let e := Equiv.sumArrowEquivProdArrow κ κ Bool
  simp only [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  let g (xy : (κ → Bool) × (κ → Bool)) : ℝ :=
    (if K.map (blockSwitch (Equiv.refl _) xy.1).toEmbedding = I then dL xy.1 else 0) *
    (if J.map (blockSwitch (cyclicRightChart s) xy.2).toEmbedding = K then dR xy.2 else 0)
  change _ = ∑ y, ∑ x, g (x,y)
  rw [Finset.sum_comm, ← Fintype.sum_prod_type g]
  apply Fintype.sum_equiv e
  intro x
  have he := twoLayerSwitch_event_with_middle s hs I J K hKL hKR hn x
  change (if J.map (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I then
    dL (x ∘ Sum.inl) * dR (x ∘ Sum.inr) else 0) = (if K.map (blockSwitch (Equiv.refl _) (x ∘ Sum.inl)).toEmbedding = I then
    dL (x ∘ Sum.inl) else 0) * (if J.map (blockSwitch (cyclicRightChart s) (x ∘ Sum.inr)).toEmbedding = K then
    dR (x ∘ Sum.inr) else 0)
  by_cases hl : K.map (blockSwitch (Equiv.refl _) (x ∘ Sum.inl)).toEmbedding = I <;>
    by_cases hr : J.map (blockSwitch (cyclicRightChart s) (x ∘ Sum.inr)).toEmbedding = K <;>
    simp [he, hl, hr]

/-- With a nontransversal boundary, a compatible intermediate set gives the
whole squared minor as the product of two layer minors. With no set the minor is zero. -/
theorem cyclic_nontransversal_subsetMinorSq (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (I J : Finset (κ × Bool)) (hIJ : I.card = J.card)
    (hn : ¬ BlockTransversal (Equiv.refl _) I ∨ ¬ BlockTransversal (cyclicRightChart s) J) :
    let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
    let eR := cyclicRightChart s
    let U := blockGateMatrix eL L
    let V := blockGateMatrix eR R
    let compatible := fun K =>
      (∀ k, blockOccupancy eL K k = blockOccupancy eL I k) ∧
      (∀ k, blockOccupancy eR K k = blockOccupancy eR J k)
    (∀ K, compatible K → subsetMinorSq (U * V) I J =
      subsetMinorSq U I K * subsetMinorSq V K J) ∧
      ((¬ ∃ K, compatible K) → subsetMinorSq (U * V) I J = 0) := by
  classical
  dsimp only
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  let U := blockGateMatrix eL L
  let V := blockGateMatrix eR R
  let r : J ≃ I := Fintype.equivOfCardEq (by simpa using hIJ.symm)
  let c : J ≃ J := Equiv.refl _
  let A := U.submatrix (Subtype.val ∘ r) id
  let B := V.submatrix id (Subtype.val ∘ c)
  have hm : (U * V).submatrix (Subtype.val ∘ r) (Subtype.val ∘ c) = A * B :=
    Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id
  rw [subsetMinorSq_eq_normSq_det_submatrix _ (blockGateMatrix_mul_unitary eL eR L R hL hR)
    I J r c, hm]
  have hassign (f : J → κ × Bool) (hf : Function.Injective f)
      (hB : ∀ j, B (f j) j ≠ 0) (hA : (A.submatrix id f).det ≠ 0) :
      let K := univ.map (⟨f,hf⟩ : J ↪ κ × Bool)
      (∀ k, blockOccupancy eL K k = blockOccupancy eL I k) ∧
        (∀ k, blockOccupancy eR K k = blockOccupancy eR J k) :=
    intermediate_assignment_occupancy eL eR L R I J r c f hf hB hA
  constructor
  · rintro K ⟨hKL,hKR⟩
    have hcard : K.card = J.card := by
      exact_mod_cast (sum_blockOccupancy eR K).symm.trans
        ((Finset.sum_congr rfl (fun k _ => hKR k)).trans (sum_blockOccupancy eR J))
    let e : J ≃ K := Fintype.equivOfCardEq (by simpa using hcard.symm)
    have hrestrict := det_mul_eq_det_restrict_of_assignment_support A B K e
      (fun f hf hb ha j => by
        let K' := univ.map (⟨f,hf⟩ : J ↪ κ × Bool)
        have he : K' = K := cyclic_intermediate_eq_of_counts s hs I J K' K
          (hassign f hf hb ha).1 (hassign f hf hb ha).2 hKL hKR hn
        rw [← he]
        exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    rw [hrestrict, map_mul]
    rw [subsetMinorSq_eq_normSq_det_submatrix _ (blockGateMatrix_unitary eL L hL) I K r e,
      subsetMinorSq_eq_normSq_det_submatrix _ (blockGateMatrix_unitary eR R hR) K J e c]
    rfl
  · intro hnone
    rw [det_mul_eq_zero_of_assignment_support A B]
    · simp
    · intro f hf hb
      by_contra ha
      exact hnone ⟨_, hassign f hf hb ha⟩

end

end MOC

namespace MOC

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem cyclic_nontransversal_independent_law (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, IsUnitary (L k)) (hR : ∀ k, IsUnitary (R k))
    (I J : Finset (κ × Bool))
    (hn : ¬ BlockTransversal (Equiv.refl _) I ∨ ¬ BlockTransversal (cyclicRightChart s) J) :
    subsetMinorSq (blockGateMatrix (Equiv.refl _) L * blockGateMatrix (cyclicRightChart s) R) I J =
      ∑ x ∈ univ.filter (fun x => J.map
        (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I),
          cyclicIndependentWeight L R x := by
  classical
  let eL : κ × Bool ≃ κ × Bool := Equiv.refl _
  let eR := cyclicRightChart s
  let E := univ.filter (fun x => J.map (twoLayerSwitch eL eR x).toEmbedding = I)
  let U := blockGateMatrix eL L
  let V := blockGateMatrix eR R
  change subsetMinorSq (U * V) I J =
    ∑ x ∈ E, cyclicIndependentWeight L R x
  by_cases hIJ : I.card = J.card
  · obtain ⟨hm, hz⟩ := cyclic_nontransversal_subsetMinorSq s hs L R
      hL hR I J hIJ hn
    let compatible := fun K =>
      (∀ k, blockOccupancy eL K k = blockOccupancy eL I k) ∧
      (∀ k, blockOccupancy eR K k = blockOccupancy eR J k)
    by_cases hK : ∃ K, compatible K
    · obtain ⟨K, hKL, hKR⟩ := hK
      rw [hm K ⟨hKL,hKR⟩, blockGateMatrix_independent_law eL L hL,
        blockGateMatrix_independent_law eR R hR]
      simp only [cyclicIndependentWeight, E]
      exact (sum_twoLayerSwitch_event_of_middle s hs I J K hKL hKR hn _ _).symm
    · rw [hz hK]
      have he : E = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        intro x _ hx
        let K := J.map (blockSwitch eR (x ∘ Sum.inr)).toEmbedding
        apply hK
        refine ⟨K, ?_, fun k => blockOccupancy_map_blockSwitch eR J _ k⟩
        intro k
        change blockOccupancy eL (J.map (blockSwitch eR (x ∘ Sum.inr)).toEmbedding) k = _
        rw [(twoLayerSwitch_event_iff eL eR x I J).mp hx]
        exact blockOccupancy_map_blockSwitch eL I _ k
      simp [he]
  · have he : E = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro x _ hx
      exact hIJ (by rw [← hx, Finset.card_map])
    simp [he, subsetMinorSq, hIJ]
theorem cyclic_nontransversal_uniform_law (s : Equiv.Perm κ) (hs : TraversesAllIndices s)
    (L R : κ → Matrix Bool Bool ℂ) (hL : ∀ k, BalancedGate (L k)) (hR : ∀ k, BalancedGate (R k))
    (I J : Finset (κ × Bool))
    (hn : ¬ BlockTransversal (Equiv.refl _) I ∨ ¬ BlockTransversal (cyclicRightChart s) J) :
    subsetMinorSq (blockGateMatrix (Equiv.refl _) L * blockGateMatrix (cyclicRightChart s) R) I J =
      ∑ _x ∈ univ.filter (fun x => J.map
        (twoLayerSwitch (Equiv.refl _) (cyclicRightChart s) x).toEmbedding = I),
          (1 / 2 : ℝ) ^ (Fintype.card κ + Fintype.card κ) := by
  simpa only [cyclicIndependentWeight_balanced L R hL hR] using
    cyclic_nontransversal_independent_law s hs L R (fun k => (hL k).1) (fun k => (hR k).1) I J hn

end

end MOC
