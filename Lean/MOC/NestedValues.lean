import MOC.CommonWeights
import MOC.TwoValues
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Instances.Matrix

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

/-- A coupling of adjacent minor laws gives one probability law for every
first spectrum and every choice of the three values on the second side. -/
theorem exists_commonWeights_of_nested_image_coupling (J : Finset ι) (j : ι)
    (hj : j ∉ J) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (p : Finset ι → Finset ι → ℝ)
    (hp : ∀ I K, 0 ≤ p I K)
    (hnest : ∀ I K, p I K ≠ 0 → I ⊆ K)
    (hrow : ∀ I, ∑ K, p I K = subsetMinorSq U I J)
    (hcol : ∀ K, ∑ I, p I K = subsetMinorSq U K (insert j J)) :
    ∃ w : Equiv.Perm ι → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      ∀ (a : ι → ℂ) (c d t : ℂ),
        weightedMatchingValue a (Function.update (fun k => if k ∈ J then c else d) j t) w =
        determinantValue a (Function.update (fun k => if k ∈ J then c else d) j t) U := by
  classical
  let mass (q : Finset ι × Finset ι) := p q.1 q.2
  have hcard (I S : Finset ι) (h : 0 < subsetMinorSq U I S) : I.card = S.card := by
    by_contra hc
    simp [subsetMinorSq, hc] at h
  have supported (q : Finset ι × Finset ι) (hq : mass q ≠ 0) :
      ∃ σ : Equiv.Perm ι,
        J.map σ.toEmbedding = q.1 ∧ (insert j J).map σ.toEmbedding = q.2 := by
    obtain ⟨I, K⟩ := q
    have hpos : 0 < p I K := lt_of_le_of_ne (hp I K) hq.symm
    have hi : 0 < subsetMinorSq U I J := by
      rw [← hrow I]
      exact hpos.trans_le (Finset.single_le_sum (fun L _ => hp I L) (mem_univ K))
    have hk : 0 < subsetMinorSq U K (insert j J) := by
      rw [← hcol K]
      exact hpos.trans_le (Finset.single_le_sum (fun L _ => hp L K) (mem_univ I))
    exact exists_perm_for_nested_images J I K j hj (hnest I K hq)
      (hcard I J hi) (hcard K (insert j J) hk)
  let pick (q : Finset ι × Finset ι) : Equiv.Perm ι :=
    if hq : mass q ≠ 0 then Classical.choose (supported q hq) else 1
  have hpick (q : Finset ι × Finset ι) (hq : mass q ≠ 0) :
      J.map (pick q).toEmbedding = q.1 ∧ (insert j J).map (pick q).toEmbedding = q.2 := by
    simpa only [pick, dif_pos hq] using Classical.choose_spec (supported q hq)
  let w (σ : Equiv.Perm ι) := ∑ q ∈ univ.filter (fun q => pick q = σ), mass q
  have hw (σ : Equiv.Perm ι) : 0 ≤ w σ :=
    Finset.sum_nonneg (fun q _ => hp q.1 q.2)
  have hsum : ∑ σ, w σ = 1 := calc
    _ = ∑ q, mass q := Finset.sum_fiberwise univ pick mass
    _ = ∑ I : Finset ι, ∑ K : Finset ι, p I K := Fintype.sum_prod_type _
    _ = 1 := by simp_rw [hrow]; exact sum_subsetMinorSq U hU J
  have hpush (f : Equiv.Perm ι → ℂ) :
      (∑ σ, (w σ : ℂ) * f σ) = ∑ q, (mass q : ℂ) * f (pick q) := by
    rw [← Finset.sum_fiberwise univ pick]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [w]
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [(Finset.mem_filter.mp hq).2]
  have hleft (f : Finset ι → ℂ) :
      (∑ q, (mass q : ℂ) * f q.1) = ∑ I, (subsetMinorSq U I J : ℂ) * f I := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro I _
    change (∑ K, (p I K : ℂ) * f I) = (subsetMinorSq U I J : ℂ) * f I
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hrow I]
  have hright (f : Finset ι → ℂ) :
      (∑ q, (mass q : ℂ) * f q.2) = ∑ K, (subsetMinorSq U K (insert j J) : ℂ) * f K := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro K _
    change (∑ I, (p I K : ℂ) * f K) = (subsetMinorSq U K (insert j J) : ℂ) * f K
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hcol K]
  have endpoint (a : ι → ℂ) (c d : ℂ) (S : Finset ι) (image : Finset ι × Finset ι → Finset ι)
      (himage : ∀ q, mass q ≠ 0 → S.map (pick q).toEmbedding = image q)
      (havg : ∀ f : Finset ι → ℂ,
        (∑ q, (mass q : ℂ) * f (image q)) = ∑ I, (subsetMinorSq U I S : ℂ) * f I) :
      weightedMatchingValue a (fun k => if k ∈ S then c else d) w =
        determinantValue a (fun k => if k ∈ S then c else d) U := by
    rw [weightedMatchingValue, hpush, determinantValue_two_values a S c d U hU]
    refine Eq.trans ?_ (havg (fun I => ∏ i, (a i + if i ∈ I then c else d)))
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : mass q = 0
    · simp only [hq, Complex.ofReal_zero, zero_mul]
    · rw [matchingProduct_two_values, himage q hq]
  let base (c d : ℂ) (k : ι) := if k ∈ J then c else d
  have regular (a : ι → ℂ) (c d t : ℂ) (hcd : c ≠ d) :
      weightedMatchingValue a (Function.update (base c d) j t) w =
        determinantValue a (Function.update (base c d) j t) U := by
    have h₀ : Function.update (base c d) j d = base c d := by
      funext k
      by_cases hk : k = j
      · subst k
        simp only [Function.update_self, base, if_neg hj]
      · rw [Function.update_of_ne hk]
    have h₁ : Function.update (base c d) j c = fun k => if k ∈ insert j J then c else d := by
      funext k
      by_cases hk : k = j
      · subst k
        simp only [Function.update_self, Finset.mem_insert_self, if_true]
      · simp only [Function.update_of_ne hk, base, Finset.mem_insert, hk, false_or]
    apply weightedMatchingValue_eq_of_two_updates a (base c d) U hU w j hcd.symm _ _ t
    · rw [h₀]
      exact endpoint a c d J Prod.fst (fun q hq => (hpick q hq).1) hleft
    · rw [h₁]
      exact endpoint a c d (insert j J) Prod.snd (fun q hq => (hpick q hq).2) hright
  refine ⟨w, hw, hsum, fun a c d t => ?_⟩
  let b (x : ℂ) := Function.update (base x d) j t
  have hgen : Set.EqOn (fun x => weightedMatchingValue a (b x) w)
      (fun x => determinantValue a (b x) U) ({d} : Set ℂ)ᶜ := by
    intro x hx
    exact regular a x d t (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx)
  have hb : Continuous b := continuous_pi fun k => by
    by_cases hk : k = j
    · subst k
      simpa only [b, Function.update_self] using
        (continuous_const : Continuous (fun _ : ℂ => t))
    · by_cases hJ : k ∈ J
      · simpa only [b, base, Function.update_of_ne hk, if_pos hJ] using
          (continuous_id : Continuous (fun x : ℂ => x))
      · simpa only [b, base, Function.update_of_ne hk, if_neg hJ] using
          (continuous_const : Continuous (fun _ : ℂ => d))
  have hweighted : Continuous (fun x => weightedMatchingValue a (b x) w) := by
    unfold weightedMatchingValue matchingProduct
    exact continuous_finset_sum _ fun σ _ => continuous_const.mul
      (continuous_finset_prod _ fun k _ => continuous_const.add ((continuous_apply k).comp hb))
  have hUconst : Continuous (fun _ : ℂ => U) := continuous_const
  have hUstar : Continuous (fun _ : ℂ => Uᴴ) := continuous_const
  have ha : Continuous (fun _ : ℂ => diagonal a) := continuous_const
  have hdet : Continuous (fun x => determinantValue a (b x) U) :=
    (ha.add ((hUconst.matrix_mul hb.matrix_diagonal).matrix_mul hUstar)).matrix_det
  exact hgen.closure hweighted hdet (dense_compl_singleton d c)

/-- A nested image coupling gives the determinant inclusion. -/
theorem holds_update_of_nested_image_coupling (a : ι → ℂ) (J : Finset ι) (j : ι)
    (hj : j ∉ J) (c d t : ℂ) (_hcd : c ≠ d) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (p : Finset ι → Finset ι → ℝ)
    (hp : ∀ I K, 0 ≤ p I K)
    (hnest : ∀ I K, p I K ≠ 0 → I ⊆ K)
    (hrow : ∀ I, ∑ K, p I K = subsetMinorSq U I J)
    (hcol : ∀ K, ∑ I, p I K = subsetMinorSq U K (insert j J)) :
    Holds a (Function.update (fun k => if k ∈ J then c else d) j t) U := by
  obtain ⟨w, hw, hsum, he⟩ :=
    exists_commonWeights_of_nested_image_coupling J j hj U hU p hp hnest hrow hcol
  exact holds_of_weights w hw hsum (he a c d t)

end

end MOC
