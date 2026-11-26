import MOC.ContinuousWeightsAtOrigin
import MOC.SubsetMarkerTest

/-! At a spectrum with one entry one and all other entries zero,
continuous exact weights require a universal matching law. -/

open BigOperators Finset Matrix Filter
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def oneHot (r : ι) (i : ι) : ℂ := if i = r then 1 else 0

private def oneHotRayLeft (r : ι) (I : Finset ι) (t : ℝ) (i : ι) : ℂ :=
  if i = r then 1 else if i ∈ I then 0 else t

private def oneHotRayRight (J : Finset ι) (t : ℝ) (j : ι) : ℂ :=
  if j ∈ J then t else 0

private theorem oneHotRay_matching (r : ι) (I J : Finset ι) (hr : r ∉ I)
    (hc : I.card = J.card) (t : ℝ) (p : Equiv.Perm ι) :
    matchingProduct (oneHotRayLeft r I t) (oneHotRayRight J t) p =
      (t : ℂ) ^ (Fintype.card ι - 1) *
        matchingProduct (fun i => if i ∈ I then 0 else 1)
          (fun j => if j ∈ J then 1 else 0) p := by
  classical
  rw [matchingProduct_subset_marker I J hc p]
  by_cases h : J.map p.toEmbedding = I
  · rw [if_pos h, mul_one]
    have hm (j : ι) : p j ∈ I ↔ j ∈ J := by
      rw [← h, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    let k := p.symm r
    have hk : p k = r := p.apply_symm_apply r
    have hkJ : k ∉ J := by
      simpa only [hk] using (fun hJ => hr ((hm k).mpr hJ))
    unfold matchingProduct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    simp only [oneHotRayLeft, hk, if_pos rfl, oneHotRayRight, if_neg hkJ, add_zero, one_mul]
    calc
      _ = ∏ _ ∈ (Finset.univ : Finset ι).erase k, (t : ℂ) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hjk : p j ≠ r := fun hEq =>
          (Finset.mem_erase.mp hj).1 (p.injective (hEq.trans hk.symm))
        by_cases hJ : j ∈ J <;> simp [hjk, hm, hJ]
      _ = _ := by
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k),
          Finset.card_univ]
  · rw [if_neg h, mul_zero]
    have hn : ¬ I ⊆ J.map p.toEmbedding := by
      intro hs
      exact h (Finset.eq_of_subset_of_card_le hs (by rw [Finset.card_map, hc])).symm
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hn
    have hj : p.symm i ∉ J := by rwa [Finset.mem_map_equiv] at hni
    have hir : i ≠ r := fun he => hr (he ▸ hi)
    unfold matchingProduct
    apply Finset.prod_eq_zero (Finset.mem_univ (p.symm i))
    simp [oneHotRayLeft, oneHotRayRight, hi, hj, hir]

private theorem exact_marker_from_oneHot_limit (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (r : ι) (I J : Finset ι) (hr : r ∉ I) (hc : I.card = J.card)
    (w : ((ι → ℂ) × (ι → ℂ)) → Equiv.Perm ι → ℝ)
    (hw : ContinuousAt w (oneHot r, 0))
    (he : ∀ᶠ s : (ι → ℂ) × (ι → ℂ) in 𝓝 (oneHot r, 0),
      weightedMatchingValue s.1 s.2 (w s) = determinantValue s.1 s.2 U) :
    weightedMatchingValue (fun i => if i ∈ I then 0 else 1)
      (fun j => if j ∈ J then 1 else 0) (w (oneHot r, 0)) =
        determinantValue (fun i => if i ∈ I then 0 else 1)
          (fun j => if j ∈ J then 1 else 0) U := by
  let a (i : ι) : ℂ := if i ∈ I then 0 else 1
  let b (j : ι) : ℂ := if j ∈ J then 1 else 0
  let path (t : ℝ) := (oneHotRayLeft r I t, oneHotRayRight J t)
  have hpath : Continuous path := by
    apply Continuous.prodMk <;> apply continuous_pi <;> intro i
    · unfold path oneHotRayLeft
      split_ifs <;> fun_prop
    · unfold path oneHotRayRight
      split_ifs <;> fun_prop
  have hzero : path 0 = (oneHot r, 0) := by
    apply Prod.ext <;> funext i <;> simp [path, oneHotRayLeft, oneHotRayRight, oneHot]
  have hray : Tendsto path (𝓝[>] (0 : ℝ)) (𝓝 (oneHot r, 0)) := by
    rw [← hzero]
    exact hpath.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hweighted : Continuous (fun v : Equiv.Perm ι → ℝ => weightedMatchingValue a b v) := by
    unfold weightedMatchingValue
    fun_prop
  have hlim : Tendsto (fun t => weightedMatchingValue a b (w (path t))) (𝓝[>] (0 : ℝ))
      (𝓝 (weightedMatchingValue a b (w (oneHot r, 0)))) :=
    hweighted.continuousAt.tendsto.comp (hw.tendsto.comp hray)
  have hEq : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      weightedMatchingValue a b (w (path t)) = determinantValue a b U := by
    filter_upwards [hray.eventually he, self_mem_nhdsWithin] with t ht hp
    change 0 < t at hp
    change weightedMatchingValue (oneHotRayLeft r I t) (oneHotRayRight J t) (w (path t)) =
      determinantValue (oneHotRayLeft r I t) (oneHotRayRight J t) U at ht
    have hm (v : Equiv.Perm ι → ℝ) :
        weightedMatchingValue (oneHotRayLeft r I t) (oneHotRayRight J t) v =
          (t : ℂ) ^ (Fintype.card ι - 1) * weightedMatchingValue a b v := by
      unfold weightedMatchingValue
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [oneHotRay_matching r I J hr hc, mul_left_comm]
    rw [hm, ← real_signed_determinant _ _ U hU] at ht
    change (t : ℂ) ^ (Fintype.card ι - 1) * weightedMatchingValue a b (w (path t)) =
      weightedMatchingValue (oneHotRayLeft r I t) (oneHotRayRight J t) (realSignedWeight U) at ht
    rw [hm] at ht
    have hdet : weightedMatchingValue a b (realSignedWeight U) = determinantValue a b U :=
      real_signed_determinant a b U hU
    rw [hdet] at ht
    exact mul_left_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hp.ne')) ht
  exact tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds hEq

/-- Continuous exact matching weights in a neighborhood of the one-hot
spectral pair exist precisely when one law gives every squared minor. -/
theorem hasUniversalMatchingWeights_iff_continuous_at_oneHot
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (r : ι) :
    HasUniversalMatchingWeights U ↔
      ∃ w : ((ι → ℂ) × (ι → ℂ)) → Equiv.Perm ι → ℝ,
        ContinuousAt w (oneHot r, 0) ∧ (∀ p, 0 ≤ w (oneHot r, 0) p) ∧
        (∑ p, w (oneHot r, 0) p = 1) ∧
        ∀ᶠ s : (ι → ℂ) × (ι → ℂ) in 𝓝 (oneHot r, 0),
          weightedMatchingValue s.1 s.2 (w s) = determinantValue s.1 s.2 U := by
  constructor
  · rintro ⟨w, hw, hs, h⟩
    exact ⟨fun _ => w, continuousAt_const, hw, hs,
      Eventually.of_forall fun s => (h s.1 s.2).symm⟩
  · rintro ⟨w, hw, hp, hs, he⟩
    let v := w (oneHot r, 0)
    refine ⟨v, hp, hs, fun a b => ?_⟩
    symm
    apply (weightedMatchingValue_eq_all_iff_subset_markers U hU v).mpr _ a b
    intro I J hc _
    by_cases hr : r ∈ I
    · have hc' : Iᶜ.card = Jᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hc]
      have h := exact_marker_from_oneHot_limit U hU r Iᶜ Jᶜ (by simp [hr]) hc' w hw he
      rw [weightedMatchingValue_subset_marker _ _ _ hc',
        determinantValue_subset_marker _ hU _ _ hc', subsetMinorSq_compl U hU] at h
      have hmap (p : Equiv.Perm ι) : Jᶜ.map p.toEmbedding = (J.map p.toEmbedding)ᶜ := by
        ext j
        simp [Finset.mem_map_equiv]
      simp_rw [hmap, compl_inj_iff] at h
      rw [weightedMatchingValue_subset_marker _ _ _ hc, determinantValue_subset_marker _ hU _ _ hc]
      exact h
    · exact exact_marker_from_oneHot_limit U hU r I J hr hc w hw he

end

end MOC
