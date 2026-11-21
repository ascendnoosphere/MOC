import MOC.ExteriorMinors
import MOC.WeightedHall

/-! Conditional support bounds for the change of a projection minor law
when one column is added. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sum_subsetMinorSq_score (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (J : Finset ι) (f : Finset ι → ℝ) :
    (∑ I : Finset ι, subsetMinorSq U I J * f I) =
      ∑ σ : Equiv.Perm ι, realSignedWeight U σ * f (J.map σ.toEmbedding) := by
  classical
  rw [← Finset.sum_fiberwise univ (fun σ : Equiv.Perm ι => J.map σ.toEmbedding)]
  apply Finset.sum_congr rfl
  intro I _
  have hmass : (∑ σ ∈ univ.filter (fun σ : Equiv.Perm ι => J.map σ.toEmbedding = I),
      realSignedWeight U σ) = subsetMinorSq U I J := by
    have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
    simpa only [Complex.re_sum, Complex.ofReal_re, realSignedWeight] using h
  rw [← hmass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [(Finset.mem_filter.mp hσ).2]

/-- The change of an additive subset score is the score of the inserted label,
with its distribution given by the entries of the added column. -/
theorem adjacent_minor_additive_score (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (J : Finset ι) (j : ι) (hj : j ∉ J) (H : ι → ℝ) :
    (∑ K : Finset ι, subsetMinorSq U K (insert j J) * (∑ i ∈ K, H i)) -
      (∑ I : Finset ι, subsetMinorSq U I J * (∑ i ∈ I, H i)) =
      ∑ i, Complex.normSq (U i j) * H i := by
  classical
  rw [sum_subsetMinorSq_score U hU, sum_subsetMinorSq_score U hU, ← Finset.sum_sub_distrib]
  have hadd (σ : Equiv.Perm ι) : (∑ i ∈ (insert j J).map σ.toEmbedding, H i) -
      (∑ i ∈ J.map σ.toEmbedding, H i) = H (σ j) := by
    have hnot : σ j ∉ J.map σ.toEmbedding := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hj
    simp only [Finset.map_insert, Equiv.toEmbedding_apply, Finset.sum_insert hnot, add_sub_cancel_right]
  simp_rw [← mul_sub, hadd]
  calc
    _ = ∑ σ : Equiv.Perm ι, ∑ i, if σ j = i then realSignedWeight U σ * H i else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.sum_eq_single (σ j)]
      · simp
      · intro i _ hi
        simp [hi.symm]
      · simp
    _ = ∑ i, (∑ σ : Equiv.Perm ι, if σ j = i then realSignedWeight U σ else 0) * H i := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    _ = _ := by simp_rw [marginal_realSignedWeight U hU]

/-- The two row-set laws for adjacent column sets admit a coupling supported
on inclusions. -/
theorem exists_adjacent_minor_transport {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J) :
    ∃ μ : Finset (Fin n) → Finset (Fin n) → ℝ,
      (∀ I K, 0 ≤ μ I K) ∧ (∀ I K, μ I K ≠ 0 → I ⊆ K) ∧
      (∀ I, ∑ K, μ I K = subsetMinorSq U I J) ∧
      (∀ K, ∑ I, μ I K = subsetMinorSq U K (insert j J)) := by
  classical
  exact exists_transport_of_weighted_hall
    (fun I K : Finset (Fin n) => I ⊆ K) (fun I => subsetMinorSq U I J)
    (fun K => subsetMinorSq U K (insert j J))
    (fun I => subsetMinorSq_nonneg U I J) (fun K => subsetMinorSq_nonneg U K (insert j J))
    (sum_subsetMinorSq U hU J) (sum_subsetMinorSq U hU (insert j J))
    (by
      intro S
      refine (subsetMinorSq_shadow_bound U hU J j hj S).trans ?_
      apply le_of_eq
      apply Finset.sum_congr
      · apply Finset.ext
        intro K
        simp only [Finset.mem_filter]
      · intro K _
        rfl)

/-- When a column is added, the difference of the two squared-minor score
averages is bounded by insertion costs weighted by that column's entries. -/
theorem adjacent_minor_score_le {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J) (f : Finset (Fin n) → ℝ) (H : Fin n → ℝ)
    (hH : ∀ I : Finset (Fin n), I.card = J.card → ∀ i ∉ I, f (insert i I) - f I ≤ H i) :
    (∑ K : Finset (Fin n), subsetMinorSq U K (insert j J) * f K) -
      (∑ I : Finset (Fin n), subsetMinorSq U I J * f I) ≤
      ∑ i, Complex.normSq (U i j) * H i := by
  classical
  obtain ⟨μ, hμ, hnest, hrow, hcol⟩ := exists_adjacent_minor_transport U hU J j hj
  have hc (I T : Finset (Fin n)) (h : 0 < subsetMinorSq U I T) : I.card = T.card := by
    by_contra hne
    simp [subsetMinorSq, hne] at h
  have hgap (I K : Finset (Fin n)) (h : μ I K ≠ 0) :
      ∃ i ∉ I, K = insert i I ∧ I.card = J.card := by
    have hpos := lt_of_le_of_ne (hμ I K) h.symm
    have hr : μ I K ≤ ∑ T, μ I T := single_le_sum (fun T _ => hμ I T) (mem_univ K)
    have hs : μ I K ≤ ∑ T, μ T K := single_le_sum (fun T _ => hμ T K) (mem_univ I)
    rw [hrow I] at hr
    rw [hcol K] at hs
    have hI := hc I J (hpos.trans_le hr)
    have hK := hc K (insert j J) (hpos.trans_le hs)
    rw [Finset.card_insert_of_not_mem hj, ← hI] at hK
    have hincl := hnest I K h
    have hne : I ≠ K := by
      intro he
      rw [← he] at hK
      omega
    obtain ⟨i, hiK, hiI⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hincl, hne⟩)
    refine ⟨i, hiI, (Finset.eq_of_subset_of_card_le (Finset.insert_subset hiK hincl) ?_).symm, hI⟩
    rw [Finset.card_insert_of_not_mem hiI, hK]
  have havg (g : Finset (Fin n) → ℝ) :
      (∑ K : Finset (Fin n), subsetMinorSq U K (insert j J) * g K) -
        (∑ I : Finset (Fin n), subsetMinorSq U I J * g I) =
        ∑ I : Finset (Fin n), ∑ K : Finset (Fin n), μ I K * (g K - g I) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol]
    · simp_rw [← Finset.sum_mul, hrow]
  rw [havg f, ← adjacent_minor_additive_score U hU J j hj H, havg]
  apply Finset.sum_le_sum
  intro I _
  apply Finset.sum_le_sum
  intro K _
  by_cases hz : μ I K = 0
  · simp [hz]
  · obtain ⟨i, hi, rfl, hI⟩ := hgap I K hz
    apply mul_le_mul_of_nonneg_left _ (hμ I (insert i I))
    rw [Finset.sum_insert hi, add_sub_cancel_right]
    exact hH I hI i hi

omit [Fintype ι] in
private theorem pair_score_insert {s : Finset ι} {i : ι} (hi : i ∉ s) (g : Finset ι → ℝ) :
    (∑ P ∈ (insert i s).powersetCard 2, g P) - (∑ P ∈ s.powersetCard 2, g P) =
      ∑ k ∈ s, g {i, k} := by
  classical
  rw [Finset.powersetCard_succ_insert hi 1, Finset.sum_union]
  · rw [add_sub_cancel_left, Finset.sum_image]
    · simp only [Finset.powersetCard_one, Finset.sum_map, Function.Embedding.coeFn_mk]
    · intro A hA B hB h
      have ha : i ∉ A := fun hm => hi ((Finset.mem_powersetCard.mp hA).1 hm)
      have hb : i ∉ B := fun hm => hi ((Finset.mem_powersetCard.mp hB).1 hm)
      simpa only [Finset.erase_insert ha, Finset.erase_insert hb] using congrArg (fun T => T.erase i) h
  · apply Finset.disjoint_left.mpr
    intro P hP hmap
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hmap
    exact hi ((Finset.mem_powersetCard.mp hP).1 (Finset.mem_insert_self _ _))

/-- The sum of the pair scores for a distinguished column and the columns
of `J` obeys the conditional assignment bound. Here `H i` may be chosen
as the sum of the `J.card` largest scores on pairs containing `i`. -/
theorem adjacent_pair_minor_support {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (J : Finset (Fin n)) (j : Fin n) (hj : j ∉ J) (g : Finset (Fin n) → ℝ) (H : Fin n → ℝ)
    (hH : ∀ I : Finset (Fin n), I.card = J.card → ∀ i ∉ I, (∑ k ∈ I, g {i, k}) ≤ H i) :
    (∑ k ∈ J, ∑ P : Finset (Fin n), subsetMinorSq U P {j, k} * g P) ≤
      ∑ i, Complex.normSq (U i j) * H i := by
  classical
  let f (I : Finset (Fin n)) := ∑ P ∈ I.powersetCard 2, g P
  have hlocal (I : Finset (Fin n)) (hI : I.card = J.card) (i : Fin n) (hi : i ∉ I) :
      f (insert i I) - f I ≤ H i := by
    simpa only [f, pair_score_insert hi] using hH I hI i hi
  have heq :
      (∑ K : Finset (Fin n), subsetMinorSq U K (insert j J) * f K) -
        (∑ I : Finset (Fin n), subsetMinorSq U I J * f I) =
        ∑ k ∈ J, ∑ P : Finset (Fin n), subsetMinorSq U P {j, k} * g P := by
    rw [sum_subsetMinorSq_score U hU, sum_subsetMinorSq_score U hU, ← Finset.sum_sub_distrib]
    have hadd (σ : Equiv.Perm (Fin n)) :
        f ((insert j J).map σ.toEmbedding) - f (J.map σ.toEmbedding) =
          ∑ k ∈ J, g (({j, k} : Finset (Fin n)).map σ.toEmbedding) := by
      have hnot : σ j ∉ J.map σ.toEmbedding := by
        simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using hj
      rw [Finset.map_insert]
      change (∑ P ∈ (insert (σ j) (J.map σ.toEmbedding)).powersetCard 2, g P) -
        (∑ P ∈ (J.map σ.toEmbedding).powersetCard 2, g P) = _
      rw [pair_score_insert hnot, Finset.sum_map]
      simp only [Finset.map_insert, Finset.map_singleton, Equiv.toEmbedding_apply]
    simp_rw [← mul_sub, hadd, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [sum_subsetMinorSq_score U hU]
  rw [← heq]
  exact adjacent_minor_score_le U hU J j hj f H hlocal

end

end MOC
