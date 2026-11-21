import MOC.MatchingProfileCompactness
import MOC.RankTwoMatchingProfile

/-! Three-row minor constraints give a closed set of matching profiles. -/

open BigOperators Matrix Set

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem reindexed_column_scaled_profile (K : Matrix ι ι ℂ)
    (r : Equiv.Perm ι) (d : ι → ℂ) (hK : VanishingThreeMinors K) :
    let M : Matrix ι ι ℂ := Matrix.of fun i j => K (r i) j * d j
    VanishingThreeMinors M ∧ ∀ σ : Equiv.Perm ι,
      kernelMatchingProduct M σ = (∏ j, d j) * kernelMatchingProduct K (r * σ) := by
  dsimp only
  constructor
  · intro a b
    have hsub : (Matrix.of fun i j => K (r i) j * d j).submatrix a b =
        Matrix.of fun i j => d (b j) * (K.submatrix (r ∘ a) b) i j := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply, mul_comm]
    rw [hsub, Matrix.det_mul_row, hK (r ∘ a) b, mul_zero]
  · intro σ
    simp only [kernelMatchingProduct, Matrix.of_apply, Finset.prod_mul_distrib,
      Equiv.Perm.mul_apply]
    exact mul_comm _ _

private theorem isClosed_rankTwo_profiles_nonempty [Nonempty ι] :
    IsClosed {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
      VanishingThreeMinors K ∧ kernelMatchingProduct K = p} := by
  classical
  let V := Equiv.Perm ι → ℂ
  let N : Set V := {p | ∃ K : Matrix ι ι ℂ,
    (∀ i, K i i = 1) ∧ VanishingThreeMinors K ∧
      (∀ σ, ‖p σ‖ ≤ 1) ∧ kernelMatchingProduct K = p}
  have hN : IsCompact N := isCompact_normalized_rankTwo_matching_profiles
  letI : CompactSpace N := isCompact_iff_compactSpace.mp hN
  let C (r : Equiv.Perm ι) : Set V := {p | ∃ u : N, ∀ σ,
    p σ = p r * u.val (r⁻¹ * σ)}
  have hC (r : Equiv.Perm ι) : IsClosed (C r) := by
    let D : Set (V × N) := {w | ∀ σ, w.1 σ = w.1 r * w.2.val (r⁻¹ * σ)}
    have hD : IsClosed D := by
      change IsClosed {w : V × N | ∀ σ, w.1 σ = w.1 r * w.2.val (r⁻¹ * σ)}
      rw [Set.setOf_forall]
      exact isClosed_iInter fun σ => isClosed_eq ((continuous_apply σ).comp continuous_fst)
        (((continuous_apply r).comp continuous_fst).mul
          ((continuous_apply (r⁻¹ * σ)).comp (continuous_subtype_val.comp continuous_snd)))
    have hDC : Prod.fst '' D = C r := by
      ext p
      constructor
      · rintro ⟨⟨_, u⟩, hu, rfl⟩
        exact ⟨u, hu⟩
      · rintro ⟨u, hu⟩
        exact ⟨(p, u), hu, rfl⟩
    rw [← hDC]
    exact isClosedMap_fst_of_compactSpace D hD
  have hset : {p : V | ∃ K : Matrix ι ι ℂ,
      VanishingThreeMinors K ∧ kernelMatchingProduct K = p} = {0} ∪ ⋃ r, C r := by
    ext p
    constructor
    · rintro ⟨K, hK, hp⟩
      by_cases hzero : p = 0
      · exact Set.mem_union_left _ (Set.mem_singleton_iff.mpr hzero)
      obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ (fun σ => ‖p σ‖)
        ⟨1, Finset.mem_univ _⟩
      have hpr : p r ≠ 0 := by
        intro hz
        apply hzero
        funext σ
        have h := hr σ (Finset.mem_univ _)
        rw [hz, norm_zero] at h
        exact norm_le_zero_iff.mp h
      have he : (∏ j, K (r j) j) = p r := congrFun hp r
      have hentry (j : ι) : K (r j) j ≠ 0 :=
        Finset.prod_ne_zero_iff.mp (he.trans_ne hpr) j (Finset.mem_univ _)
      let d (j : ι) := (K (r j) j)⁻¹
      let M : Matrix ι ι ℂ := Matrix.of fun i j => K (r i) j * d j
      obtain ⟨hM, hval⟩ := reindexed_column_scaled_profile K r d hK
      have hdprod : (∏ j, d j) = (p r)⁻¹ := by
        simp only [d, Finset.prod_inv_distrib, he]
      have hquot (σ : Equiv.Perm ι) : kernelMatchingProduct M σ = (p r)⁻¹ * p (r * σ) := by
        rw [hval σ, hdprod, congrFun hp (r * σ)]
      have hd (j : ι) : M j j = 1 := mul_inv_cancel₀ (hentry j)
      have hbound (σ : Equiv.Perm ι) : ‖kernelMatchingProduct M σ‖ ≤ 1 := by
        rw [hquot, norm_mul, norm_inv, inv_mul_eq_div]
        exact (div_le_one₀ (norm_pos_iff.mpr hpr)).mpr (hr (r * σ) (Finset.mem_univ _))
      let u : N := ⟨kernelMatchingProduct M, M, hd, hM, hbound, rfl⟩
      refine Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨r, u, ?_⟩)
      intro σ
      change p σ = p r * kernelMatchingProduct M (r⁻¹ * σ)
      rw [hquot, ← mul_assoc, mul_inv_cancel₀ hpr, one_mul]
      simp
    · intro hp
      let j₀ := Classical.choice (inferInstance : Nonempty ι)
      rcases hp with hzero | hc
      · rw [Set.mem_singleton_iff.mp hzero]
        refine ⟨0, fun a b => by simp, ?_⟩
        funext σ
        change (∏ _ : ι, (0 : ℂ)) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ j₀) rfl
      · obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hc
        obtain ⟨u, hu⟩ := hr
        obtain ⟨K, _, hK, _, hval⟩ := u.property
        let d (j : ι) := if j = j₀ then p r else 1
        have hdprod : (∏ j, d j) = p r := by
          rw [Finset.prod_eq_single j₀]
          · simp [d]
          · intro j _ hj
            simp [d, hj]
          · simp
        obtain ⟨hM, hMp⟩ := reindexed_column_scaled_profile K r⁻¹ d hK
        refine ⟨Matrix.of (fun i j => K (r⁻¹ i) j * d j), hM, ?_⟩
        funext σ
        rw [hMp σ, hdprod, congrFun hval (r⁻¹ * σ)]
        exact (hu σ).symm
  rw [hset]
  exact isClosed_singleton.union (isClosed_iUnion_of_finite hC)

/-- The profiles of kernels with all three-row minors zero form a closed
set, including limits in which some or all matching products vanish. -/
theorem isClosed_rankTwo_matching_profiles :
    IsClosed {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
      VanishingThreeMinors K ∧ kernelMatchingProduct K = p} := by
  cases isEmpty_or_nonempty ι with
  | inr h => letI := h; exact isClosed_rankTwo_profiles_nonempty
  | inl h =>
    letI := h
    have he : {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
        VanishingThreeMinors K ∧ kernelMatchingProduct K = p} = {fun _ => 1} := by
      ext p
      constructor
      · rintro ⟨K, _, rfl⟩
        apply Set.mem_singleton_iff.mpr
        funext σ
        simp [kernelMatchingProduct]
      · intro hp
        rw [Set.mem_singleton_iff.mp hp]
        refine ⟨0, fun a _ => isEmptyElim (a 0), ?_⟩
        funext σ
        simp [kernelMatchingProduct]
    rw [he]
    exact isClosed_singleton

/-- Exact additive matching profiles coincide with the profiles of kernels
whose three-row minors vanish. A common scalar is absorbed into both spectra. -/
theorem additive_profiles_eq_rankTwo_matching_profiles :
    {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ, matchingProduct a b = p} =
    {p : Equiv.Perm ι → ℂ | ∃ K : Matrix ι ι ℂ,
      VanishingThreeMinors K ∧ kernelMatchingProduct K = p} := by
  classical
  ext p
  constructor
  · rintro ⟨a, b, hp⟩
    refine ⟨Matrix.of (fun i j => a i + b j), ?_, hp⟩
    intro r c
    simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply]
    ring
  · rintro ⟨K, hK, hp⟩
    cases isEmpty_or_nonempty ι with
    | inl h =>
      letI := h
      refine ⟨0, 0, ?_⟩
      funext σ
      rw [← congrFun hp σ]
      simp [matchingProduct, kernelMatchingProduct]
    | inr h =>
      letI := h
      by_cases hz : p = 0
      · refine ⟨0, 0, ?_⟩
        funext σ
        rw [hz]
        change (∏ j : ι, ((0 : ι → ℂ) (σ j) + (0 : ι → ℂ) j)) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ (Classical.choice h)) (by simp)
      obtain ⟨σ, hσ⟩ : ∃ σ, p σ ≠ 0 := by
        contrapose! hz
        exact funext hz
      have hprod : (∏ j, K (σ j) j) ≠ 0 := (congrFun hp σ).trans_ne hσ
      have hentry (j : ι) : K (σ j) j ≠ 0 :=
        Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ _)
      have hrow (i : ι) : ∃ j, K i j ≠ 0 :=
        ⟨σ.symm i, by simpa only [Equiv.apply_symm_apply] using hentry (σ.symm i)⟩
      obtain ⟨L, R, α, β, _, _, hg⟩ :=
        exists_additive_gauge_of_three_minors_eq_zero K hK hrow (fun j => ⟨σ j, hentry j⟩)
      let d := (∏ i, L i) * ∏ j, R j
      have hprofile (τ : Equiv.Perm ι) : p τ = d * matchingProduct α β τ := by
        rw [← congrFun hp τ]
        simp only [kernelMatchingProduct, hg, Finset.prod_mul_distrib, Equiv.prod_comp τ L,
          d, matchingProduct]
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq d (Fintype.card_pos_iff.mpr h)
      refine ⟨fun i => c * α i, fun j => c * β j, ?_⟩
      funext τ
      rw [hprofile τ]
      simp only [matchingProduct, ← mul_add, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, hc]

/-- The exact matching profiles of additive complex spectra form a closed set. -/
theorem isClosed_additive_matching_profiles :
    IsClosed {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ, matchingProduct a b = p} := by
  rw [additive_profiles_eq_rankTwo_matching_profiles]
  exact isClosed_rankTwo_matching_profiles

end MOC
