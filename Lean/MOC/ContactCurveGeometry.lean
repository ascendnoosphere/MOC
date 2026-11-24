import MOC.RealizableContactKernels

/-! Fixed-pivot coordinates and density for the exact matching-profile variety. -/

open Filter
open scoped BigOperators Topology

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem anchor_rank_one_chart_entry_eq_quotient
    (o i j : ι) (hi : i ≠ o) (hj : j ≠ o) (d : ℂ) (u v : ι → ℂ)
    (hu : u o = 0) (hv : v o = 0) (p : Equiv.Perm ι → ℂ)
    (hp : ∀ σ, p σ = d * ∏ k, (1 + u (σ k) * v k))
    (hnz : ∀ σ, p σ ≠ 0) :
    1 + u i * v j = p (Equiv.swap j i) / p (Equiv.swap j i * Equiv.swap o j) := by
  have hp' (σ : Equiv.Perm ι) : p σ = d * kernelMatchingProduct (anchoredMatchingKernel u v) σ := by
    simpa only [kernelMatchingProduct, anchoredMatchingKernel, Matrix.of_apply] using hp σ
  have he := anchored_entry_eq_profile_ratio u v o j hj hu hv (Equiv.swap j i)
    (Equiv.swap_apply_of_ne_of_ne hj.symm hi.symm) d
    ((hp' _).symm.trans_ne (hnz _))
  rw [← hp', ← hp'] at he
  simpa only [anchoredMatchingKernel, Matrix.of_apply, Equiv.swap_apply_left] using he

omit [Fintype ι] [DecidableEq ι] in
/-- Both normalized factors can be read off from their nonzero-pivot
block, so normalizing the pivot eliminates the factorization redundancy. -/
theorem pivot_normalized_rank_one_chart_injective
    (i₀ j₀ : ι) (u₁ v₁ u₂ v₂ : ι → ℂ)
    (h₁ : u₁ i₀ = 1) (h₂ : u₂ i₀ = 1) (h₀ : v₁ j₀ ≠ 0)
    (h : ∀ i j, u₁ i * v₁ j = u₂ i * v₂ j) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  have hv : v₁ = v₂ := by
    funext j
    simpa only [h₁, h₂, one_mul] using h i₀ j
  refine ⟨funext (fun i => mul_right_cancel₀ h₀ ?_), hv⟩
  rw [h i j₀, hv]

/-- The anchored matching chart is injective after fixing the row pivot,
on the locus where every matching coordinate and one column pivot is nonzero. -/
theorem pivot_normalized_matching_profile_chart_injective
    (o i₀ j₀ : ι) (d₁ d₂ : ℂ) (u₁ v₁ u₂ v₂ : ι → ℂ)
    (hu₁ : u₁ o = 0) (hv₁ : v₁ o = 0) (hu₂ : u₂ o = 0) (hv₂ : v₂ o = 0)
    (h₁ : u₁ i₀ = 1) (h₂ : u₂ i₀ = 1) (h₀ : v₁ j₀ ≠ 0)
    (p : Equiv.Perm ι → ℂ)
    (hp₁ : ∀ σ, p σ = d₁ * ∏ k, (1 + u₁ (σ k) * v₁ k))
    (hp₂ : ∀ σ, p σ = d₂ * ∏ k, (1 + u₂ (σ k) * v₂ k))
    (hnz : ∀ σ, p σ ≠ 0) :
    d₁ = d₂ ∧ u₁ = u₂ ∧ v₁ = v₂ := by
  have h (i j : ι) : u₁ i * v₁ j = u₂ i * v₂ j := by
    by_cases hi : i = o
    · simp [hi, hu₁, hu₂]
    by_cases hj : j = o
    · simp [hj, hv₁, hv₂]
    apply add_left_cancel (a := (1 : ℂ))
    rw [anchor_rank_one_chart_entry_eq_quotient o i j hi hj d₁ u₁ v₁ hu₁ hv₁ p hp₁ hnz,
      anchor_rank_one_chart_entry_eq_quotient o i j hi hj d₂ u₂ v₂ hu₂ hv₂ p hp₂ hnz]
  obtain ⟨hu, hv⟩ := pivot_normalized_rank_one_chart_injective i₀ j₀ u₁ v₁ u₂ v₂ h₁ h₂ h₀ h
  subst u₂ v₂
  have hprod : (∏ k, (1 + u₁ ((1 : Equiv.Perm ι) k) * v₁ k)) ≠ 0 :=
    right_ne_zero_of_mul (fun h => hnz 1 ((hp₁ 1).trans h))
  exact ⟨mul_right_cancel₀ hprod ((hp₁ 1).symm.trans (hp₂ 1)), rfl, rfl⟩

/-- The nonvanishing chart locus is Euclidean-dense in the exact profile
image. A common additive perturbation of one spectrum suffices. -/
theorem closure_nonzero_matching_profiles :
    closure {p : Equiv.Perm ι → ℂ |
      (∃ a b : ι → ℂ, matchingProduct a b = p) ∧ ∀ σ, p σ ≠ 0} =
    {p : Equiv.Perm ι → ℂ | ∃ a b : ι → ℂ, matchingProduct a b = p} := by
  apply Set.Subset.antisymm
  · exact isClosed_additive_matching_profiles.closure_subset_iff.mpr fun _ h => h.1
  · rintro _ ⟨a, b, rfl⟩
    let F (t : ℂ) := matchingProduct (fun i => a i + t) b
    have hcont : Continuous F := by
      apply continuous_pi
      intro σ
      change Continuous (fun t : ℂ => ∏ j, (a (σ j) + t + b j))
      exact continuous_finset_prod _ fun j _ => (continuous_const.add continuous_id).add continuous_const
    have hlim : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (matchingProduct a b)) := by
      have hzero : F 0 = matchingProduct a b := by
        simp [F]
      rw [← hzero]
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hlim
    have hne (i j : ι) : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ), a i + t + b j ≠ 0 := by
      by_cases h : a i + b j = 0
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : t ≠ 0 := ht
        simpa [add_right_comm (a i) t (b j), h] using ht'
      · have hc : Continuous (fun t : ℂ => a i + t + b j) :=
          (continuous_const.add continuous_id).add continuous_const
        have ho := isOpen_ne_fun hc (continuous_const (y := (0 : ℂ)))
        have he : ∀ᶠ t : ℂ in 𝓝 (0 : ℂ), a i + t + b j ≠ 0 :=
          ho.mem_nhds (x := (0 : ℂ)) (by simpa using h)
        exact he.filter_mono nhdsWithin_le_nhds
    have he : ∀ᶠ t : ℂ in 𝓝[≠] (0 : ℂ), ∀ i j, a i + t + b j ≠ 0 :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hne i j
    filter_upwards [he] with t ht
    refine ⟨⟨fun i => a i + t, b, rfl⟩, fun σ => ?_⟩
    exact Finset.prod_ne_zero_iff.mpr fun j _ => ht (σ j) j

end MOC
