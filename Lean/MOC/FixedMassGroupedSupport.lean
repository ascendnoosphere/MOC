import MOC.GroupedPencil

/-! Exact dual support for fixed grouped masses in the one-entry pencil.
The criterion tests the prescribed masses, not existence with free
masses, and does not assert the physical masses are always feasible. -/

open BigOperators Finset

namespace MOC
noncomputable section

/-- For fixed nonnegative masses, the two prescribed grouped moments are
feasible exactly when every real projection lies below the sum of the
group support values. The independent finite choices on the right can
each be made at a maximizing label. -/
theorem fixedMassGroupedSupport_iff
    {I P : Type*} [Fintype I] [Fintype P] (label : P → I) (hl : Function.Surjective label)
    (s : P → ℂ) (a : I → ℂ) (m : I → ℝ) (hm : ∀ i, 0 ≤ m i) (A B : ℂ) :
    (∃ z : I → ℂ, (∀ i, z i ∈ convexHull ℝ (s '' {p | label p = i})) ∧
      (∑ i, m i • z i) = A ∧ (∑ i, m i • (a i * z i)) = B) ↔
    ∀ u v : ℂ, ∃ p : I → P, (∀ i, label (p i) = i) ∧
      (u * A + v * B).re ≤ ∑ i, m i * (((u + v * a i) * s (p i)).re) := by
  classical
  let K (i : I) := convexHull ℝ (s '' {p | label p = i})
  let F : (I → ℂ) →ₗ[ℝ] ℂ × ℂ :=
    LinearMap.prod (∑ i, m i • LinearMap.proj i)
      (∑ i, m i • ((LinearMap.mulLeft ℝ (a i)).comp (LinearMap.proj i)))
  let C := F '' Set.pi Set.univ K
  have hF (z : I → ℂ) :
      F z = (∑ i, m i • z i, ∑ i, m i • (a i * z i)) := by
    ext <;> simp [F, LinearMap.mulLeft_apply]
  have hmem : (A,B) ∈ C ↔
      ∃ z : I → ℂ, (∀ i, z i ∈ K i) ∧ (∑ i, m i • z i) = A ∧
        (∑ i, m i • (a i * z i)) = B := by
    simp only [C, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies, hF, Prod.mk.injEq]
  have hscore (u v : ℂ) (z : I → ℂ) :
      (u * (F z).1 + v * (F z).2).re = ∑ i, m i * (((u + v * a i) * z i).re) := by
    rw [hF]
    simp only [mul_sum, ← Finset.sum_add_distrib, Complex.re_sum, Complex.real_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show u * ((m i : ℂ) * z i) + v * ((m i : ℂ) * (a i * z i)) =
      (m i : ℂ) * ((u + v * a i) * z i) by ring, Complex.re_ofReal_mul]
  rw [← hmem]
  constructor
  · intro h u v
    obtain ⟨z,hz,hzAB⟩ := h
    let Q (i : I) : Finset P := univ.filter (fun p => label p = i)
    have hchoose (i : I) : ∃ p ∈ Q i, ∀ q ∈ Q i,
        ((u + v * a i) * s q).re ≤ ((u + v * a i) * s p).re := by
      obtain ⟨p,hp⟩ := hl i
      exact Finset.exists_max_image (Q i) _ ⟨p, Finset.mem_filter.mpr ⟨mem_univ _,hp⟩⟩
    choose p hp hmax using hchoose
    refine ⟨p,fun i => (Finset.mem_filter.mp (hp i)).2,?_⟩
    change (u * (A, B).1 + v * (A, B).2).re ≤ _
    rw [← hzAB, hscore]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hm i)
    let L : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ (u + v * a i))
    change L (z i) ≤ L (s (p i))
    apply convexHull_min ?_ (convex_halfSpace_le L.isLinear _) (hz i (Set.mem_univ i))
    rintro _ ⟨q,hq,rfl⟩
    exact hmax i q (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩)
  · intro H
    apply Classical.byContradiction
    intro h
    have hcv : Convex ℝ C := (convex_pi (fun i _ => convex_convexHull ℝ _)).linear_image F
    have hk (i : I) : IsCompact (K i) :=
      ((Set.finite_univ.subset (Set.subset_univ {p | label p = i})).image s).isCompact_convexHull
    have hcp : IsCompact C := (isCompact_univ_pi hk).image F.continuous_of_finiteDimensional
    obtain ⟨f,b,hb,hx⟩ := geometric_hahn_banach_closed_point hcv hcp.isClosed h
    obtain ⟨u,v,hf⟩ := productFunctional f
    obtain ⟨p,hp,hle⟩ := H u v
    let z (i : I) := s (p i)
    have hz : F z ∈ C := by
      refine ⟨z,fun i _ => subset_convexHull ℝ _ ?_,rfl⟩
      exact ⟨p i,hp i,rfl⟩
    have hfz := hf (F z)
    rw [hscore u v z] at hfz
    rw [← hf (A,B), ← hfz] at hle
    exact (lt_irrefl _) (((hb _ hz).trans hx).trans_le hle)

end
end MOC
