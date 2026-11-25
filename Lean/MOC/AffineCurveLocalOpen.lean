import MOC.AffineGapCover
import Mathlib.Analysis.NormedSpace.HomeomorphBall

/-! A nonconstant regular coordinate on a finite prime affine curve is
locally open at every affine point, including ramified or singular points.
This one-dimensional proof uses the regular cover and compact boundaries,
rather than a higher-dimensional analytic open-mapping theorem. Compare
Joiţa–Tibăr, DOI: 10.4310/ARKIV.2021.v59.n2.a5. -/

open Set MvPolynomial Filter
open scoped Topology

namespace MOC

private theorem punctured_complex_ball_preconnected (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (Metric.ball c r \ {c}) := by
  let e : PartialHomeomorph ℂ ℂ := PartialHomeomorph.univBall c r
  have hsource : e.source = univ := PartialHomeomorph.univBall_source c r
  have htarget : e.target = Metric.ball c r := PartialHomeomorph.univBall_target c hr
  have hzero : e 0 = c := PartialHomeomorph.univBall_apply_zero c r
  have hdim : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat
  have he : e '' (({0} : Set ℂ)ᶜ) = Metric.ball c r \ {c} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hmem := e.map_source (show x ∈ e.source by rw [hsource]; trivial)
      refine ⟨htarget ▸ hmem, ?_⟩
      intro h
      have heq : e x = e 0 := (Set.mem_singleton_iff.mp h).trans hzero.symm
      exact hx (Set.mem_singleton_iff.mpr (e.injOn (by rw [hsource]; trivial)
        (by rw [hsource]; trivial) heq))
    · rintro ⟨hy,hyne⟩
      have hy' : y ∈ e.target := htarget.symm ▸ hy
      refine ⟨e.symm y, ?_, e.right_inv hy'⟩
      intro heq
      have hyc : y = c := by rw [← e.right_inv hy', Set.mem_singleton_iff.mp heq, hzero]
      exact hyne (Set.mem_singleton_iff.mpr hyc)
  rw [← he]
  exact ((isPathConnected_compl_singleton_of_one_lt_rank hdim (0 : ℂ)).image
    (PartialHomeomorph.continuous_univBall c r)).isConnected.isPreconnected

/-- The entire image of an arbitrarily small neighborhood of a possibly
exceptional point contains a neighborhood of its polynomial value. -/
theorem affine_curve_varying_coordinate_mem_nhds_image
    {σ : Type*} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f) (t g : MvPolynomial σ ℂ)
    (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hv : ∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g)
    (x : zeroLocus Q) {W : Set (zeroLocus Q)} (hW : W ∈ 𝓝 x) :
    (fun y : zeroLocus Q => eval y.val g) '' W ∈ 𝓝 (eval x.val g) := by
  classical
  let G (y : zeroLocus Q) := eval y.val g
  let c := G x
  have hcG : Continuous G := g.continuous_eval.comp continuous_subtype_val
  have hQ : IsClosed (zeroLocus Q) := by
    have he : zeroLocus Q = ⋂ p : Q, {z | eval z p.val = 0} := by
      ext z
      simp only [mem_iInter,mem_setOf_eq]
      exact ⟨fun h p => h p.val p.property, fun h p hp => h ⟨p,hp⟩⟩
    rw [he]
    exact isClosed_iInter fun p => isClosed_eq p.val.continuous_eval continuous_const
  letI : ProperSpace (zeroLocus Q) := by
    refine ⟨fun z r => ?_⟩
    exact hQ.isClosedEmbedding_subtypeVal.isInducing.isCompact_preimage
      (by simpa only [Subtype.range_coe] using hQ) (isCompact_closedBall z.val r)
  obtain ⟨B,hB,hcov,_⟩ := affineGapCharts σ Q f hf hfi t g ht hv
  let E := {z : zeroLocus Q | G z ∈ Bᶜ}
  let p : E → (↑Bᶜ : Type) := fun z => ⟨G z.val,z.property⟩
  have hopen : IsOpenMap (fun z : E => G z.val) :=
    hB.isClosed.isOpen_compl.isOpenMap_subtype_val.comp (show IsCoveringMap p from hcov).isOpenMap
  let S := {y : zeroLocus Q | G y = c} \ {x}
  have hS : S.Finite := (finite_points_over_varying_affine_coordinate Q f hf hfi t g ht hv c).subset
    inter_subset_left
  have hxS : x ∈ Sᶜ := by simp [S]
  obtain ⟨r₀,hr₀,hsmall⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hW (hS.isClosed.isOpen_compl.mem_nhds hxS))
  let r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  let K := Metric.closedBall x r
  let A := Metric.ball x r
  let J := G '' K
  have hK : K ⊆ W ∩ Sᶜ :=
    (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hsmall
  have hJ : IsClosed J := ((isCompact_closedBall x r).image hcG).isClosed
  let L := G '' Metric.sphere x r
  have hL : IsClosed L := ((isCompact_sphere x r).image hcG).isClosed
  have hcL : c ∈ Lᶜ := by
    rintro ⟨y,hy,hyc⟩
    have hyx : y ≠ x := fun he => hr.ne' (by simpa [he] using (Metric.mem_sphere.mp hy).symm)
    have hyK : y ∈ K := (Metric.mem_sphere.mp hy).le
    exact (hK hyK).2 ⟨hyc,hyx⟩
  let B' := B \ {c}
  have hB' : B'.Finite := hB.subset inter_subset_left
  have hcB : c ∈ B'ᶜ := by simp [B']
  obtain ⟨δ,hδ,hD⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hL.isOpen_compl.mem_nhds hcL) (hB'.isClosed.isOpen_compl.mem_nhds hcB))
  let D := Metric.ball c δ \ {c}
  have hDo : IsOpen D := Metric.isOpen_ball.sdiff isClosed_singleton
  let q : E → ℂ := fun z => G z.val
  let V := q '' ((Subtype.val : E → zeroLocus Q) ⁻¹' A)
  have hV : IsOpen V := hopen _ (Metric.isOpen_ball.preimage continuous_subtype_val)
  have hVJ : V ⊆ J := by
    rintro z ⟨y,hy,rfl⟩
    exact ⟨y.val,Metric.ball_subset_closedBall hy,rfl⟩
  have hJV : J ∩ D ⊆ V := by
    rintro z ⟨⟨y,hy,rfl⟩,hz⟩
    have hyA : y ∈ A := by
      by_cases hyA : y ∈ A
      · exact hyA
      · exfalso
        have hsph : y ∈ Metric.sphere x r := by rw [← Metric.closedBall_diff_ball]; exact ⟨hy,hyA⟩
        exact (hD hz.1).1 ⟨y,hsph,rfl⟩
    have hyB : G y ∈ Bᶜ := by
      intro hyB'
      exact (hD hz.1).2 ⟨hyB',hz.2⟩
    exact ⟨⟨y,hyB⟩,hyA,rfl⟩
  have hnon : (D ∩ V).Nonempty := by
    have hden := dense_affine_varying_coordinate_off_finite Q f hf hfi t g ht hv
      (hS := hB.insert c)
    obtain ⟨y,⟨hyA,hyD⟩,hy⟩ := hden.inter_open_nonempty
      (A ∩ G ⁻¹' Metric.ball c δ) (Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage hcG))
      ⟨x,Metric.mem_ball_self hr,Metric.mem_ball_self hδ⟩
    have hyB : G y ∉ B := fun hb => hy (Set.mem_insert_of_mem _ hb)
    have hyc : G y ∉ ({c} : Set ℂ) := fun hz => hy (Set.mem_insert_iff.mpr (Or.inl hz))
    exact ⟨G y,⟨hyD,hyc⟩,⟨⟨y,hyB⟩,hyA,rfl⟩⟩
  have hfull : D ⊆ V := (punctured_complex_ball_preconnected c hδ).subset_of_closure_inter_subset
    hV hnon (fun z hz => hJV ⟨hJ.closure_subset_iff.mpr hVJ hz.1,hz.2⟩)
  apply Metric.mem_nhds_iff.mpr
  refine ⟨δ,hδ,fun z hz => ?_⟩
  by_cases he : z = c
  · exact ⟨x,mem_of_mem_nhds hW,he.symm⟩
  · obtain ⟨y,hy,hye⟩ := hVJ (hfull ⟨hz,he⟩)
    exact ⟨y,(hK hy).1,hye⟩

end MOC
