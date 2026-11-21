import MOC.Support
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice

/-! The analytic contact step for a supplied compactified curve. A holomorphic
gap function with nonnegative real part on the entire punctured curve would
have a bounded reciprocal transform and hence be constant. -/

open Filter Function Set
open scoped Manifold Topology

namespace MOC

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ, ℂ) 1 M]

/-- A bounded holomorphic function off finitely many points extends
holomorphically to the surface. -/
theorem exists_holomorphic_extension_off_finite {S : Set M} (hS : S.Finite)
    {f : M → ℂ} (hf : MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f Sᶜ)
    (R : ℝ) (hb : ∀ x ∈ Sᶜ, ‖f x‖ ≤ R) :
    ∃ F : M → ℂ, MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F ∧ EqOn F f Sᶜ := by
  classical
  let F (x : M) : ℂ := if x ∈ S then limUnder (𝓝[Sᶜ] x) f else f x
  have hopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  refine ⟨F, ?_, fun x hx => if_neg (show x ∉ S from hx)⟩
  intro x
  by_cases hx : x ∈ S
  · let e := extChartAt 𝓘(ℂ, ℂ) x
    let c := e x
    let T : Set ℂ := e.target ∩ e.symm ⁻¹' (S \ {x})ᶜ
    have hrange : range 𝓘(ℂ, ℂ) = univ :=
      ModelWithCorners.Boundaryless.range_eq_univ
    have hcenter : e.symm c = x := e.left_inv (mem_extChartAt_source x)
    have hT : T ∈ 𝓝 c := by
      have htarget : e.target ∈ 𝓝 c := by
        have h := extChartAt_target_mem_nhdsWithin (I := 𝓘(ℂ, ℂ)) x
        rw [hrange, nhdsWithin_univ] at h
        exact h
      have hothers : IsOpen ((S \ {x})ᶜ) := hS.diff.isClosed.isOpen_compl
      have hxothers : e.symm c ∈ (S \ {x})ᶜ := by simp [hcenter]
      exact inter_mem htarget
        ((continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) x).preimage_mem_nhds
          (hothers.mem_nhds hxothers))
    have hlocal (z : ℂ) (hz : z ∈ T) : e.symm z ∈ Sᶜ ↔ z ≠ c := by
      constructor
      · intro hn he
        exact hn (by rw [he, hcenter]; exact hx)
      · intro hn hzS
        have hne : e.symm z ≠ x := by
          intro he
          apply hn
          calc
            z = e (e.symm z) := (e.right_inv hz.1).symm
            _ = c := congrArg e he
        exact hz.2 ⟨hzS, by simpa only [mem_singleton_iff] using hne⟩
    have hd : DifferentiableOn ℂ (f ∘ e.symm) (T \ {c}) := by
      intro z hz
      have hzS := (hlocal z hz.1).2 (by simpa only [mem_singleton_iff] using hz.2)
      have hsource : e.symm z ∈ (chartAt ℂ x).source := by
        rw [← extChartAt_source 𝓘(ℂ, ℂ) x]
        exact e.map_target hz.1.1
      have h := (mdifferentiableAt_iff_source_of_mem_source
        (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) hsource).1
        (hf.mdifferentiableAt (hopen.mem_nhds hzS))
      change MDifferentiableWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (f ∘ e.symm)
        (range 𝓘(ℂ, ℂ)) (e (e.symm z)) at h
      rw [hrange, mdifferentiableWithinAt_univ, e.right_inv hz.1.1] at h
      exact h.differentiableAt.differentiableWithinAt
    have hbound : BddAbove (norm ∘ (f ∘ e.symm) '' (T \ {c})) := by
      refine ⟨R, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hb _ ((hlocal z hz.1).2 (by simpa only [mem_singleton_iff] using hz.2))
    have hnhds : 𝓝[e.symm ⁻¹' Sᶜ] c = 𝓝[≠] c := by
      apply nhdsWithin_eq_iff_eventuallyEq.mpr
      filter_upwards [hT] with z hz
      apply propext
      simpa only [mem_preimage, mem_compl_iff, mem_singleton_iff] using hlocal z hz
    have hmap : map e.symm (𝓝[≠] c) = 𝓝[Sᶜ] x := by
      have h := map_extChartAt_symm_nhdsWithin (I := 𝓘(ℂ, ℂ)) (s := Sᶜ) x
      rw [hrange, inter_univ] at h
      change map e.symm (𝓝[e.symm ⁻¹' Sᶜ] c) = 𝓝[Sᶜ] x at h
      rwa [hnhds] at h
    have hlim :
        limUnder (𝓝[≠] c) (f ∘ e.symm) = limUnder (𝓝[Sᶜ] x) f := by
      unfold limUnder
      rw [← Filter.map_map, hmap]
    apply (mdifferentiableAt_iff_source_of_mem_source (I := 𝓘(ℂ, ℂ))
      (I' := 𝓘(ℂ, ℂ)) (mem_chart_source ℂ x)).2
    rw [hrange, mdifferentiableWithinAt_univ, mdifferentiableAt_iff_differentiableAt]
    change DifferentiableAt ℂ (F ∘ e.symm) c
    have hupdate := Complex.differentiableOn_update_limUnder_of_bddAbove hT hd hbound
    apply (hupdate.differentiableAt hT).congr_of_eventuallyEq
    filter_upwards [hT] with z hz
    by_cases hzc : z = c
    · subst z
      simp only [Function.comp_apply, hcenter, F, if_pos hx, update_self, hlim]
    · have hzS : e.symm z ∉ S := (hlocal z hz).2 hzc
      simp only [Function.comp_apply, F, if_neg hzS, update_of_ne hzc]
  · apply (hf.mdifferentiableAt (hopen.mem_nhds (show x ∈ Sᶜ from hx))).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds (show x ∈ Sᶜ from hx)] with y hy
    exact if_neg (show y ∉ S from hy)

variable [CompactSpace M] [PreconnectedSpace M]

/-- A holomorphic function on the complement of a finite set in a compact
connected complex surface cannot be nonconstant and take all its values
in the closed right half-plane. -/
theorem eqOn_of_re_nonneg_off_finite {S : Set M} (hS : S.Finite)
    {f : M → ℂ} (hf : MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f Sᶜ)
    (hre : ∀ x ∈ Sᶜ, 0 ≤ (f x).re) {x y : M} (hx : x ∈ Sᶜ) (hy : y ∈ Sᶜ) :
    f x = f y := by
  let g (x : M) := (1 + f x)⁻¹
  have hopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  have hpos (x : M) (hx : x ∈ Sᶜ) : 1 ≤ (1 + f x).re := by
    simpa only [Complex.add_re, Complex.one_re, add_zero] using add_le_add_left (hre x hx) 1
  have hg : MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) g Sᶜ := by
    intro z hz
    have hn : (1 + f z : ℂ) ≠ 0 := by
      intro h
      have h' := hpos z hz
      rw [h, Complex.zero_re] at h'
      exact (not_le_of_gt zero_lt_one) h'
    have hd : DifferentiableAt ℂ (fun w : ℂ => (1 + w)⁻¹) (f z) :=
      (differentiableAt_id.const_add (1 : ℂ)).inv hn
    have hcomp := hd.mdifferentiableAt.comp z (hf.mdifferentiableAt (hopen.mem_nhds hz))
    exact hcomp.mdifferentiableWithinAt
  have hbounded (z : M) (hz : z ∈ Sᶜ) : ‖g z‖ ≤ 1 := by
    change ‖(1 + f z)⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ ((hpos z hz).trans (Complex.re_le_norm _))
  obtain ⟨G, hG, hEq⟩ := exists_holomorphic_extension_off_finite hS hg 1 hbounded
  have he : g x = g y := (hEq hx).symm.trans ((hG.apply_eq_of_compactSpace x y).trans (hEq hy))
  have he' : 1 + f x = 1 + f y := by
    simpa only [g, inv_inv] using congrArg (fun z : ℂ => z⁻¹) he
  exact add_left_cancel he'

/-- On a supplied compactified curve, a finite family of initially positive
gaps acquires a zero while the other gaps stay nonnegative, provided one
gap function varies on the connected punctured curve. -/
theorem exists_new_contact_on_curve {ι : Type*} (J : Finset ι) {S : Set M} (hS : S.Finite)
    (hconn : IsPreconnected Sᶜ) (H : ι → M → ℂ)
    (hhol : ∀ i ∈ J, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (H i) Sᶜ)
    {x₀ : M} (hx₀ : x₀ ∈ Sᶜ) (hstart : ∀ i ∈ J, 0 < (H i x₀).re)
    (hvar : ∃ i ∈ J, ∃ x ∈ Sᶜ, ∃ y ∈ Sᶜ, H i x ≠ H i y) :
    ∃ z ∈ Sᶜ, (∀ i ∈ J, 0 ≤ (H i z).re) ∧ ∃ i ∈ J, (H i z).re = 0 := by
  obtain ⟨i, hi, x, hx, y, hy, hxy⟩ := hvar
  have hnegative : ∃ w ∈ Sᶜ, (H i w).re < 0 := by
    by_contra! h
    exact hxy (eqOn_of_re_nonneg_off_finite hS (hhol i hi) h hx hy)
  obtain ⟨w, hw, hwi⟩ := hnegative
  let Jne : J.Nonempty := ⟨i, hi⟩
  let m (z : M) : ℝ := J.inf' Jne (fun j => (H j z).re)
  have hm : ContinuousOn m Sᶜ :=
    ContinuousOn.finset_inf'_apply (f := fun j z => (H j z).re) Jne
      (fun j hj => Complex.continuous_re.comp_continuousOn (hhol j hj).continuousOn)
  have hmw : m w < 0 := (Finset.inf'_lt_iff Jne).2 ⟨i, hi, hwi⟩
  have hm₀ : 0 < m x₀ := (Finset.lt_inf'_iff Jne).2 hstart
  have hz : (0 : ℝ) ∈ m '' Sᶜ :=
    (hconn.image _ hm).Icc_subset ⟨w, hw, rfl⟩ ⟨x₀, hx₀, rfl⟩ ⟨hmw.le, hm₀.le⟩
  obtain ⟨z, hzS, hmz⟩ := hz
  have hzle : ∀ j ∈ J, 0 ≤ (H j z).re :=
    (Finset.le_inf'_iff Jne (fun j => (H j z).re)).1 (show 0 ≤ m z from hmz.ge)
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' Jne (fun k => (H k z).re)
  exact ⟨z, hzS, hzle, j, hj, he.symm.trans hmz⟩

open scoped BigOperators

/-- The spectral contact step preserves every old contact and the strict
determinant support gap on a supplied compactified deformation curve. -/
theorem exists_new_matching_contact_on_curve {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Set M} (hS : S.Finite) (hconn : IsPreconnected Sᶜ)
    (a b : M → ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (r : Equiv.Perm ι)
    (J : Finset (Equiv.Perm ι))
    (hhol : ∀ σ ∈ J, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun x => η * (matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) σ)) Sᶜ)
    (hold : ∀ x ∈ Sᶜ, ∀ σ ∉ J, matchingGap (a x) (b x) η r σ = 0)
    {g : ℝ}
    (hgap : ∀ x ∈ Sᶜ,
      (η * (determinantValue (a x) (b x) U - matchingProduct (a x) (b x) r)).re = g)
    (hg : 0 < g)
    {x₀ : M} (hx₀ : x₀ ∈ Sᶜ) (hstart : ∀ σ ∈ J, 0 < matchingGap (a x₀) (b x₀) η r σ)
    (hvar : ∃ σ ∈ J, ∃ x ∈ Sᶜ, ∃ y ∈ Sᶜ,
      η * (matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) σ) ≠
        η * (matchingProduct (a y) (b y) r - matchingProduct (a y) (b y) σ)) :
    ∃ z ∈ Sᶜ, (∀ σ, 0 ≤ matchingGap (a z) (b z) η r σ) ∧
      (∀ σ ∉ J, matchingGap (a z) (b z) η r σ = 0) ∧
      (∃ σ ∈ J, matchingGap (a z) (b z) η r σ = 0) ∧
      (η * determinantValue (a z) (b z) U).re - (η * matchingProduct (a z) (b z) r).re = g ∧
      ∀ σ, (η * matchingProduct (a z) (b z) σ).re < (η * determinantValue (a z) (b z) U).re := by
  let H (σ : Equiv.Perm ι) (x : M) :=
    η * (matchingProduct (a x) (b x) r - matchingProduct (a x) (b x) σ)
  have hH (σ : Equiv.Perm ι) (x : M) :
      (H σ x).re = matchingGap (a x) (b x) η r σ := by
    simp only [H, matchingGap, mul_sub, Complex.sub_re]
  obtain ⟨z, hz, hnonneg, j, hj, hjz⟩ := exists_new_contact_on_curve J hS hconn H hhol hx₀
    (by simpa only [hH] using hstart) hvar
  have hall (σ : Equiv.Perm ι) : 0 ≤ matchingGap (a z) (b z) η r σ := by
    by_cases hσ : σ ∈ J
    · exact (hH σ z) ▸ hnonneg σ hσ
    · exact (hold z hz σ hσ).ge
  have hg' : (η * determinantValue (a z) (b z) U).re -
      (η * matchingProduct (a z) (b z) r).re = g := by
    simpa only [mul_sub, Complex.sub_re] using hgap z hz
  have hrlt : (η * matchingProduct (a z) (b z) r).re <
      (η * determinantValue (a z) (b z) U).re := by
    apply sub_pos.mp
    rwa [hg']
  exact ⟨z, hz, hall, hold z hz, ⟨j, hj, (hH j z).symm.trans hjz⟩, hg',
    fun σ => (sub_nonneg.mp (hall σ)).trans_lt hrlt⟩

end

end MOC
