import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Lattice

/-! Compact transport duality for continuous real costs, using positive linear functionals. -/

namespace MOC

open MeasureTheory

noncomputable section

private theorem compactTransport_monotone {X : Type*} [TopologicalSpace X]
    (L : C(X, ℝ) →ₗ[ℝ] ℝ) (hL : ∀ f, 0 ≤ f → 0 ≤ L f) : Monotone L := by
  intro f g hfg
  have h := hL (g - f) (sub_nonneg.mpr hfg)
  rwa [map_sub, sub_nonneg] at h

/-- If every sum of continuous marginal potentials that majorizes the cost has value
at least `z`, a positive normalized joint functional with the given marginals gives
the cost value at least `z`. -/
theorem exists_compact_transport_functional
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y]
    (Lx : C(X, ℝ) →ₗ[ℝ] ℝ) (Ly : C(Y, ℝ) →ₗ[ℝ] ℝ)
    (hx : ∀ f, 0 ≤ f → 0 ≤ Lx f) (hy : ∀ f, 0 ≤ f → 0 ≤ Ly f)
    (hx1 : Lx 1 = 1) (hy1 : Ly 1 = 1) (c : C(X × Y, ℝ)) (z : ℝ)
    (hz : ∀ (u : C(X, ℝ)) (v : C(Y, ℝ)),
      (∀ p : X × Y, c p ≤ u p.1 + v p.2) → z ≤ Lx u + Ly v) :
    ∃ L : C(X × Y, ℝ) →ₗ[ℝ] ℝ, (∀ f, 0 ≤ f → 0 ≤ L f) ∧ L 1 = 1 ∧
      (∀ u : C(X, ℝ), L (u.comp ⟨Prod.fst, continuous_fst⟩) = Lx u) ∧
      (∀ v : C(Y, ℝ), L (v.comp ⟨Prod.snd, continuous_snd⟩) = Ly v) ∧ z ≤ L c := by
  let fstMap : C(X × Y, X) := ⟨Prod.fst, continuous_fst⟩
  let sndMap : C(X × Y, Y) := ⟨Prod.snd, continuous_snd⟩
  let A : C(X, ℝ) × C(Y, ℝ) →ₗ[ℝ] C(X × Y, ℝ) :=
    { toFun := fun uv => uv.1.comp fstMap + uv.2.comp sndMap
      map_add' := by
        intro u v
        ext p
        change (u.1 p.1 + v.1 p.1) + (u.2 p.2 + v.2 p.2) =
          (u.1 p.1 + u.2 p.2) + (v.1 p.1 + v.2 p.2)
        exact add_add_add_comm _ _ _ _
      map_smul' := by
        intro r u
        ext p
        change r * u.1 p.1 + r * u.2 p.2 = r * (u.1 p.1 + u.2 p.2)
        exact (mul_add _ _ _).symm }
  let m : C(X, ℝ) × C(Y, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun uv => Lx uv.1 + Ly uv.2
      map_add' := by
        intro u v
        change Lx (u.1 + v.1) + Ly (u.2 + v.2) = (Lx u.1 + Ly u.2) + (Lx v.1 + Ly v.2)
        rw [map_add, map_add, add_add_add_comm]
      map_smul' := by
        intro r u
        change Lx (r • u.1) + Ly (r • u.2) = r * (Lx u.1 + Ly u.2)
        simp only [map_smul, smul_eq_mul, mul_add] }
  have hconstX (r : ℝ) : Lx (r • (1 : C(X, ℝ))) = r := by
    rw [map_smul, hx1, smul_eq_mul, mul_one]
  have hconstY (r : ℝ) : Ly (r • (1 : C(Y, ℝ))) = r := by
    rw [map_smul, hy1, smul_eq_mul, mul_one]
  have hm (uv : C(X, ℝ) × C(Y, ℝ)) (huv : 0 ≤ A uv) : 0 ≤ m uv := by
    have hybound : (-Lx uv.1) • (1 : C(Y, ℝ)) ≤ uv.2 := by
      intro y
      have hxbound : (-uv.2 y) • (1 : C(X, ℝ)) ≤ uv.1 := by
        intro x
        have h : 0 ≤ uv.1 x + uv.2 y := huv (x, y)
        change -(uv.2 y) * 1 ≤ uv.1 x
        linarith only [h]
      have h := compactTransport_monotone Lx hx hxbound
      rw [hconstX] at h
      change -(Lx uv.1) * 1 ≤ uv.2 y
      linarith only [h]
    have h := compactTransport_monotone Ly hy hybound
    rw [hconstY] at h
    change 0 ≤ Lx uv.1 + Ly uv.2
    linarith only [h]
  have hker : LinearMap.ker A ≤ LinearMap.ker m := by
    intro uv huv
    have he := LinearMap.mem_ker.mp huv
    have hpos := hm uv (by simp only [he, le_rfl])
    have hneg := hm (-uv) (by simp only [map_neg, he, neg_zero, le_rfl])
    rw [map_neg, neg_nonneg] at hneg
    exact LinearMap.mem_ker.mpr (le_antisymm hneg hpos)
  let F : LinearMap.range A →ₗ[ℝ] ℝ :=
    ((LinearMap.ker A).liftQ m hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hF (uv : C(X, ℝ) × C(Y, ℝ)) : F ⟨A uv, LinearMap.mem_range_self A uv⟩ = m uv := by
    change (LinearMap.ker A).liftQ m hker (A.quotKerEquivRange.symm ⟨A uv, _⟩) = m uv
    rw [LinearMap.quotKerEquivRange_symm_apply_image] <;> rfl
  let d : C(X × Y, ℝ) := c - z • 1
  let S : ConvexCone ℝ C(X × Y, ℝ) :=
    { carrier := {f | ∃ r : ℝ, 0 ≤ r ∧ r • d ≤ f}
      smul_mem' := by
        rintro a ha f ⟨r, hr, hrf⟩
        refine ⟨a * r, mul_nonneg ha.le hr, ?_⟩
        intro p
        change (a * r) * d p ≤ a * f p
        have hp : r * d p ≤ f p := hrf p
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hp ha.le
      add_mem' := by
        rintro f ⟨r, hr, hrf⟩ g ⟨t, ht, htg⟩
        refine ⟨r + t, add_nonneg hr ht, ?_⟩
        intro p
        change (r + t) * d p ≤ f p + g p
        rw [add_mul]
        exact add_le_add (hrf p) (htg p) }
  have hS (w : LinearMap.range A) (hw : (w : C(X × Y, ℝ)) ∈ S) : 0 ≤ F w := by
    obtain ⟨uv, huv⟩ := LinearMap.mem_range.mp w.property
    have he : w = ⟨A uv, LinearMap.mem_range_self A uv⟩ := Subtype.ext huv.symm
    obtain ⟨r, hr, hrs⟩ := hw
    change r • d ≤ (w : C(X × Y, ℝ)) at hrs
    rw [← huv] at hrs
    rw [he, hF]
    by_cases hr0 : r = 0
    · exact hm uv (by simpa only [hr0, zero_smul] using hrs)
    have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let u := r⁻¹ • uv.1 + z • (1 : C(X, ℝ))
    let v := r⁻¹ • uv.2
    have hmajor (p : X × Y) : c p ≤ u p.1 + v p.2 := by
      have hp : r * (c p - z * 1) ≤ uv.1 p.1 + uv.2 p.2 := hrs p
      change c p ≤ r⁻¹ * uv.1 p.1 + z * 1 + r⁻¹ * uv.2 p.2
      have hh := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hr)
      rw [← mul_assoc, inv_mul_cancel₀ hr0, one_mul, mul_add] at hh
      linarith only [hh]
    have hbound := hz u v hmajor
    simp only [u, v, map_add, map_smul, hx1, smul_eq_mul, mul_one] at hbound
    have hprod : 0 ≤ r⁻¹ * (Lx uv.1 + Ly uv.2) := by
      rw [mul_add]
      linarith only [hbound]
    exact nonneg_of_mul_nonneg_right hprod (inv_pos.mpr hrp)
  have hdense (f : C(X × Y, ℝ)) :
      ∃ w : LinearMap.range A, (w : C(X × Y, ℝ)) + f ∈ S := by
    let uv : C(X, ℝ) × C(Y, ℝ) := (‖f‖ • 1, 0)
    refine ⟨⟨A uv, LinearMap.mem_range_self A uv⟩, 0, le_rfl, ?_⟩
    rw [zero_smul]
    intro p
    change 0 ≤ ‖f‖ * 1 + 0 + f p
    linarith only [f.neg_norm_le_apply p]
  let P : C(X × Y, ℝ) →ₗ.[ℝ] ℝ := ⟨LinearMap.range A, F⟩
  obtain ⟨L, hext, hpos⟩ := riesz_extension S P hS hdense
  have hLadd (uv : C(X, ℝ) × C(Y, ℝ)) : L (A uv) = m uv :=
    (hext (⟨A uv, LinearMap.mem_range_self A uv⟩ : LinearMap.range A)).trans (hF uv)
  have hLx (u : C(X, ℝ)) : L (u.comp fstMap) = Lx u := by
    have h := hLadd (u, 0)
    have he : (0 : C(Y, ℝ)).comp sndMap = 0 := by ext p; rfl
    change L (u.comp fstMap + (0 : C(Y, ℝ)).comp sndMap) = Lx u + Ly 0 at h
    simpa only [he, add_zero, map_zero] using h
  have hLy (v : C(Y, ℝ)) : L (v.comp sndMap) = Ly v := by
    have h := hLadd (0, v)
    have he : (0 : C(X, ℝ)).comp fstMap = 0 := by ext p; rfl
    change L ((0 : C(X, ℝ)).comp fstMap + v.comp sndMap) = Lx 0 + Ly v at h
    simpa only [he, zero_add, map_zero] using h
  have hL1 : L 1 = 1 := by
    simpa only [ContinuousMap.one_comp, hx1] using hLx 1
  refine ⟨L, ?_, hL1, hLx, hLy, ?_⟩
  · intro f hf
    exact hpos f ⟨0, le_rfl, by simpa only [zero_smul] using hf⟩
  · have hd : d ∈ S := ⟨1, zero_le_one, by simp only [one_smul, le_rfl]⟩
    have h := hpos d hd
    change 0 ≤ L (c - z • 1) at h
    rw [map_sub, map_smul, hL1, smul_eq_mul, mul_one] at h
    exact sub_nonneg.mp h

section Measure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Integration against a finite measure defines a real linear functional
on continuous functions on a compact space. -/
def compactTransportIntegral (μ : Measure X) [IsFiniteMeasure μ] : C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := by
    have hf : Integrable f μ := by
      rw [← integrableOn_univ]
      exact ContinuousOn.integrableOn_compact isCompact_univ f.continuous.continuousOn
    have hg : Integrable g μ := by
      rw [← integrableOn_univ]
      exact ContinuousOn.integrableOn_compact isCompact_univ g.continuous.continuousOn
    exact integral_add hf hg
  map_smul' r f := integral_smul r f

@[simp] theorem compactTransportIntegral_apply (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℝ)) : compactTransportIntegral μ f = ∫ x, f x ∂μ := rfl

theorem compactTransportIntegral_nonneg (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ compactTransportIntegral μ f :=
  integral_nonneg fun x => hf x

@[simp] theorem compactTransportIntegral_one (μ : Measure X) [IsProbabilityMeasure μ] :
    compactTransportIntegral μ 1 = 1 := by
  change (∫ _ : X, (1 : ℝ) ∂μ) = 1
  simp

end Measure

end

end MOC
