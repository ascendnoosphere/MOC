import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! The strict weighted coordinate maximum principle on a secular chamber. -/

open BigOperators Finset Filter Set
open scoped Topology

namespace MOC

private theorem second_derivative_nonpos_at_local_max {f : ℝ → ℝ} {a b : ℝ}
    (hmax : IsLocalMax f a)
    (hnear : ∀ᶠ t in 𝓝 a, DifferentiableAt ℝ f t)
    (hsecond : HasDerivAt (deriv f) b a) :
    b ≤ 0 := by
  by_contra! hb
  have ha : deriv f a = 0 := hmax.deriv_eq_zero
  have hpositive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < deriv f (a + t) := by
    have h := hsecond.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hb)
    filter_upwards [h, self_mem_nhdsWithin] with t ht htpos
    have ht' : 0 < t := htpos
    have hmul : 0 < t⁻¹ * deriv f (a + t) := by
      simpa only [ha, sub_zero, smul_eq_mul] using ht
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr ht')).mp hmul
  have hshift : Tendsto (fun t : ℝ => a + t) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have hc : Continuous (fun t : ℝ => a + t) := continuous_const.add continuous_id
    have hc₀ : ContinuousAt (fun t : ℝ => a + t) 0 := hc.continuousAt
    simpa only [add_zero] using hc₀.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hregular : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      DifferentiableAt ℝ f (a + t) ∧ f (a + t) ≤ f a ∧ 0 < deriv f (a + t) :=
    (hshift.eventually hnear).and ((hshift.eventually hmax).and hpositive)
  obtain ⟨δ, hδ, hreg⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hregular
  let upper := a + δ / 2
  have hupper : a < upper := by dsimp only [upper]; linarith
  have hupper_shift : upper - a ∈ Ioo (0 : ℝ) δ := by
    constructor <;> dsimp only [upper] <;> linarith
  have hfield (x : ℝ) (hx : x ∈ Ioc a upper) :
      DifferentiableAt ℝ f x ∧ f x ≤ f a ∧ 0 < deriv f x := by
    have hxshift : x - a ∈ Ioo (0 : ℝ) δ :=
      ⟨sub_pos.mpr hx.1, (sub_le_sub_right hx.2 a).trans_lt hupper_shift.2⟩
    simpa only [add_sub_cancel] using hreg hxshift
  have hcont : ContinuousOn f (Icc a upper) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with he | hlt
    · subst x
      exact hnear.self_of_nhds.continuousAt.continuousWithinAt
    · exact (hfield x ⟨hlt, hx.2⟩).1.continuousAt.continuousWithinAt
  obtain ⟨c, hc, hs⟩ := exists_deriv_eq_slope f hupper hcont
    (fun x hx => (hfield x ⟨hx.1, hx.2.le⟩).1.differentiableWithinAt)
  have hstrict := (hfield c ⟨hc.1, hc.2.le⟩).2.2
  have hle := (hfield upper ⟨hupper, le_rfl⟩).2.1
  rw [hs] at hstrict
  exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle)
    (sub_nonneg.mpr hupper.le))) hstrict

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive weighted sum of pure second derivatives excludes an
interior maximum on any compact superlevel set above the boundary bound. -/
theorem weighted_coordinate_maximum_principle
    (f : (ι → ℝ) → ℝ) (Ω : Set (ι → ℝ)) (hΩ : IsOpen Ω) (M : ℝ)
    (r : (ι → ℝ) → ι → ℝ) (hr : ∀ d ∈ Ω, ∀ i, 0 ≤ r d i)
    (hcont : ContinuousOn f Ω)
    (hnear : ∀ d ∈ Ω, ∀ i, ∀ᶠ t in 𝓝 (d i),
      DifferentiableAt ℝ (fun s => f (Function.update d i s)) t)
    (hsecond : ∀ d ∈ Ω, ∀ i,
      DifferentiableAt ℝ (deriv (fun s => f (Function.update d i s))) (d i))
    (hstrict : ∀ d ∈ Ω, 0 < ∑ i, r d i * deriv
      (deriv (fun s => f (Function.update d i s))) (d i))
    (hcompact : ∀ c > M, IsCompact {d ∈ Ω | c ≤ f d}) :
    ∀ d ∈ Ω, f d ≤ M := by
  intro d hd
  by_contra! hf
  obtain ⟨c, hMc, hcd⟩ := exists_between hf
  let S := {x ∈ Ω | c ≤ f x}
  have hS : IsCompact S := hcompact c hMc
  have hdS : d ∈ S := ⟨hd, hcd.le⟩
  obtain ⟨p, hp, hmax⟩ := hS.exists_isMaxOn ⟨d, hdS⟩ (hcont.mono fun _ h => h.1)
  have hpΩ : p ∈ Ω := hp.1
  have hcp : c < f p := hcd.trans_le (hmax hdS)
  have hpNear : S ∈ 𝓝 p := by
    have hc' := hcont.continuousAt (hΩ.mem_nhds hpΩ)
    filter_upwards [hΩ.mem_nhds hpΩ, hc'.tendsto.eventually (Ioi_mem_nhds hcp)] with x hxΩ hx
    exact ⟨hxΩ, hx.le⟩
  have hpMax : IsLocalMax f p := hmax.isLocalMax hpNear
  have hnonpos (i : ι) :
      deriv (deriv (fun s => f (Function.update p i s))) (p i) ≤ 0 := by
    have hc : Continuous (fun t : ℝ => Function.update p i t) :=
      continuous_const.update i continuous_id
    have hc₀ : ContinuousAt (fun t : ℝ => Function.update p i t) (p i) := hc.continuousAt
    have hupd : Function.update p i (p i) = p := by simp
    have ht : Tendsto (fun t : ℝ => Function.update p i t) (𝓝 (p i)) (𝓝 p) := by
      simpa only [hupd] using hc₀.tendsto
    have hloc : IsLocalMax (fun t => f (Function.update p i t)) (p i) := by
      change ∀ᶠ t in 𝓝 (p i), f (Function.update p i t) ≤ f (Function.update p i (p i))
      simpa only [hupd] using ht.eventually hpMax
    exact second_derivative_nonpos_at_local_max hloc (hnear p hpΩ i)
      (hsecond p hpΩ i).hasDerivAt
  exact (not_lt_of_ge (Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (hr p hpΩ i) (hnonpos i))) (hstrict p hpΩ)

omit [DecidableEq ι] in
/-- A bounded superlevel set is compact if it cannot approach the
boundary of its open domain at or above the prescribed level. -/
theorem compact_superlevel_of_boundary_exclusion
    (f : (ι → ℝ) → ℝ) (Ω : Set (ι → ℝ))
    (hc : ContinuousOn f Ω) (a : ℝ)
    (hb : Bornology.IsBounded {d ∈ Ω | a ≤ f d})
    (he : ∀ p ∈ closure Ω, p ∉ Ω → ∀ᶠ d in 𝓝[Ω] p, f d < a) :
    IsCompact {d ∈ Ω | a ≤ f d} := by
  classical
  let S := {d ∈ Ω | a ≤ f d}
  have hS : S ⊆ Ω := fun _ h => h.1
  refine Metric.isCompact_of_isClosed_isBounded ?_ hb
  apply isClosed_of_closure_subset
  intro p hp
  letI : NeBot (𝓝[S] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hm : ∀ᶠ d in 𝓝[S] p, d ∈ S := self_mem_nhdsWithin
  have hge : ∀ᶠ d in 𝓝[S] p, a ≤ f d := hm.mono fun _ h => h.2
  have hsub : 𝓝[S] p ≤ 𝓝[Ω] p := nhdsWithin_mono _ hS
  have hpΩ : p ∈ Ω := by
    by_contra h
    have hlt := (he p (closure_mono hS hp) h).filter_mono hsub
    obtain ⟨d, h₁, h₂⟩ := (hge.and hlt).exists
    exact (not_lt_of_ge h₁) h₂
  have ht : Tendsto f (𝓝[S] p) (𝓝 (f p)) := (hc p hpΩ).tendsto.mono_left hsub
  exact ⟨hpΩ, ge_of_tendsto ht hge⟩

/-- Adding a strict barrier to a weighted harmonic function proves its
boundary bound if each perturbed superlevel set is compact. -/
theorem weighted_coordinate_harmonic_bound_of_barrier
    (f φ : (ι → ℝ) → ℝ) (Ω : Set (ι → ℝ)) (hΩ : IsOpen Ω) (M : ℝ)
    (r : (ι → ℝ) → ι → ℝ) (hr : ∀ d ∈ Ω, ∀ i, 0 ≤ r d i)
    (hcf : ContinuousOn f Ω) (hcφ : ContinuousOn φ Ω)
    (hnear : ∀ d ∈ Ω, ∀ i, ∀ᶠ t in 𝓝 (d i),
      DifferentiableAt ℝ (fun s => f (Function.update d i s)) t ∧
      DifferentiableAt ℝ (fun s => φ (Function.update d i s)) t)
    (hsecond_f : ∀ d ∈ Ω, ∀ i,
      DifferentiableAt ℝ (deriv (fun s => f (Function.update d i s))) (d i))
    (hsecond_φ : ∀ d ∈ Ω, ∀ i,
      DifferentiableAt ℝ (deriv (fun s => φ (Function.update d i s))) (d i))
    (hzero : ∀ d ∈ Ω, (∑ i, r d i * deriv
      (deriv (fun s => f (Function.update d i s))) (d i)) = 0)
    (hpos : ∀ d ∈ Ω, 0 < ∑ i, r d i * deriv
      (deriv (fun s => φ (Function.update d i s))) (d i))
    (hcompact : ∀ ε > 0, ∀ c > M, IsCompact {d ∈ Ω | c ≤ f d + ε * φ d}) :
    ∀ d ∈ Ω, f d ≤ M := by
  have hp (ε : ℝ) (hε : 0 < ε) : ∀ d ∈ Ω, f d + ε * φ d ≤ M := by
    let g (d : ι → ℝ) := f d + ε * φ d
    have h₂ (d : ι → ℝ) (hd : d ∈ Ω) (i : ι) :
        HasDerivAt (deriv (fun s => g (Function.update d i s)))
          (deriv (deriv (fun s => f (Function.update d i s))) (d i) +
            ε * deriv (deriv (fun s => φ (Function.update d i s))) (d i)) (d i) := by
      have h := (hsecond_f d hd i).hasDerivAt.add
        ((hsecond_φ d hd i).hasDerivAt.const_mul ε)
      apply h.congr_of_eventuallyEq
      filter_upwards [hnear d hd i] with x hx
      exact deriv_add hx.1 (hx.2.const_mul ε) ▸ by rw [deriv_const_mul ε hx.2]
    apply weighted_coordinate_maximum_principle g Ω hΩ M r hr
      (hcf.add (continuousOn_const.mul hcφ))
    · intro d hd i
      filter_upwards [hnear d hd i] with t ht using ht.1.add (ht.2.const_mul ε)
    · exact fun d hd i => (h₂ d hd i).differentiableAt
    · intro d hd
      simp_rw [(h₂ d hd _).deriv, mul_add, sum_add_distrib, mul_left_comm (r d _), ← mul_sum,
        hzero d hd, zero_add]
      exact mul_pos hε (hpos d hd)
    · exact fun c hc => hcompact ε hε c hc
  intro d hd
  have hc : ContinuousAt (fun ε : ℝ => f d + ε * φ d) 0 := by fun_prop
  have ht : Tendsto (fun ε : ℝ => f d + ε * φ d) (𝓝[>] (0 : ℝ)) (𝓝 (f d)) := by
    simpa only [zero_mul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with ε hε
  exact hp ε hε d hd

end MOC
