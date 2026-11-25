import MOC.HalfPlaneProfileObstruction
import MOC.ConnectedContactStep
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-! More contacts on a positive-gap component with a regular half-plane
sheet. A topological covering suffices if the profile coordinates are
holomorphic in its local base charts. -/

open Filter Set Matrix
open scoped Topology unitInterval

namespace MOC


/-- Lift a shifted half-plane through a cover. Local holomorphic
expressions in the complex base coordinate remain holomorphic on the
global lift. -/
theorem exists_halfPlane_holomorphic_coordinates {E B J : Type*}
    [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (hp : IsCoveringMap p)
    (b : B → ℂ) (c : ℝ) (D : Set ℂ) (hD : D = {z | 0 < z.re})
    (i : C(D, B)) (hi : ∀ z, b (i z) = (z : ℂ) + c)
    (z₀ : D) (e₀ : E) (he₀ : p e₀ = i z₀) (P : E → J → ℂ)
    (hlocal : ∀ e q, ∃ f : ℂ → ℂ, DifferentiableAt ℂ f (b (p e)) ∧
      ∀ᶠ e' in 𝓝 e, P e' q = f (b (p e'))) :
    ∃ s : C(D, E), s z₀ = e₀ ∧ (∀ z, p (s z) = i z) ∧
      ∃ Q : ℂ → J → ℂ, (∀ z, Q z.val = P (s z)) ∧
        ∀ q, DifferentiableOn ℂ (fun z => Q z q) D := by
  classical
  have hDop : IsOpen D := hD ▸ isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ D := hD ▸ convex_halfSpace_gt Complex.reLm.isLinear 0
  letI : ContractibleSpace D := hconv.contractibleSpace ⟨z₀, z₀.property⟩
  letI : SimplyConnectedSpace D := SimplyConnectedSpace.ofContractible D
  letI : LocPathConnectedSpace D := hDop.locPathConnectedSpace
  obtain ⟨s, ⟨hstart, hs⟩, _⟩ := hp.existsUnique_continuousMap_lifts i z₀ e₀ he₀
  have hs' (z : D) : p (s z) = i z := congrFun hs z
  let Q (z : ℂ) : J → ℂ := if hz : z ∈ D then P (s ⟨z, hz⟩) else 0
  have hQ (z : D) : Q z.val = P (s z) := dif_pos z.property
  refine ⟨s, hstart, hs', Q, hQ, fun q z hz => ?_⟩
  let x : D := ⟨z, hz⟩
  obtain ⟨f, hfd, he⟩ := hlocal (s x) q
  have hfd' : DifferentiableAt ℂ f (z + (c : ℂ)) := by simpa only [hs', hi] using hfd
  have hdiff : DifferentiableAt ℂ (fun y : ℂ => f (y + (c : ℂ))) z :=
    hfd'.comp z ((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).add_const _)
  apply (hdiff.congr_of_eventuallyEq ?_).differentiableWithinAt
  have hpred : ∀ᶠ y in 𝓝 x, Q y.val q = f (y.val + (c : ℂ)) := by
    have h : ∀ᶠ y in 𝓝 x, P (s y) q = f (b (p (s y))) :=
      (s.continuous.continuousAt : ContinuousAt s x) he
    exact h.mono fun y hy => by rw [hQ, hy, hs', hi]
  rw [nhds_subtype_eq_comap] at hpred
  obtain ⟨V, hV, hsub⟩ := mem_comap.mp hpred
  filter_upwards [hV, hDop.mem_nhds hz] with z' hV' hD'
  exact hsub (show (⟨z', hD'⟩ : D) ∈ Subtype.val ⁻¹' V from hV')

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A half-plane sheet in the positive-gap component forces a new
contact without pinning the determinant gap. All old complex differences
are preserved when they are constant on the component. -/
theorem StrictMatchingSupport.exists_more_contacts_of_halfPlane_sheet
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    {X : Type*} [TopologicalSpace X] {S : Set X} (hconn : IsPreconnected S)
    (P : X → Equiv.Perm ι → ℂ)
    (hexact : ∀ x ∈ S, ∃ a b : ι → ℂ, matchingProduct a b = P x)
    (hc : ∀ q, ContinuousOn (fun x => (w.η * (P x w.pivot - P x q)).re) S)
    {x₀ : X} (hx₀ : x₀ ∈ S) (hbase : P x₀ = matchingProduct w.a w.b)
    (hold : ∀ x ∈ S, ∀ q ∈ w.contacts,
      P x w.pivot - P x q = P x₀ w.pivot - P x₀ q)
    (hgap : ∀ x ∈ S, 0 < (matchingProfileDetGap U w.η w.pivot (P x)).re)
    (s : ℂ → X) (c : ℝ)
    (hs : ∀ z, 0 < z.re → s z ∈ S)
    (hhol : ∀ q, DifferentiableOn ℂ (fun z => P (s z) q) {z | 0 < z.re})
    (hsG : ∀ z, 0 < z.re → matchingProfileDetGap U w.η w.pivot (P (s z)) = z + c) :
    ∃ w' : StrictMatchingSupport U, w'.η = w.η ∧ w'.pivot = w.pivot ∧
      w.contacts ⊂ w'.contacts ∧
      ∀ q ∈ w.contacts, matchingProduct w'.a w'.b w'.pivot - matchingProduct w'.a w'.b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q := by
  classical
  have hη : w.η ≠ 0 := by
    intro h
    have hh := w.strict
    simp [h] at hh
  have hneg : ∃ x ∈ S, ∃ q, (w.η * (P x w.pivot - P x q)).re < 0 := by
    by_contra h
    push_neg at h
    exact not_exact_profile_halfPlane_section U hU w.η hη w.pivot (fun z => P (s z)) c
      (fun z hz => hexact _ (hs z hz)) hhol hsG (fun z hz q => h _ (hs z hz) q)
  have hold' (x) (hx : x ∈ S) (q) (hq : q ∈ w.contacts) :
      (w.η * (P x w.pivot - P x q)).re = 0 := by
    rw [hold x hx q hq, hbase, mul_sub, Complex.sub_re, (Finset.mem_filter.mp hq).2, sub_self]
  obtain ⟨v, hη', hp, hv, z, hz, heq⟩ :=
    w.exists_more_contacts_on_connected_profiles hU hconn P hexact hc hx₀ hbase hold' hgap hneg
  refine ⟨v, hη', hp, hv, fun q hq => ?_⟩
  rw [hp, heq, hold z hz q hq, hbase]

/-- Path lifting joins a strict starting profile to its entire
half-plane sheet in the positive-gap locus. This isolates the remaining
algebraic input: a cover by local holomorphic profile charts. -/
theorem StrictMatchingSupport.exists_more_contacts_of_gap_cover
    {U : Matrix ι ι ℂ} (hU : IsUnitary U) (w : StrictMatchingSupport U)
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (hp : IsCoveringMap p) (b : B → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (D : Set ℂ) (hD : D = {z | 0 < z.re}) (i : C(D, B))
    (hi : ∀ z, b (i z) = (z : ℂ) + c)
    (z₀ : D) (e₀ : E) (γ : Path (p e₀) (i z₀))
    (hγ : ∀ t, 0 < (b (γ t)).re)
    (P : E → Equiv.Perm ι → ℂ)
    (hex : ∀ e, ∃ a b : ι → ℂ, matchingProduct a b = P e)
    (hstart : P e₀ = matchingProduct w.a w.b)
    (hcont : Continuous P)
    (hold : ∀ e, ∀ q ∈ w.contacts, P e w.pivot - P e q = P e₀ w.pivot - P e₀ q)
    (hG : ∀ e, matchingProfileDetGap U w.η w.pivot (P e) = b (p e))
    (hlocal : ∀ e q, ∃ f : ℂ → ℂ, DifferentiableAt ℂ f (b (p e)) ∧
      ∀ᶠ e' in 𝓝 e, P e' q = f (b (p e'))) :
    ∃ w' : StrictMatchingSupport U, w'.η = w.η ∧ w'.pivot = w.pivot ∧
      w.contacts ⊂ w'.contacts ∧
      ∀ q ∈ w.contacts, matchingProduct w'.a w'.b w'.pivot - matchingProduct w'.a w'.b q =
        matchingProduct w.a w.b w.pivot - matchingProduct w.a w.b q := by
  classical
  obtain ⟨Γ, hlift, hzero⟩ := hp.exists_path_lifts γ.toContinuousMap e₀ γ.source
  have hproj (t : I) : p (Γ t) = γ t := congrFun hlift t
  have hend : p (Γ 1) = i z₀ := (hproj 1).trans γ.target
  obtain ⟨s, hs0, hs, R, hR, hhol⟩ :=
    exists_halfPlane_holomorphic_coordinates p hp b c D hD i hi z₀ (Γ 1) hend P hlocal
  let A : Set E := {e | 0 < (b (p e)).re}
  let S := pathComponentIn e₀ A
  have he₀ : e₀ ∈ A := by
    have hh := hγ 0
    rwa [γ.source] at hh
  have hjoin : Γ 1 ∈ S := by
    refine ⟨⟨Γ, hzero, rfl⟩, fun t => ?_⟩
    change 0 < (b (p (Γ t))).re
    rw [hproj]
    exact hγ t
  have ha (z : D) : s z ∈ A := by
    change 0 < (b (p (s z))).re
    have hz : 0 < (z : ℂ).re := hD ▸ z.property
    rw [hs, hi, Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg hz hc
  have hconv : Convex ℝ D := hD ▸ convex_halfSpace_gt Complex.reLm.isLinear 0
  letI : ContractibleSpace D := hconv.contractibleSpace ⟨z₀, z₀.property⟩
  letI : SimplyConnectedSpace D := SimplyConnectedSpace.ofContractible D
  have hsS (z : D) : s z ∈ S := by
    have hpath : IsPathConnected (range s) := isPathConnected_range s.continuous
    have h := hpath.joinedIn (s z₀) ⟨z₀, rfl⟩ (s z) ⟨z, rfl⟩
    rw [hs0] at h
    refine (show JoinedIn A e₀ (Γ 1) from hjoin).trans (h.mono ?_)
    rintro e ⟨y, hy⟩
    rw [← hy]
    exact ha y
  let s₁ (z : ℂ) : E := if hz : z ∈ D then s ⟨z,hz⟩ else e₀
  have hval (z : ℂ) (hz : z ∈ D) : s₁ z = s ⟨z,hz⟩ := dif_pos hz
  have hEq (z : ℂ) (hz : z ∈ D) : P (s₁ z) = R z := by rw [hval z hz, ← hR ⟨z,hz⟩]
  refine w.exists_more_contacts_of_halfPlane_sheet hU (isPathConnected_pathComponentIn he₀).isConnected.isPreconnected
    P (fun e _ => hex e) (fun q => ?_) (mem_pathComponentIn_self he₀) hstart (fun e _ => hold e)
    (fun e he => ?_) s₁ c (fun z hz => ?_) (fun q => ?_) (fun z hz => ?_)
  · have h (q : Equiv.Perm ι) := (continuous_apply q).comp hcont
    exact (Complex.continuous_re.comp (continuous_const.mul ((h w.pivot).sub (h q)))).continuousOn
  · rw [hG]
    exact (show e ∈ A from pathComponentIn_subset he)
  · have h : z ∈ D := hD ▸ hz
    rw [hval z h]
    exact hsS ⟨z,h⟩
  · rw [← hD]
    exact (hhol q).congr fun z hz => congrFun (hEq z hz) q
  · have h : z ∈ D := hD ▸ hz
    rw [hG, hval z h, hs, hi]

end MOC
