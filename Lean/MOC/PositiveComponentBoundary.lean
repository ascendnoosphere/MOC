import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.Compact

/-! A positive component of the real gap must approach a singularity.
The lemma isolates the topological part of the maximum-principle
argument from the meromorphic geometry. -/

open Set
open scoped Topology

namespace MOC

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [CompactSpace X]

/-- A component of a positive superlevel set cannot stay away from the
excluded set when the function has no positive local maximum. -/
theorem closure_positive_component_meets_excluded
    (f : X → ℝ) (S : Set X) (hS : IsClosed S)
    (hcont : ContinuousOn f Sᶜ)
    (hno : ∀ x ∈ Sᶜ, 0 < f x → ¬ IsLocalMax f x)
    {x₀ : X} (hx : x₀ ∈ Sᶜ) (hpos : 0 < f x₀) :
    (closure (connectedComponentIn (Sᶜ ∩ {x | 0 < f x}) x₀) ∩ S).Nonempty := by
  let D : Set X := Sᶜ ∩ {x | 0 < f x}
  let C := connectedComponentIn D x₀
  have hD : IsOpen D :=
    hcont.isOpen_inter_preimage hS.isOpen_compl isOpen_Ioi
  have hxC : x₀ ∈ C := mem_connectedComponentIn ⟨hx,hpos⟩
  apply Classical.byContradiction
  intro hb
  have hclose : closure C ⊆ Sᶜ := fun x hm hs => hb ⟨x, hm, hs⟩
  obtain ⟨z,hzc,hzmax⟩ := isClosed_closure.isCompact.exists_isMaxOn
    ⟨x₀, subset_closure hxC⟩ (hcont.mono hclose)
  have hzp : 0 < f z := hpos.trans_le (hzmax (subset_closure hxC))
  have hzD : z ∈ D := ⟨hclose hzc,hzp⟩
  let C' := connectedComponentIn D z
  have hC' : IsOpen C' := hD.connectedComponentIn
  have hzin : z ∈ C' := mem_connectedComponentIn hzD
  obtain ⟨y,hy',hy⟩ := (mem_closure_iff.mp hzc) C' hC' hzin
  have hEq : C = C' := (connectedComponentIn_eq hy).trans (connectedComponentIn_eq hy').symm
  have hzC : z ∈ C := hEq ▸ hzin
  apply hno z (hclose hzc) hzp
  have hnear : ∀ᶠ y in 𝓝 z, y ∈ C := hD.connectedComponentIn.mem_nhds hzC
  exact hnear.mono fun _ hy => hzmax (subset_closure hy)

end MOC
