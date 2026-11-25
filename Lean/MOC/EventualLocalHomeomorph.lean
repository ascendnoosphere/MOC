import Mathlib.Topology.IsLocalHomeomorph
import MOC.FiniteCurvePrimitiveCoordinate

/-! A two-sided local inverse gives a partial homeomorphism. -/

open Set Filter
open scoped Topology

namespace MOC

theorem exists_partialHomeomorph_of_eventually_inverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (g : X → Y) (hg : Continuous g) (x₀ : X) (j : Y → X)
    (h₁ : ∀ᶠ y in 𝓝 (g x₀), ContinuousAt j y ∧ g (j y) = y)
    (h₂ : ∀ᶠ x in 𝓝 x₀, j (g x) = x) :
    ∃ e : PartialHomeomorph X Y, x₀ ∈ e.source ∧ Set.EqOn g e e.source := by
  obtain ⟨W, hW, hWo, hW₀⟩ := mem_nhds_iff.mp h₁
  obtain ⟨V, hV, hVo, hV₀⟩ := mem_nhds_iff.mp h₂
  let U := W ∩ j ⁻¹' V
  have hc : ContinuousOn j W := continuousOn_of_forall_continuousAt fun y hy => (hW hy).1
  have hu : IsOpen U := hc.isOpen_inter_preimage hWo hVo
  have hu₀ : g x₀ ∈ U := by
    refine ⟨hW₀, ?_⟩
    change j (g x₀) ∈ V
    rwa [hV hV₀]
  let V' := V ∩ g ⁻¹' U
  refine ⟨{
    toFun := g
    invFun := j
    source := V'
    target := U
    map_source' := fun _ h => h.2
    map_target' := fun y hy => ⟨hy.2, by
      change g (j y) ∈ U
      rwa [(hW hy.1).2]⟩
    left_inv' := fun _ h => hV h.1
    right_inv' := fun _ h => (hW h.1).2
    open_source := hVo.inter (hu.preimage hg)
    open_target := hu
    continuousOn_toFun := hg.continuousOn
    continuousOn_invFun := hc.mono inter_subset_left }, ⟨hV₀,hu₀⟩, fun _ _ => rfl⟩


/-- An inverse into an ambient space gives a partial homeomorphism if it
locally takes values in the continuously embedded domain. -/
theorem exists_partialHomeomorph_of_eventually_inverse_into_embedding
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (ι : X → Z) (hι : Topology.IsEmbedding ι)
    (g : X → Y) (hg : Continuous g) (x₀ : X) (j : Y → Z)
    (h₁ : ∀ᶠ y in 𝓝 (g x₀), ContinuousAt j y ∧ ∃ x, ι x = j y ∧ g x = y)
    (h₂ : ∀ᶠ x in 𝓝 x₀, j (g x) = ι x) :
    ∃ e : PartialHomeomorph X Y, x₀ ∈ e.source ∧ Set.EqOn g e e.source := by
  classical
  let p (y : Y) : Prop := ∃ x : X, ι x = j y
  let lift (y : Y) : X := if hy : p y then Classical.choose hy else x₀
  have hl (y : Y) (hy : p y) : ι (lift y) = j y := by
    change ι (if h : p y then Classical.choose h else x₀) = j y
    rw [dif_pos hy]
    exact Classical.choose_spec hy
  obtain ⟨W, hW, hWo, hW₀⟩ := mem_nhds_iff.mp h₁
  have hW' : W ∈ 𝓝 (g x₀) := hWo.mem_nhds hW₀
  apply exists_partialHomeomorph_of_eventually_inverse g hg x₀ lift
  · filter_upwards [hW'] with y hy
    obtain ⟨hj, z, hz, hgz⟩ := hW hy
    have he : lift y = z := hι.injective ((hl y ⟨z,hz⟩).trans hz.symm)
    refine ⟨hι.isInducing.continuousAt_iff.mpr (hj.congr ?_), he ▸ hgz⟩
    filter_upwards [hWo.mem_nhds hy] with y' hy'
    obtain ⟨z', hz', _⟩ := (hW hy').2
    exact (hl y' ⟨z',hz'⟩).symm
  · filter_upwards [h₂] with x hx
    exact hι.injective ((hl (g x) ⟨x,hx.symm⟩).trans hx)

open MvPolynomial

/-- An ambient affine gap chart yields a partial homeomorphism on the
actual points restricted to an arbitrary set of allowed gap values.
The ambient chart need not have been defined as a subtype-valued map. -/
theorem exists_partialHomeomorph_of_affine_gap_chart
    {σ : Type*} (Q : Ideal (MvPolynomial σ ℂ)) (g : MvPolynomial σ ℂ)
    (O : Set ℂ)
    (x₀ : {x : zeroLocus Q // eval x.val g ∈ O})
    (J : ℂ → σ → ℂ)
    (hJ : ∀ᶠ w in 𝓝 (eval x₀.val.val g),
      J w ∈ zeroLocus Q ∧ eval (J w) g = w ∧ ContinuousAt J w)
    (hInv : ∀ᶠ x : zeroLocus Q in 𝓝 x₀.val, J (eval x.val g) = x.val) :
    let gap : {x : zeroLocus Q // eval x.val g ∈ O} → O :=
      fun x => ⟨eval x.val.val g, x.property⟩
    ∃ e : PartialHomeomorph {x : zeroLocus Q // eval x.val g ∈ O} O,
      x₀ ∈ e.source ∧ Set.EqOn gap e e.source := by
  let X := {x : zeroLocus Q // eval x.val g ∈ O}
  let gap : X → O := fun x => ⟨eval x.val.val g, x.property⟩
  let ι : X → σ → ℂ := fun x => x.val.val
  have hι : Topology.IsEmbedding ι := Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hg : Continuous gap :=
    (g.continuous_eval.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  apply exists_partialHomeomorph_of_eventually_inverse_into_embedding ι hι gap hg x₀ (J ∘ Subtype.val)
  · have hc : ContinuousAt (Subtype.val : O → ℂ) (gap x₀) := continuous_subtype_val.continuousAt
    filter_upwards [hc.eventually hJ] with y hy
    obtain ⟨hyQ, hyG, hyC⟩ := hy
    have hyo : eval (J y.val) g ∈ O := by
      rw [hyG]
      exact y.property
    refine ⟨hyC.comp continuous_subtype_val.continuousAt, ⟨⟨⟨J y.val,hyQ⟩,hyo⟩, rfl, ?_⟩⟩
    exact Subtype.ext hyG
  · exact continuous_subtype_val.continuousAt.eventually hInv


end MOC
