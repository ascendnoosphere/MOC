import MOC.AffineGapCharts
import MOC.AffineGapContinuation
import MOC.EventualLocalHomeomorph

/-! A varying regular coordinate of a prime finite affine curve supplies
the exact gap covering needed for contact transfer. No projective model
or Laurent expansion is used by this route. -/

open Set MvPolynomial Filter Matrix
open scoped Topology

namespace MOC
noncomputable section

/-- The varying gap on an actual prime finite affine curve is covered
by local holomorphic root charts after excluding finitely many values. -/
theorem affineGapCharts (σ : Type*) [Fintype σ] : AffineGapCharts σ := by
  classical
  intro Q hQ f hf hfi t g ht hvar
  obtain ⟨B₁,hB₁,hchart⟩ := exists_local_affine_gap_charts_off_finite Q f hf hfi t g ht hvar
  obtain ⟨B₂,hB₂,hproper⟩ := affine_varying_coordinate_proper_off_finite Q f hf hfi t g ht
  let G (x : zeroLocus Q) := eval x.val g
  have hc : (range G)ᶜ.Finite := finite_compl_range_varying_affine_coordinate Q f hf hfi t g ht hvar
  let B := (B₁ ∪ B₂) ∪ (range G)ᶜ
  have hB : B.Finite := (hB₁.union hB₂).union hc
  let E : Set (zeroLocus Q) := G ⁻¹' Bᶜ
  let p : E → (↑Bᶜ : Type) := fun x => ⟨G x.val,x.property⟩
  have hpcont : Continuous p :=
    (g.continuous_eval.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hsurj : Function.Surjective p := by
    intro y
    have hy : y.val ∈ range G := by
      apply Classical.byContradiction
      intro h
      exact y.property (Or.inr h)
    obtain ⟨x,hx⟩ := hy
    exact ⟨⟨x,show G x ∈ Bᶜ from hx.symm ▸ y.property⟩, Subtype.ext hx⟩
  have hp : IsProperMap p := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hpcont,fun K hK => ?_⟩
    let V := (Subtype.val : (↑Bᶜ : Type) → ℂ) '' K
    have hcV : IsCompact V := hK.image continuous_subtype_val
    have hsub : V ⊆ B₂ᶜ := by
      rintro z ⟨y,hy,rfl⟩ hb
      exact y.property (Or.inl (Or.inr hb))
    have hcomp : IsCompact (G ⁻¹' V) := hproper V hcV hsub
    apply Subtype.isCompact_iff.mpr
    have he : (Subtype.val : E → zeroLocus Q) '' (p ⁻¹' K) = G ⁻¹' V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨p y,hy,rfl⟩
      · rintro ⟨z,hz,he⟩
        have hx : G x ∈ Bᶜ := he ▸ z.property
        let y : E := ⟨x,hx⟩
        refine ⟨y, ?_, rfl⟩
        change p y ∈ K
        rwa [show p y = z from Subtype.ext he.symm]
    rwa [he]
  have hbranch (x : E) :
      ∃ J : ℂ → σ → ℂ, J (G x.val) = x.val.val ∧
        (∀ᶠ w in 𝓝 (G x.val), J w ∈ zeroLocus Q ∧ eval (J w) g = w ∧
          ∀ i, DifferentiableAt ℂ (fun z => J z i) w) ∧
        ∀ᶠ x' : zeroLocus Q in 𝓝 x.val, J (G x') = x'.val :=
    hchart x.val (fun hb => x.property (Or.inl (Or.inl hb)))
  have hl : IsLocalHomeomorph p := IsLocalHomeomorph.mk p (by
    intro x
    obtain ⟨J,_,hJ,hInv⟩ := hbranch x
    exact exists_partialHomeomorph_of_affine_gap_chart Q g Bᶜ x J
      (hJ.mono fun _ h => ⟨h.1,h.2.1,continuousAt_pi.mpr fun i => (h.2.2 i).continuousAt⟩)
      hInv)
  refine ⟨B,hB,isCoveringMap_of_proper_localHomeomorph p hl hp hsurj,fun x i => ?_⟩
  obtain ⟨J,_,hJ,hInv⟩ := hbranch x
  refine ⟨fun z => J z i,hJ.self_of_nhds.2.2 i,?_⟩
  have he : ∀ᶠ x' in 𝓝 x, J (G x'.val) = x'.val.val := continuous_subtype_val.continuousAt hInv
  exact he.mono fun x' hx' => (congrFun hx' i).symm

/-- Unconditional affine continuation for any finite complex affine
prime curve, including curves with exceptional initial points. -/
theorem affineGapContinuation (σ : Type*) [Fintype σ] : AffineGapContinuation σ :=
  affineGapContinuation_of_charts (affineGapCharts σ)

/-- The full conjecture is equivalent to its terminal support bound on
profiles with at least $2n-1$ contacts, without any genericity hypothesis. -/
theorem conjecture_iff_sharp_terminal_contact_bound {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Conjecture ι ↔ ¬ ∃ (U : Matrix ι ι ℂ), IsUnitary U ∧
      ∃ w : StrictMatchingSupport U, 2 * Fintype.card ι - 1 ≤ w.contacts.card :=
  conjecture_iff_varying_gap_terminal (affineGapContinuation (Equiv.Perm ι))

end
end MOC
