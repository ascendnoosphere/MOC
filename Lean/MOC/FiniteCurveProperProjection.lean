import MOC.FiniteCurveFibers
import MOC.FiniteCurveClosure
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Finite affine projection is proper in the complex topology. -/

open Set MvPolynomial
open scoped Topology

namespace MOC

variable {σ : Type*}

private theorem isClosed_affine_zero_locus (Q : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (zeroLocus Q) := by
  have h : zeroLocus Q = ⋂ q : Q, {x : σ → ℂ | eval x q.val = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, mem_zeroLocus_iff]
    exact ⟨fun h q => h q q.prop, fun h q hq => h ⟨q,hq⟩⟩
  rw [h]
  exact isClosed_iInter fun q => isClosed_eq q.val.continuous_eval continuous_const

/-- A compact set of parameter values has a compact full inverse image in
the given affine curve. Algebraic finiteness supplies monic coordinate
equations and hence uniform coordinate bounds. -/
theorem isCompact_affine_finite_projection_over_compact
    (Q : Ideal (MvPolynomial σ ℂ))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    {S : Set ℂ} (hS : IsCompact S) :
    IsCompact {x : σ → ℂ | x ∈ zeroLocus Q ∧ eval x t ∈ S} := by
  classical
  obtain ⟨P, hP, hroot⟩ := exists_monic_coordinate_equations_of_finite_projection Q f hf t ht
  have hg i := exists_uniform_polynomial_growth_of_monic_family_roots (P i) (hP i)
  choose C hC d hbound using hg
  obtain ⟨B, hB⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp hS.isBounded
  let K : σ → Set ℂ := fun i => Metric.closedBall 0 (C i * (1 + max B 0) ^ d i)
  have hK (i : σ) : IsCompact (K i) := isCompact_closedBall _ _
  have hclosed :
      IsClosed {x : σ → ℂ | x ∈ zeroLocus Q ∧ eval x t ∈ S} :=
    (isClosed_affine_zero_locus Q).inter (hS.isClosed.preimage t.continuous_eval)
  apply (isCompact_univ_pi hK).of_isClosed_subset hclosed
  intro x hx
  apply Set.mem_pi.mpr
  intro i _
  apply Metric.mem_closedBall.mpr
  rw [dist_zero_right]
  have hp : ‖eval x t‖ ≤ B := by simpa [Metric.mem_closedBall, dist_zero_right] using hB hx.2
  exact (hbound i (eval x t) (x i) (hroot x hx.1 i)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [hp.trans (le_max_left B 0)]) _)
      (hC i).le)

/-- Every plane projection preserving the finite base coordinate is
proper as a map on complex points. -/
theorem isProperMap_affine_plane_projection
    (Q : Ideal (MvPolynomial σ ℂ))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (t u : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X) :
    IsProperMap (fun x : zeroLocus Q => (eval x.val t, eval x.val u)) := by
  let F (x : σ → ℂ) := (eval x t, eval x u)
  have hF : Continuous F := t.continuous_eval.prodMk u.continuous_eval
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hF.comp continuous_subtype_val, fun K hK => ?_⟩
  apply Subtype.isCompact_iff.mpr
  have heq :
      Subtype.val '' ((fun x : zeroLocus Q => F x.val) ⁻¹' K) =
        {x : σ → ℂ | x ∈ zeroLocus Q ∧ F x ∈ K} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [heq]
  apply (isCompact_affine_finite_projection_over_compact Q f hf t ht
    (hK.image continuous_fst)).of_isClosed_subset
    ((isClosed_affine_zero_locus Q).inter (hK.isClosed.preimage hF))
  intro x hx
  exact ⟨hx.1, ⟨F x, hx.2, rfl⟩⟩

/-- If a plane coordinate pair separates a pinned affine point in its
fiber, then regular plane roots approximating its image lift to affine
points approximating the pinned point. Properness supplies a limit lift. -/
theorem mem_closure_regular_affine_of_unique_plane_preimage
    (Q : Ideal (MvPolynomial σ ℂ))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (t u : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic)
    (hplane : ∀ a b : ℂ, (P.map (Polynomial.evalRingHom a)).IsRoot b ↔
      ∃ z ∈ zeroLocus Q, eval z t = a ∧ eval z u = b)
    {S : Set ℂ} (hS : S.Finite)
    (hsep : ∀ a ∈ Sᶜ, (P.map (Polynomial.evalRingHom a)).Separable)
    (x : zeroLocus Q)
    (hunique : ∀ y : zeroLocus Q,
      eval y.val t = eval x.val t → eval y.val u = eval x.val u → y = x) :
    x ∈ closure {y : zeroLocus Q | eval y.val t ∈ Sᶜ} := by
  let F (y : zeroLocus Q) := (eval y.val t, eval y.val u)
  let R : Set (zeroLocus Q) := {y | eval y.val t ∈ Sᶜ}
  have hImg : F '' R =
      {p : ℂ × ℂ | p.1 ∈ Sᶜ ∧ (P.map (Polynomial.evalRingHom p.1)).IsRoot p.2} := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, (hplane _ _).mpr ⟨y.val, y.property, rfl, rfl⟩⟩
    · rintro ⟨hs, hr⟩
      obtain ⟨y, hy, ht, hu⟩ := (hplane p.1 p.2).mp hr
      refine ⟨⟨y,hy⟩, ?_, Prod.ext ht hu⟩
      change eval y t ∈ Sᶜ
      rwa [ht]
  have hx : F x ∈ closure (F '' R) := by
    rw [hImg, closure_simple_root_cover_eq_plane_curve P hP hS hsep]
    exact (hplane _ _).mpr ⟨x.val, x.property, rfl, rfl⟩
  obtain ⟨y, hy, hF⟩ :=
    (isProperMap_affine_plane_projection Q f hf t u ht).isClosedMap.closure_image_subset R hx
  have he : y = x := hunique y (congrArg Prod.fst hF) (congrArg Prod.snd hF)
  exact he ▸ hy

/-- Connectedness of an irreducible plane curve transfers back to the
affine curve if its regular points are dense and the plane pair is
injective there. Both conditions are stated on the actual affine points. -/
theorem connectedSpace_affine_of_injective_regular_plane_projection
    (Q : Ideal (MvPolynomial σ ℂ))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (t u : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic) (hirr : Irreducible P)
    (hplane : ∀ a b : ℂ, (P.map (Polynomial.evalRingHom a)).IsRoot b ↔
      ∃ z ∈ zeroLocus Q, eval z t = a ∧ eval z u = b)
    {S : Set ℂ} (hS : S.Finite)
    (hsep : ∀ a ∈ Sᶜ, (P.map (Polynomial.evalRingHom a)).Separable)
    (hinj : Set.InjOn (fun y : zeroLocus Q => (eval y.val t, eval y.val u))
      {y | eval y.val t ∈ Sᶜ})
    (hdense : Dense {y : zeroLocus Q | eval y.val t ∈ Sᶜ}) :
    ConnectedSpace (zeroLocus Q) := by
  let F (y : zeroLocus Q) := (eval y.val t, eval y.val u)
  let A : Set (ℂ × ℂ) := {p | p.1 ∈ Sᶜ ∧ (P.map (Polynomial.evalRingHom p.1)).IsRoot p.2}
  let R : Set (zeroLocus Q) := {y | eval y.val t ∈ Sᶜ}
  have hA : IsConnected A := isConnected_simple_root_cover_of_irreducible P hP hirr hS hsep
  have hpre : F ⁻¹' A = R := by
    ext y
    exact ⟨fun hy => hy.1, fun hy => ⟨hy, (hplane _ _).mpr ⟨y.val, y.property, rfl, rfl⟩⟩⟩
  have hFclosed : IsClosedMap F := (isProperMap_affine_plane_projection Q f hf t u ht).isClosedMap
  let G := A.restrictPreimage F
  have hGclosed : IsClosedMap G := hFclosed.restrictPreimage A
  have hGinj : Function.Injective G := by
    intro x y hxy
    apply Subtype.ext
    have hx : x.val ∈ R := by rw [← hpre]; exact x.property
    have hy : y.val ∈ R := by rw [← hpre]; exact y.property
    apply hinj hx hy
    exact congrArg Subtype.val hxy
  have hGsurj : Function.Surjective G := by
    intro p
    obtain ⟨x, hx, ht, hu⟩ := (hplane p.val.1 p.val.2).mp p.property.2
    let y : zeroLocus Q := ⟨x,hx⟩
    have he : F y = p.val := Prod.ext ht hu
    have hy : y ∈ F ⁻¹' A := by change F y ∈ A; rw [he]; exact p.property
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  letI : ConnectedSpace A := Subtype.connectedSpace hA
  have hPre : IsConnected (Set.univ : Set (F ⁻¹' A)) := by
    simpa only [Set.preimage_univ] using
      isConnected_univ.preimage_of_isClosedMap hGinj hGclosed (range_eq_univ.mpr hGsurj ▸ subset_rfl)
  have hR : IsConnected R := by
    simpa [hpre] using hPre.image Subtype.val continuous_subtype_val.continuousOn
  have hUniv : IsConnected (Set.univ : Set (zeroLocus Q)) := hdense.closure_eq ▸ hR.closure
  exact { toPreconnectedSpace := ⟨hUniv.isPreconnected⟩
          toNonempty := Nonempty.map Subtype.val hUniv.nonempty.to_subtype }

end MOC
