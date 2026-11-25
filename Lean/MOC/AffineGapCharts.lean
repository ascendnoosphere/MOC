import MOC.AffineGapCritical
import MOC.AffineCoordinateChart
import MOC.AffineGapProper

/-! On the actual affine curve, only finitely many values of the varying
gap need to be removed before it gives a local holomorphic coordinate. -/

open Filter Set MvPolynomial
open scoped Topology

namespace MOC

private theorem derivative_eval_ne_zero_of_separable_root (P : Polynomial ℂ) {a : ℂ}
    (hs : P.Separable) (hr : P.IsRoot a) : P.derivative.eval a ≠ 0 := by
  intro hz
  obtain ⟨U,V,h⟩ := (Polynomial.separable_def' _).mp hs
  have he := congrArg (Polynomial.eval a) h
  change P.eval a = 0 at hr
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    hr, hz, mul_zero, add_zero, zero_ne_one] at he

/-- The new base coordinate has local inverses on the original affine
locus, with holomorphic entries and both inverse identities. The finite
exceptional set is in the new base, not in a possibly unbounded old chart. -/
theorem exists_local_affine_gap_charts_off_finite
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite) (hfi : Function.Injective f)
    (t g : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hv : ∃ x y : zeroLocus Q, eval x.val g ≠ eval y.val g) :
    ∃ B : Set ℂ, B.Finite ∧ ∀ x₀ : zeroLocus Q, eval x₀.val g ∉ B →
      ∃ J : ℂ → σ → ℂ, J (eval x₀.val g) = x₀.val ∧
        (∀ᶠ w in 𝓝 (eval x₀.val g), J w ∈ zeroLocus Q ∧ eval (J w) g = w ∧
          ∀ i, DifferentiableAt ℂ (fun z => J z i) w) ∧
        ∀ᶠ x : zeroLocus Q in 𝓝 x₀, J (eval x.val g) = x.val := by
  classical
  let A := Polynomial ℂ
  let T := MvPolynomial σ ℂ ⧸ Q
  letI : Algebra A T := f.toRingHom.toAlgebra
  letI : Module.Finite A T := hf
  letI : FaithfulSMul A T := (faithfulSMul_iff_algebraMap_injective A T).mpr hfi
  obtain ⟨v,hvrec⟩ := exists_primitive_element_with_base_denominators A T
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective v
  choose d hd E hE using (fun i : σ => hvrec (Ideal.Quotient.mk Q (X i)))
  obtain ⟨P, hPm, hPi, hP⟩ :=
    exists_monic_irreducible_plane_image_of_finite_projection Q f hf hfi t g ht
  obtain ⟨L, hLm, hLi, hL⟩ :=
    exists_monic_irreducible_plane_image_of_finite_projection Q f hf hfi t u ht
  let G (x : zeroLocus Q) := eval x.val g
  let t₁ (x : zeroLocus Q) := eval x.val t
  have hPpoint (x : zeroLocus Q) : (P.map (Polynomial.evalRingHom (t₁ x))).IsRoot (G x) :=
    (hP _ _).mpr ⟨x.val,x.property,rfl,rfl⟩
  have hLpoint (x : zeroLocus Q) :
      (L.map (Polynomial.evalRingHom (t₁ x))).IsRoot (eval x.val u) :=
    (hL _ _).mpr ⟨x.val,x.property,rfl,rfl⟩
  have hInf : (range G).Infinite := by
    letI := connectedSpace_prime_finite_affine_curve Q f hf hfi t ht
    have hc : IsPreconnected (range G) :=
      (isConnected_range (g.continuous_eval.comp continuous_subtype_val)).isPreconnected
    obtain ⟨x,y,hxy⟩ := hv
    exact hc.infinite_of_nontrivial ⟨G x,⟨x,rfl⟩,G y,⟨y,rfl⟩,hxy⟩
  have hpInf : {w : ℂ | ∃ a, (P.map (Polynomial.evalRingHom a)).IsRoot w}.Infinite :=
    hInf.mono (by rintro _ ⟨x,rfl⟩; exact ⟨t₁ x,hPpoint x⟩)
  obtain ⟨R, _, hR, hBad⟩ := exists_generic_reversed_plane_root_cover P hPi hpInf
  let B₀ : Set ℂ :=
    {a | ¬ (P.map (Polynomial.evalRingHom a)).Separable} ∪
      {a | ¬ (L.map (Polynomial.evalRingHom a)).Separable} ∪
      ⋃ i, {a | (d i).IsRoot a}
  have hB₀ : B₀.Finite := ((finite_nonseparable_specializations_of_irreducible P hPm hPi).union
    (finite_nonseparable_specializations_of_irreducible L hLm hLi)).union
      (Set.finite_iUnion fun i => Polynomial.finite_setOf_isRoot (hd i))
  let W : Set (zeroLocus Q) := t₁ ⁻¹' B₀
  have hF : W.Finite := by
    apply Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    apply Set.Finite.subset (hB₀.biUnion (fun a _ => finite_points_over_finite_projection Q f hf t ht a))
    rintro y ⟨x,hx,rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨t₁ x,hx,x.property,rfl⟩
  let B : Set ℂ := {w : ℂ | ¬ (R.map (Polynomial.evalRingHom w)).Separable ∨
      R.leadingCoeff.eval w = 0} ∪ G '' W
  refine ⟨B,hBad.union (hF.image G),fun x₀ hx₀ => ?_⟩
  have htg : t₁ x₀ ∉ B₀ := fun hh => hx₀ (Or.inr ⟨x₀,hh,rfl⟩)
  have hp : (P.map (Polynomial.evalRingHom (t₁ x₀))).Separable :=
    not_not.mp (fun h => htg (Or.inl (Or.inl h)))
  have hl : (L.map (Polynomial.evalRingHom (t₁ x₀))).Separable :=
    not_not.mp (fun h => htg (Or.inl (Or.inr h)))
  have hr : (R.map (Polynomial.evalRingHom (G x₀))).Separable :=
    not_not.mp (fun h => hx₀ (Or.inl (Or.inl h)))
  have hn : ∀ᶠ a in 𝓝 (t₁ x₀), ∀ i, (d i).eval a ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    apply (d i).continuous.continuousAt.eventually_ne
    exact fun h => htg (Or.inr (mem_iUnion.mpr ⟨i,h⟩))
  obtain ⟨H,hH₀,hH,hInv⟩ := exists_local_holomorphic_affine_coordinate_chart Q f t u ht L hL
    d E hE x₀ hn (derivative_eval_ne_zero_of_separable_root _ hl (hLpoint x₀))
  exact exists_local_holomorphic_gap_chart_of_simple_plane_pair Q t g P R hPpoint hR x₀
    (derivative_eval_ne_zero_of_separable_root _ hp (hPpoint x₀))
    (derivative_eval_ne_zero_of_separable_root _ hr ((hR _ _).mpr (hPpoint x₀))) H hH₀ hH hInv

end MOC
