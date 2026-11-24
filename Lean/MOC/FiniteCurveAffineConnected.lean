import MOC.FiniteCurvePlaneImage
import MOC.FiniteCurveFiberSeparation
import MOC.FiniteCurveProperProjection

/-! Pinned density and connectedness criteria for finite affine complex curves. -/

open Set MvPolynomial
open scoped Topology

namespace MOC

variable {σ : Type*} [Fintype σ]

/-- Deleting any finite set of parameter values from a prime finite affine
curve leaves a dense set of its complex points. Each pinned point may use
its own separating plane coordinate. -/
theorem dense_affine_finite_projection_off_finite
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    {S : Set ℂ} (hS : S.Finite) :
    Dense {x : zeroLocus Q | eval x.val t ∈ Sᶜ} := by
  intro x
  obtain ⟨u, hu⟩ := exists_polynomial_separating_pinned_finite_fiber Q f hf t ht x
  obtain ⟨P, hP, hirr, hplane⟩ :=
    exists_monic_irreducible_plane_image_of_finite_projection Q f hf hfi t u ht
  let E : Set ℂ := S ∪ {z | ¬ (P.map (Polynomial.evalRingHom z)).Separable}
  have hE : E.Finite := hS.union (finite_nonseparable_specializations_of_irreducible P hP hirr)
  have hsep : ∀ a ∈ Eᶜ, (P.map (Polynomial.evalRingHom a)).Separable := by
    intro a ha
    exact not_not.mp (fun h => ha (Or.inr h))
  have hh := mem_closure_regular_affine_of_unique_plane_preimage Q f hf t u ht P hP hplane
    hE hsep x hu
  have hsub : {y : zeroLocus Q | eval y.val t ∈ Eᶜ} ⊆
      {y : zeroLocus Q | eval y.val t ∈ Sᶜ} := fun _ hy h => hy (Or.inl h)
  exact closure_mono hsub hh

/-- Denominator-cleared recovery of every coordinate from a plane pair in
the coordinate ring gives injectivity on actual complex points away from
finitely many base values. -/
theorem exists_finite_exceptional_set_of_affine_coordinate_recovery
    (Q : Ideal (MvPolynomial σ ℂ))
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q))
    (t u : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hrec : ∀ i : σ, ∃ d : Polynomial ℂ, d ≠ 0 ∧
      ∃ E : Polynomial (Polynomial ℂ),
        f d * Ideal.Quotient.mk Q (X i) =
          E.eval₂ f.toRingHom (Ideal.Quotient.mk Q u)) :
    ∃ S : Set ℂ, S.Finite ∧ Set.InjOn
      (fun x : zeroLocus Q => (eval x.val t, eval x.val u)) {x | eval x.val t ∈ Sᶜ} := by
  classical
  choose d hd E hE using hrec
  let S : Set ℂ := ⋃ i, {a | (d i).IsRoot a}
  have hS : S.Finite := Set.finite_iUnion fun i => Polynomial.finite_setOf_isRoot (hd i)
  refine ⟨S, hS, ?_⟩
  have eval_eq (x : zeroLocus Q) (i : σ) :
      (d i).eval (eval x.val t) * x.val i =
        (E i).eval₂ (Polynomial.evalRingHom (eval x.val t)) (eval x.val u) := by
    let φ : (MvPolynomial σ ℂ ⧸ Q) →ₐ[ℂ] ℂ :=
      Ideal.Quotient.liftₐ Q (MvPolynomial.aeval x.val) fun a ha =>
        (mem_zeroLocus_iff.mp x.property) a ha
    have hφ (a : MvPolynomial σ ℂ) : φ (Ideal.Quotient.mk Q a) = eval x.val a := rfl
    have he : φ.comp f = Polynomial.aeval (eval x.val t) := by
      apply Polynomial.algHom_ext
      change φ (f Polynomial.X) = Polynomial.aeval (eval x.val t) Polynomial.X
      rw [← ht, hφ, Polynomial.aeval_X]
    have hh : φ.toRingHom.comp f.toRingHom = Polynomial.evalRingHom (eval x.val t) :=
      congrArg AlgHom.toRingHom he
    have hd' : φ (f (d i)) = (d i).eval (eval x.val t) := by
      have h := congrArg (fun g : Polynomial ℂ →+* ℂ => g (d i)) hh
      exact h
    have h := congrArg φ (hE i)
    rw [map_mul, hd', hφ, MvPolynomial.eval_X] at h
    have heval := Polynomial.hom_eval₂ (E i) f.toRingHom φ.toRingHom (Ideal.Quotient.mk Q u)
    rw [hh] at heval
    change φ _ = _ at heval
    have hu : φ.toRingHom (Ideal.Quotient.mk Q u) = eval x.val u := hφ u
    rw [hu] at heval
    rw [heval] at h
    exact h
  intro x hx y hy hxy
  apply Subtype.ext
  funext i
  have h1 : eval x.val t = eval y.val t := congrArg Prod.fst hxy
  have h2 : eval x.val u = eval y.val u := congrArg Prod.snd hxy
  have hdi : (d i).eval (eval x.val t) ≠ 0 :=
    fun he => hx (Set.mem_iUnion.mpr ⟨i, he⟩)
  apply mul_left_cancel₀ hdi
  rw [eval_eq x i, h1, h2, ← eval_eq y i]

/-- A prime finite affine curve is connected whenever one plane variable
recovers its coordinates rationally with denominators in the base alone.
The finitely many exceptional fibers are included by density. -/
theorem connectedSpace_affine_of_coordinate_recovery
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t u : MvPolynomial σ ℂ) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hrec : ∀ i : σ, ∃ d : Polynomial ℂ, d ≠ 0 ∧
      ∃ E : Polynomial (Polynomial ℂ),
        f d * Ideal.Quotient.mk Q (X i) =
          E.eval₂ f.toRingHom (Ideal.Quotient.mk Q u)) :
    ConnectedSpace (zeroLocus Q) := by
  obtain ⟨S, hS, hinj⟩ := exists_finite_exceptional_set_of_affine_coordinate_recovery Q f t u ht hrec
  obtain ⟨P, hP, hirr, hplane⟩ :=
    exists_monic_irreducible_plane_image_of_finite_projection Q f hf hfi t u ht
  let E : Set ℂ := S ∪ {z | ¬ (P.map (Polynomial.evalRingHom z)).Separable}
  have hE : E.Finite := hS.union (finite_nonseparable_specializations_of_irreducible P hP hirr)
  have hsep : ∀ a ∈ Eᶜ, (P.map (Polynomial.evalRingHom a)).Separable := by
    intro a ha
    exact not_not.mp (fun h => ha (Or.inr h))
  exact connectedSpace_affine_of_injective_regular_plane_projection Q f hf t u ht P hP hirr
    hplane hE hsep (hinj.mono (fun _ hy h => hy (Or.inl h)))
    (dense_affine_finite_projection_off_finite Q f hf hfi t ht hE)

end MOC
