import MOC.FiniteCurveReprojection
import MOC.PlanePolynomialExceptional
import MOC.PrimitivePlaneModel
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-! A nonconstant polynomial on an irreducible affine curve is a covering
projection outside a finite subset of the complex line. -/

open Polynomial Set

namespace MOC

abbrev CurveProjectionPoints {σ : Type*} (Q : Ideal (MvPolynomial σ ℂ))
    (x : MvPolynomial σ ℂ) (S : Set ℂ) :=
  {z : σ → ℂ // z ∈ MvPolynomial.zeroLocus Q ∧ MvPolynomial.eval z x ∈ S}

private theorem exists_plane_chart_of_algebraic_projection {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime] (x : MvPolynomial σ ℂ)
    (g : ℂ[X] →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q) (hgi : Function.Injective g)
    (hgx : g Polynomial.X = Ideal.Quotient.mk Q x)
    (hg : letI := g.toRingHom.toAlgebra; Algebra.IsAlgebraic ℂ[X] (MvPolynomial σ ℂ ⧸ Q)) :
    ∃ (P : Polynomial ℂ[X]) (D : ℂ[X]) (yPoly : MvPolynomial σ ℂ) (N : σ → Polynomial ℂ[X]),
      0 < P.natDegree ∧ D ≠ 0 ∧
      (P.map (algebraMap ℂ[X] (FractionRing ℂ[X]))).Separable ∧
      ∀ S : Set ℂ, (∀ t ∈ S, D.eval t ≠ 0) →
        ∃ e : CurveProjectionPoints Q x S ≃ₜ PlanePolynomialRoots P S,
          (∀ z, (e z).val.1 = (⟨MvPolynomial.eval z.val x, z.property.2⟩ : ↥S)) ∧
          (∀ z, (e z).val.2 = MvPolynomial.eval z.val yPoly) ∧
          ∀ z a, (e.symm z).val a =
            planePolynomialEval (N a) (z.val.1.val, z.val.2) / D.eval z.val.1.val := by
  classical
  let R := ℂ[X]
  let B := MvPolynomial σ ℂ ⧸ Q
  let E := FractionRing B
  let j := algebraMap B E
  letI : Algebra R B := g.toRingHom.toAlgebra
  letI : NoZeroSMulDivisors R B := NoZeroSMulDivisors.iff_algebraMap_injective.mpr hgi
  obtain ⟨y, hyi, hsep, D, N, hD, hcoord⟩ :=
    exists_integral_primitive_curve_coordinates Q g hgi hg
  obtain ⟨yPoly, hyPoly⟩ := Ideal.Quotient.mk_surjective y
  let P := minpoly R y
  refine ⟨P, D, yPoly, N, minpoly.natDegree_pos hyi, hD, hsep, fun S hS => ?_⟩

  let A := AdjoinRoot P
  let i : A →+* B := (AdjoinRoot.liftHom P y (minpoly.aeval R y)).toRingHom
  have hi : Function.Injective i := by
    refine (injective_iff_map_eq_zero i).2 fun a ha => ?_
    obtain ⟨p, hp⟩ := (AdjoinRoot.mk_surjective (g := P)) a
    subst hp
    have hap : Polynomial.aeval y p = 0 := by simpa [i] using ha
    exact (AdjoinRoot.mk_eq_zero (f := P)).2 (minpoly.isIntegrallyClosed_dvd hyi hap)
  have hiOf (a : R) : i (AdjoinRoot.of P a) = g a := by
    change AdjoinRoot.liftHom P y (minpoly.aeval R y) (AdjoinRoot.of P a) = g a
    rw [AdjoinRoot.liftHom_of]
    rfl
  have hiRoot : i (AdjoinRoot.root P) = y :=
    AdjoinRoot.liftHom_root P (minpoly.aeval R y)
  have hiMk (p : R[X]) : i (AdjoinRoot.mk P p) = Polynomial.aeval y p :=
    AdjoinRoot.liftHom_mk P (minpoly.aeval R y)
  let d : A := AdjoinRoot.of P D
  let L := Localization.Away d
  let l := algebraMap A L
  have hji : Function.Injective (j.comp i) := (IsFractionRing.injective B E).comp hi
  have hunit : IsUnit ((j.comp i) d) := by
    rw [RingHom.comp_apply, show i d = g D from hiOf D]
    exact ((map_ne_zero_iff j (IsFractionRing.injective B E)).2 ((map_ne_zero_iff g hgi).2 hD)).isUnit
  let k : L →+* E := IsLocalization.Away.lift d hunit
  have hk (a : A) : k (l a) = j (i a) := IsLocalization.Away.lift_eq _ _ _
  have hki : Function.Injective k := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers d) k).2
    intro a b
    change l a = l b ↔ k (l a) = k (l b)
    rw [hk, hk]
    exact ⟨fun h => by simpa only [hk] using congrArg k h, fun h => congrArg l (hji h)⟩
  let q (a : σ) : L := IsLocalization.Away.invSelf d * l (AdjoinRoot.mk P (N a))
  have hq (a : σ) : l d * q a = l (AdjoinRoot.mk P (N a)) := by
    change l d * (IsLocalization.Away.invSelf d * l (AdjoinRoot.mk P (N a))) = _
    rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  have hdE : k (l d) ≠ 0 := by rw [hk]; exact hunit.ne_zero
  have hkq (a : σ) : k (q a) = j (Ideal.Quotient.mk Q (MvPolynomial.X a)) := by
    apply mul_left_cancel₀ hdE
    rw [← map_mul, hq, hk, hiMk, hk, show i d = g D from hiOf D,
      ← map_mul, hcoord]
  let c : ℂ →+* L := l.comp ((AdjoinRoot.of P).comp Polynomial.C)
  let ψ : MvPolynomial σ ℂ →+* L := MvPolynomial.eval₂Hom c q
  have hψ : k.comp ψ = j.comp (Ideal.Quotient.mk Q) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change k (MvPolynomial.eval₂Hom c q (MvPolynomial.C a)) = j (Ideal.Quotient.mk Q (MvPolynomial.C a))
      rw [MvPolynomial.eval₂Hom_C]
      change k (l (AdjoinRoot.of P (Polynomial.C a))) = _
      rw [hk, hiOf]
      exact congrArg j (g.commutes a)
    · intro a
      change k (MvPolynomial.eval₂Hom c q (MvPolynomial.X a)) = _
      rw [MvPolynomial.eval₂Hom_X', hkq]
      rfl
  have hψ' (p : MvPolynomial σ ℂ) : k (ψ p) = j (Ideal.Quotient.mk Q p) :=
    RingHom.congr_fun hψ p
  have hψzero (p : MvPolynomial σ ℂ) (hp : p ∈ Q) : ψ p = 0 := by
    apply hki
    rw [hψ', Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]
  have hψx : ψ x = l (AdjoinRoot.of P Polynomial.X) := by
    apply hki
    rw [hψ', hk, hiOf, hgx]
  have hψy : ψ yPoly = l (AdjoinRoot.root P) := by
    apply hki
    rw [hψ', hk, hiRoot, hyPoly]

  let X := CurveProjectionPoints Q x S
  let Y := PlanePolynomialRoots P S
  let pointEval (z : X) : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q (MvPolynomial.aeval z.val)
    (fun p hp => (MvPolynomial.mem_zeroLocus_iff.mp z.property.1) p hp)
  have hpointEval (z : X) (p : MvPolynomial σ ℂ) :
      pointEval z (Ideal.Quotient.mk Q p) = MvPolynomial.eval z.val p := rfl
  have hpointBase (z : X) : (pointEval z).comp g = Polynomial.aeval (MvPolynomial.eval z.val x) := by
    apply Polynomial.algHom_ext
    change pointEval z (g Polynomial.X) = _
    rw [hgx, hpointEval, Polynomial.aeval_X]
  have hpointPlane (z : X) (p : R[X]) : pointEval z (Polynomial.aeval y p) =
      planePolynomialEval p (MvPolynomial.eval z.val x, MvPolynomial.eval z.val yPoly) := by
    have hbase : (pointEval z).toRingHom.comp (algebraMap R B) =
        Polynomial.evalRingHom (MvPolynomial.eval z.val x) := congrArg AlgHom.toRingHom (hpointBase z)
    have hyz : (pointEval z).toRingHom y = MvPolynomial.eval z.val yPoly := hyPoly ▸ hpointEval z yPoly
    change (pointEval z).toRingHom (Polynomial.aeval y p) =
      (p.map (Polynomial.evalRingHom (MvPolynomial.eval z.val x))).eval
      (MvPolynomial.eval z.val yPoly)
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂ (p := p) (f := algebraMap R B)
      (g := (pointEval z).toRingHom) y, hbase, hyz, Polynomial.eval_map]
  let F (z : X) : Y := ⟨(⟨MvPolynomial.eval z.val x, z.property.2⟩, MvPolynomial.eval z.val yPoly), by
    change planePolynomialEval P (MvPolynomial.eval z.val x, MvPolynomial.eval z.val yPoly) = 0
    rw [← hpointPlane, minpoly.aeval, map_zero]⟩

  let xy (z : Y) : ℂ × ℂ := (z.val.1.val, z.val.2)
  let reconstruct (z : Y) (a : σ) : ℂ := planePolynomialEval (N a) (xy z) / D.eval (xy z).1
  have hden (z : Y) : D.eval (xy z).1 ≠ 0 := hS _ z.val.1.property
  let specialize (z : Y) : A →+* ℂ :=
    AdjoinRoot.lift (Polynomial.evalRingHom (xy z).1) (xy z).2 <| by
      rw [← Polynomial.eval_map]
      exact z.property
  have hspecOf (z : Y) (a : R) : specialize z (AdjoinRoot.of P a) = a.eval (xy z).1 :=
    AdjoinRoot.lift_of _
  have hspecMk (z : Y) (p : R[X]) : specialize z (AdjoinRoot.mk P p) = planePolynomialEval p (xy z) := by
    change _ = (p.map (Polynomial.evalRingHom (xy z).1)).eval (xy z).2
    rw [AdjoinRoot.lift_mk, Polynomial.eval_map]
  let liftSpecialize (z : Y) : L →+* ℂ :=
    IsLocalization.Away.lift d (show IsUnit (specialize z d) by
      change IsUnit (specialize z (AdjoinRoot.of P D))
      rw [hspecOf]
      exact (hden z).isUnit)
  have hlift (z : Y) (a : A) : liftSpecialize z (l a) = specialize z a :=
    IsLocalization.Away.lift_eq _ _ _
  have hliftq (z : Y) (a : σ) : liftSpecialize z (q a) = reconstruct z a := by
    have h := congrArg (liftSpecialize z) (hq a)
    rw [map_mul, hlift, hlift, show specialize z d = D.eval (xy z).1 from hspecOf z D, hspecMk] at h
    exact (eq_div_iff (hden z)).2 ((mul_comm _ _).trans h)
  have hspecial (z : Y) : (liftSpecialize z).comp ψ = MvPolynomial.eval (reconstruct z) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change liftSpecialize z (MvPolynomial.eval₂Hom c q (MvPolynomial.C a)) = _
      rw [MvPolynomial.eval₂Hom_C]
      change liftSpecialize z (l (AdjoinRoot.of P (Polynomial.C a))) = _
      rw [hlift, hspecOf, Polynomial.eval_C, MvPolynomial.eval_C]
    · intro a
      change liftSpecialize z (MvPolynomial.eval₂Hom c q (MvPolynomial.X a)) = _
      rw [MvPolynomial.eval₂Hom_X', hliftq, MvPolynomial.eval_X]
  have hspecial' (z : Y) (p : MvPolynomial σ ℂ) :
      liftSpecialize z (ψ p) = MvPolynomial.eval (reconstruct z) p := RingHom.congr_fun (hspecial z) p
  have hrecx (z : Y) : MvPolynomial.eval (reconstruct z) x = (xy z).1 := by
    rw [← hspecial', hψx, hlift, hspecOf, Polynomial.eval_X]
  have hrecy (z : Y) : MvPolynomial.eval (reconstruct z) yPoly = (xy z).2 := by
    rw [← hspecial', hψy, hlift]
    exact AdjoinRoot.lift_root _
  let G (z : Y) : X := ⟨reconstruct z, MvPolynomial.mem_zeroLocus_iff.mpr fun p hp => by
    rw [← hspecial', hψzero p hp, map_zero], hrecx z ▸ z.val.1.property⟩
  have hleft (z : X) : G (F z) = z := by
    apply Subtype.ext
    funext a
    have h := congrArg (pointEval z) (hcoord a)
    rw [map_mul, hpointEval, MvPolynomial.eval_X, hpointPlane] at h
    have hbase : pointEval z (g D) = D.eval (MvPolynomial.eval z.val x) := by
      rw [← AlgHom.comp_apply, hpointBase, Polynomial.coe_aeval_eq_eval]
    rw [hbase] at h
    change planePolynomialEval (N a) (xy (F z)) / D.eval (xy (F z)).1 = z.val a
    exact (div_eq_iff (hden (F z))).2 (h.symm.trans (mul_comm _ _))
  have hright (z : Y) : F (G z) = z :=
    Subtype.ext (Prod.ext (Subtype.ext (hrecx z)) (hrecy z))
  let e : X ≃ₜ Y :=
    { toEquiv := ⟨F, G, hleft, hright⟩
      continuous_toFun := by
        have hfirst : Continuous (fun z : X => (⟨MvPolynomial.eval z.val x, z.property.2⟩ : ↥S)) :=
          ((MvPolynomial.continuous_eval x).comp continuous_subtype_val).subtype_mk _
        exact (hfirst.prodMk ((MvPolynomial.continuous_eval yPoly).comp continuous_subtype_val)).subtype_mk _
      continuous_invFun := by
        have hxy : Continuous xy :=
          (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
            (continuous_snd.comp continuous_subtype_val)
        exact (continuous_pi fun a => ((continuous_planePolynomialEval (N a)).comp hxy).div₀
          (D.continuous.comp (continuous_fst.comp hxy)) hden).subtype_mk _ }
  exact ⟨e, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- Outside finitely many values, a nonconstant curve projection is a covering
and polynomial functions along any continuous local section are holomorphic. -/
theorem exists_curve_projection_covering_and_holomorphic_sections {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : ℂ[X] →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q) (hf : f.Finite) (hfi : Function.Injective f)
    (x : MvPolynomial σ ℂ)
    (hx : Ideal.Quotient.mk Q x ∉ Set.range (algebraMap ℂ (MvPolynomial σ ℂ ⧸ Q)))
    {T : Set ℂ} (hT : T.Finite) :
    ∃ S : Set ℂ, S.Finite ∧ T ⊆ S ∧
      (IsCoveringMap (fun z : CurveProjectionPoints Q x Sᶜ =>
        (⟨MvPolynomial.eval z.val x, z.property.2⟩ : ↥Sᶜ))) ∧
      ∀ (W : Set ℂ), IsOpen W → W ⊆ Sᶜ → ∀ z : ℂ → σ → ℂ,
        ContinuousOn z W → (∀ t ∈ W, z t ∈ MvPolynomial.zeroLocus Q) →
        (∀ t ∈ W, MvPolynomial.eval (z t) x = t) →
        ∀ p : MvPolynomial σ ℂ, DifferentiableOn ℂ (fun t => MvPolynomial.eval (z t) p) W := by
  let g : ℂ[X] →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q := Polynomial.aeval (Ideal.Quotient.mk Q x)
  have hgi : Function.Injective g := aeval_injective_of_not_scalar (K := ℂ) (Ideal.Quotient.mk Q x) hx
  obtain ⟨P, D, yPoly, N, hP, hD, hsep, hchart⟩ := exists_plane_chart_of_algebraic_projection Q x g hgi
    (Polynomial.aeval_X _) (algebraic_of_reprojecting_finite_curve f g hf hfi hgi)
  obtain ⟨S, hS, hTS, hdeg, hsep'⟩ := exists_finite_planePolynomial_exceptional_set P hP hsep
    (hT.union (Polynomial.finite_setOf_isRoot hD))
  have hden (t : ℂ) (ht : t ∈ Sᶜ) : D.eval t ≠ 0 := fun hroot => ht (hTS (Or.inr hroot))
  obtain ⟨e, he, hey, hrec⟩ := hchart Sᶜ hden
  refine ⟨S, hS, subset_union_left.trans hTS, ?_, ?_⟩
  · have hc := isCoveringMap_planePolynomialRoots P Sᶜ hP hdeg hsep'
    have heq : (fun z : PlanePolynomialRoots P Sᶜ => z.val.1) ∘ e =
        (fun z : CurveProjectionPoints Q x Sᶜ => (⟨MvPolynomial.eval z.val x, z.property.2⟩ : ↥Sᶜ)) :=
      funext he
    rw [← heq]
    intro t
    obtain ⟨hdiscrete, trivialization, ht⟩ := hc t
    exact IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨hdiscrete, trivialization.compHomeomorph e, ht⟩
  · intro W hW hWS z hz hzQ hzproj
    let y (t : ℂ) := MvPolynomial.eval (z t) yPoly
    let q (t : W) : CurveProjectionPoints Q x Sᶜ := ⟨z t.val, hzQ _ t.property, by
      rw [hzproj _ t.property]
      exact hWS t.property⟩
    have hfirst (t : W) : (e (q t)).val.1.val = t.val :=
      (congrArg (fun v : ↥Sᶜ => v.val) (he (q t))).trans (hzproj _ t.property)
    have hsecond (t : W) : (e (q t)).val.2 = y t.val := hey (q t)
    have hroot (t : ℂ) (ht : t ∈ W) : planePolynomialEval P (t, y t) = 0 := by
      have hs := (e (q ⟨t, ht⟩)).property
      change planePolynomialEval P ((e (q ⟨t, ht⟩)).val.1.val, (e (q ⟨t, ht⟩)).val.2) = 0 at hs
      rwa [hfirst ⟨t, ht⟩, hsecond ⟨t, ht⟩] at hs
    have hyd : DifferentiableOn ℂ y W := differentiableOn_of_continuous_planePolynomialRoot
      P hW y ((MvPolynomial.continuous_eval yPoly).comp_continuousOn' hz) hroot
      (fun t ht => hsep' ⟨t, hWS ht⟩)
    have hcoord (a : σ) : DifferentiableOn ℂ (fun t => z t a) W := by
      have hpair : DifferentiableOn ℂ (fun t : ℂ => (t, y t)) W := differentiableOn_id.prodMk hyd
      have hd := ((differentiable_planePolynomialEval (N a)).comp_differentiableOn hpair).div
        D.differentiableOn (fun t ht => hden t (hWS ht))
      apply hd.congr
      intro t ht
      have hs := hrec (e (q ⟨t, ht⟩)) a
      rwa [e.symm_apply_apply, hfirst ⟨t, ht⟩, hsecond ⟨t, ht⟩] at hs
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => simpa only [MvPolynomial.eval_C] using
        (differentiableOn_const c : DifferentiableOn ℂ (fun _ => c) W)
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | mul_X p a hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hcoord a)

/-- A finite affine curve over one parameter is a covering over a second
nonconstant parameter away from finitely many values. -/
theorem exists_isCoveringMap_curve_projection_off_finite {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : ℂ[X] →ₐ[ℂ] MvPolynomial σ ℂ ⧸ Q) (hf : f.Finite) (hfi : Function.Injective f)
    (x : MvPolynomial σ ℂ)
    (hx : Ideal.Quotient.mk Q x ∉ Set.range (algebraMap ℂ (MvPolynomial σ ℂ ⧸ Q)))
    {T : Set ℂ} (hT : T.Finite) :
    ∃ S : Set ℂ, S.Finite ∧ T ⊆ S ∧
      IsCoveringMap (fun z : CurveProjectionPoints Q x Sᶜ =>
        (⟨MvPolynomial.eval z.val x, z.property.2⟩ : ↥Sᶜ)) := by
  obtain ⟨S, hS, hTS, hc, _⟩ :=
    exists_curve_projection_covering_and_holomorphic_sections Q f hf hfi x hx hT
  exact ⟨S, hS, hTS, hc⟩

end MOC
