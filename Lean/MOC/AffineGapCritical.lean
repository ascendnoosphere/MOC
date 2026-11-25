import Mathlib.Topology.Separation.Connected
import MOC.FiniteCurveBranchValues
import MOC.FiniteCurvePrimitiveCoordinate
import Mathlib.RingTheory.Localization.Integral

/-! A generically separable plane polynomial has finitely many nonseparable fibers.
Monicity over the coefficient ring is not needed. -/

open Polynomial
open scoped nonZeroDivisors

namespace MOC

/-- A separable fraction-field equation, including a cleared minimal
polynomial in the gap coordinate, has only finitely many nonsimple fibers. -/
theorem finite_nonseparable_specializations_of_fraction_separable
    (P : Polynomial (Polynomial ℂ))
    (hsep : (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable) :
    Set.Finite {z : ℂ | ¬ (P.map (evalRingHom z)).Separable} := by
  classical
  let A := Polynomial ℂ
  let K := FractionRing A
  let i : A →+* K := algebraMap A K
  let U := P.map i
  obtain ⟨V, W, hVW⟩ := (separable_def' _).mp hsep
  change V * U + W * U.derivative = 1 at hVW
  obtain ⟨v, hv⟩ := IsLocalization.integerNormalization_map_to_map A⁰ V
  obtain ⟨w, hw⟩ := IsLocalization.integerNormalization_map_to_map A⁰ W
  let V' := IsLocalization.integerNormalization A⁰ V
  let W' := IsLocalization.integerNormalization A⁰ W
  have hvmap : V'.map i = C (i (v : A)) * V := by
    rw [← algebraMap_smul K (v : A) V, Polynomial.smul_eq_C_mul] at hv
    exact hv
  have hwmap : W'.map i = C (i (w : A)) * W := by
    rw [← algebraMap_smul K (w : A) W, Polynomial.smul_eq_C_mul] at hw
    exact hw
  let p : Polynomial ℂ := (v : A) * (w : A)
  have hp0 : p ≠ 0 :=
    mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp v.property)
      (mem_nonZeroDivisors_iff_ne_zero.mp w.property)
  let T := C (w : A) * V'
  let Q := C (v : A) * W'
  have hbez : C p = P * T + P.derivative * Q := by
    apply Polynomial.map_injective i (IsFractionRing.injective A K)
    simp only [T, Q, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hvmap, hwmap]
    have hUd : P.derivative.map i = U.derivative := (Polynomial.derivative_map P i).symm
    rw [hUd, ← show U = P.map i from rfl]
    rw [Polynomial.map_C, show i p = i (v : A) * i (w : A) from map_mul i _ _, C_mul]
    calc
      _ = C (i (v : A)) * C (i (w : A)) * (V * U + W * U.derivative) := by rw [hVW, mul_one]
      _ = _ := by ring
  apply (Polynomial.finite_setOf_isRoot hp0).subset
  intro z hz
  change ¬ (P.map (evalRingHom z)).Separable at hz
  change p.eval z = 0
  apply Classical.byContradiction
  intro hn'
  let f := evalRingHom z
  let U := P.map f
  let T' := T.map f
  let Q' := Q.map f
  have heval : (C (p.eval z) : ℂ[X]) = U * T' + U.derivative * Q' := by
    have hh := congrArg (Polynomial.map f) hbez
    rw [Polynomial.map_C] at hh
    simpa only [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, ← derivative_map, coe_evalRingHom] using hh
  apply hz
  apply (separable_def' _).mpr
  refine ⟨T' * C ((p.eval z)⁻¹), Q' * C ((p.eval z)⁻¹), ?_⟩
  change (T' * C ((p.eval z)⁻¹)) * U + (Q' * C ((p.eval z)⁻¹)) * U.derivative = 1
  calc
    _ = (U * T' + U.derivative * Q') * C ((p.eval z)⁻¹) := by ring
    _ = 1 := by rw [← heval, ← C_mul, mul_inv_cancel₀ hn', C_1]


/-- Exchange the two polynomial variables. -/
private noncomputable def swapHom : Polynomial (Polynomial ℂ) →+* Polynomial (Polynomial ℂ) :=
  eval₂RingHom (eval₂RingHom (Polynomial.C.comp Polynomial.C) Polynomial.X)
    (Polynomial.C Polynomial.X)

private theorem swapHom_sq : swapHom.comp swapHom = RingHom.id _ := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro a
      simp [swapHom]
    · simp [swapHom]
  · simp [swapHom]

private theorem swapInvolutive : Function.Involutive swapHom :=
  fun p => DFunLike.congr_fun swapHom_sq p

private noncomputable def swapEquiv : Polynomial (Polynomial ℂ) ≃+* Polynomial (Polynomial ℂ) :=
  RingEquiv.ofBijective swapHom ⟨swapInvolutive.injective, swapInvolutive.surjective⟩

private theorem swapSpecialization (P : Polynomial (Polynomial ℂ)) (a b : ℂ) :
    ((swapEquiv P).map (evalRingHom b)).eval a = (P.map (evalRingHom a)).eval b := by
  let ep (x y : ℂ) : Polynomial (Polynomial ℂ) →+* ℂ :=
    eval₂RingHom (evalRingHom x) y
  have he : (ep b a).comp swapHom = ep a b := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro x
        simp [ep, swapHom]
      · simp [ep, swapHom]
    · simp [ep, swapHom]
  simpa only [ep, coe_eval₂RingHom, RingHom.coe_comp, Function.comp_apply,
    eval_map, swapEquiv, RingEquiv.ofBijective_apply] using DFunLike.congr_fun he P

/-- Reverse plane specialization has only finitely many nonsimple fibers
whenever the varied coordinate has infinitely many values on the plane model. -/
theorem exists_generic_reversed_plane_root_cover
    (P : Polynomial (Polynomial ℂ)) (hP : Irreducible P)
    (hvar : {w : ℂ | ∃ a, (P.map (evalRingHom a)).IsRoot w}.Infinite) :
    ∃ R : Polynomial (Polynomial ℂ), Irreducible R ∧
      (∀ a w, (R.map (evalRingHom w)).IsRoot a ↔ (P.map (evalRingHom a)).IsRoot w) ∧
      {w : ℂ | ¬ (R.map (evalRingHom w)).Separable ∨ R.leadingCoeff.eval w = 0}.Finite := by
  let R := swapEquiv P
  have hR : Irreducible R := (MulEquiv.irreducible_iff swapEquiv.toMulEquiv).2 hP
  have hswap (a w : ℂ) :
      (R.map (evalRingHom w)).IsRoot a ↔ (P.map (evalRingHom a)).IsRoot w := by
    simp only [IsRoot, R, swapSpecialization]
  have hdeg : R.natDegree ≠ 0 := by
    intro h
    have heq : R = C (R.coeff 0) := eq_C_of_natDegree_eq_zero h
    apply hvar
    have hR0 : R.coeff 0 ≠ 0 := fun hn => hR.ne_zero (heq.trans ((congrArg C hn).trans C_0))
    apply (finite_setOf_isRoot hR0).subset
    rintro w ⟨a, ha⟩
    have hr := (hswap a w).mpr ha
    rw [heq] at hr
    simpa only [IsRoot, map_C, eval_C, coe_evalRingHom] using hr
  have hfrac : (R.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable :=
    ((hR.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map.mp hR).separable
  exact ⟨R, hR, hswap, (finite_nonseparable_specializations_of_fraction_separable R hfrac).union
    (finite_setOf_isRoot (leadingCoeff_ne_zero.mpr hR.ne_zero))⟩


/-- A varying polynomial gap on a prime finite affine curve has an exact
reversed plane model (gap, old parameter). Away from finitely many gap
values, every old parameter is a simple root and has a holomorphic
local branch as a function of the gap. -/
theorem exists_reversed_affine_gap_plane_model_off_finite
    {σ : Type*} [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f) (t g : MvPolynomial σ ℂ)
    (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (hvar : ∃ x y : MvPolynomial.zeroLocus Q, MvPolynomial.eval x.val g ≠ MvPolynomial.eval y.val g) :
    ∃ R : Polynomial (Polynomial ℂ), Irreducible R ∧
      (∀ a w, (R.map (evalRingHom w)).IsRoot a ↔
        ∃ x : MvPolynomial.zeroLocus Q, MvPolynomial.eval x.val t = a ∧ MvPolynomial.eval x.val g = w) ∧
      {w : ℂ | ¬ (R.map (evalRingHom w)).Separable ∨ R.leadingCoeff.eval w = 0}.Finite := by
  letI : ConnectedSpace (MvPolynomial.zeroLocus Q) :=
    connectedSpace_prime_finite_affine_curve Q f hf hfi t ht
  obtain ⟨P, _, hP, hp⟩ :=
    exists_monic_irreducible_plane_image_of_finite_projection Q f hf hfi t g ht
  let G (x : MvPolynomial.zeroLocus Q) := MvPolynomial.eval x.val g
  have hInf : (Set.range G).Infinite := by
    have hc : IsPreconnected (Set.range G) :=
      (isConnected_range (g.continuous_eval.comp continuous_subtype_val)).isPreconnected
    obtain ⟨x,y,hxy⟩ := hvar
    exact hc.infinite_of_nontrivial ⟨G x, ⟨x,rfl⟩, G y, ⟨y,rfl⟩, hxy⟩
  have hlarge : {w : ℂ | ∃ a, (P.map (evalRingHom a)).IsRoot w}.Infinite :=
    hInf.mono (by
      rintro w ⟨x, rfl⟩
      exact ⟨MvPolynomial.eval x.val t, (hp _ _).mpr ⟨x.val, x.property, rfl, rfl⟩⟩)
  obtain ⟨R, hR, heq, hfin⟩ := exists_generic_reversed_plane_root_cover P hP hlarge
  refine ⟨R, hR, fun a w => (heq a w).trans ((hp a w).trans ?_), hfin⟩
  exact ⟨fun ⟨x,hx,ht',hg⟩ => ⟨⟨x,hx⟩,ht',hg⟩, fun ⟨x,ht',hg⟩ => ⟨x.val,x.property,ht',hg⟩⟩


end MOC
