import MOC.ContactCurveGoingDown
import MOC.FiniteNormalGoingDown
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! A finite affine curve through a pinned point of a positive-dimensional
complex affine slice. -/

open Set MvPolynomial

namespace MOC

/-- A nonzero maximal ideal in a finite type complex domain admits a finite
curve quotient through it that preserves any chosen nonzero element. -/
theorem exists_finite_curve_through_maximal_avoiding
    {B : Type*} [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (m : Ideal B) [m.IsMaximal] (hm : m ≠ ⊥) (b : B) (hb : b ≠ 0) :
    ∃ q : Ideal B, q ≤ m ∧ q.IsPrime ∧
      ∃ F : Polynomial ℂ →ₐ[ℂ] B ⧸ q,
        F.Finite ∧ Function.Injective F ∧ Ideal.Quotient.mk q b ≠ 0 := by
  obtain ⟨n, G, hGinj, hGfin⟩ := exists_finite_inj_algHom_of_fg ℂ B
  let A := MvPolynomial (Fin n) ℂ
  letI : Algebra A B := G.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (G.commutes c).symm
  letI : Module.Finite A B := hGfin
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hGinj
  have hn : n ≠ 0 := by
    intro h
    subst n
    have hfA : IsField A := (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).toMulEquiv.isField _
      (Field.toIsField ℂ)
    have hfB : IsField B := isField_of_isIntegral_of_isField' hfA
    exact (Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mpr
      ⟨m, bot_lt_iff_ne_bot.mpr hm, lt_top_iff_ne_top.mpr (Ideal.IsMaximal.ne_top inferInstance)⟩) hfB
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  letI : IsIntegrallyClosed A := by dsimp [A]; infer_instance
  letI : CharZero A := by dsimp [A]; infer_instance
  letI : Algebra.HasGoingDown A B := hasGoingDown_of_finite_normal_base A B
  let mA : Ideal A := m.under A
  have hmA : mA.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  obtain ⟨x, hx⟩ := (isMaximal_iff_eq_vanishingIdeal_singleton mA).mp hmA
  have hker : m.under A = RingHom.ker (MvPolynomial.eval x) := by
    rw [show m.under A = vanishingIdeal {x} from hx]
    ext p
    exact mem_vanishingIdeal_singleton_iff x p
  exact exists_polynomial_normalization_curve_avoiding m x hker b hb

/-- If the affine equations leave a prime strictly below the ideal of a
pinned point, there is a finite affine curve through that point, and the
curve can be chosen to preserve any polynomial nonzero in that prime. -/
theorem exists_finite_affine_curve_from_prime_below_point
    {σ : Type*} [Fintype σ] (x : σ → ℂ)
    (I : Ideal (MvPolynomial σ ℂ)) [I.IsPrime]
    (hI : I < RingHom.ker (MvPolynomial.eval x))
    (w : MvPolynomial σ ℂ) (hw : w ∉ I) :
    ∃ Q : Ideal (MvPolynomial σ ℂ),
      I ≤ Q ∧ Q ≤ RingHom.ker (MvPolynomial.eval x) ∧ Q.IsPrime ∧ w ∉ Q ∧
      ∃ f : Polynomial ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ Q),
        f.Finite ∧ Function.Injective f ∧
        ∃ t : MvPolynomial σ ℂ, Ideal.Quotient.mk Q t = f Polynomial.X := by
  let B := MvPolynomial σ ℂ ⧸ I
  let k : MvPolynomial σ ℂ →ₐ[ℂ] B := Ideal.Quotient.mkₐ ℂ I
  let φ : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (fun a ha => hI.le ha)
  let m := RingHom.ker φ
  have hφs : Function.Surjective φ := fun c => ⟨algebraMap ℂ B c, φ.commutes c⟩
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφs
  have hm : m ≠ ⊥ := by
    obtain ⟨w, hw, hwi⟩ := SetLike.exists_of_lt hI
    intro he
    have ha : k w ∈ m := hw
    rw [he, Ideal.mem_bot, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact hwi ha
  letI : Algebra.FiniteType ℂ B := Algebra.FiniteType.of_surjective inferInstance k (Ideal.Quotient.mkₐ_surjective _ _)
  have hb : k w ≠ 0 := by
    change Ideal.Quotient.mk I w ≠ 0
    exact mt Ideal.Quotient.eq_zero_iff_mem.mp hw
  obtain ⟨q, hqm, hq, F, hFfin, hFinj, hwq⟩ := exists_finite_curve_through_maximal_avoiding m hm (k w) hb
  let ψ := (Ideal.Quotient.mkₐ ℂ q).comp k
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mkₐ_surjective ℂ q).comp (Ideal.Quotient.mkₐ_surjective ℂ I)
  let Q := RingHom.ker ψ
  let e := Ideal.quotientKerAlgEquivOfSurjective hψ
  let f := e.symm.toAlgHom.comp F
  have hff : f.Finite := (AlgHom.Finite.of_surjective _ e.symm.surjective).comp hFfin
  have hfinj : Function.Injective f := e.symm.injective.comp hFinj
  letI : q.IsPrime := hq
  letI : Q.IsPrime := RingHom.ker_isPrime ψ
  refine ⟨Q, ?_, ?_, inferInstance, ?_, f, hff, hfinj, ?_⟩
  · intro a ha
    change ψ a = 0
    change (Ideal.Quotient.mk q) (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro a ha
    have hab : k a ∈ q := Ideal.Quotient.eq_zero_iff_mem.mp ha
    exact hqm hab
  · exact hwq
  · exact Ideal.Quotient.mk_surjective (f Polynomial.X)

end MOC
