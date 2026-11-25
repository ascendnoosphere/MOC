import MOC.IntegralGoingDown
import MOC.PolynomialFiberComponents
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! An irreducible affine curve through a point of a positive-dimensional fiber. -/

open MvPolynomial

namespace MOC

noncomputable section

variable {K σ ι : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ] [Fintype ι]

private theorem exists_finite_curve_quotient
    (B : Type*) [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    (φ : B →ₐ[K] K) (hφ : RingHom.ker φ ≠ ⊥) :
    ∃ R : Ideal B, R.IsPrime ∧ R < RingHom.ker φ ∧
      ∃ f : Polynomial K →ₐ[K] (B ⧸ R), Function.Injective f ∧ f.Finite := by
  obtain ⟨s, g, hgi, hgf⟩ := exists_finite_inj_algHom_of_fg K B
  cases s with
  | zero =>
      let A := MvPolynomial (Fin 0) K
      letI : Algebra A B := g.toRingHom.toAlgebra
      letI : Module.Finite A B := hgf
      have hA : IsField A :=
        (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).symm.toRingEquiv.toMulEquiv.isField
          (Field.toIsField K)
      have hB : IsField B := isField_of_isIntegral_of_isField' hA
      exact (Ring.not_isField_iff_exists_prime.mpr ⟨_, hφ, RingHom.ker_isPrime φ⟩ hB).elim
  | succ d =>
      let A := MvPolynomial (Fin (d + 1)) K
      letI : Algebra A B := g.toRingHom.toAlgebra
      letI : Module.Finite A B := hgf
      letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hgi
      letI : CharZero (FractionRing A) := charZero_of_injective_algebraMap (IsFractionRing.injective A _)
      letI : Algebra.HasGoingDown A B := finite_domain_goingDown_of_normal_base A B
      let M : Ideal B := RingHom.ker φ
      letI : M.IsPrime := RingHom.ker_isPrime φ
      let a : Fin (d + 1) → K := fun i => φ (g (X i))
      let h : A →ₐ[K] Polynomial K := MvPolynomial.aeval (Fin.cases Polynomial.X
        (fun i : Fin d => Polynomial.C (a i.succ)))
      let J : Ideal A := RingHom.ker h
      letI : J.IsPrime := RingHom.ker_isPrime h
      have hsurj : Function.Surjective h := by
        let u : Polynomial K →ₐ[K] A := Polynomial.aeval (X (0 : Fin (d + 1)))
        have hu : h.comp u = AlgHom.id K (Polynomial K) := by
          apply Polynomial.algHom_ext
          change h (u Polynomial.X) = Polynomial.X
          simp [h, u, Polynomial.aeval_X, MvPolynomial.aeval_X]
        intro p
        exact ⟨u p, AlgHom.congr_fun hu p⟩
      have hcomp : (Polynomial.aeval (a 0)).comp h = φ.comp g := by
        apply MvPolynomial.algHom_ext
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [h, a]
        · simp [h, a]
      have hJ : J < M.under A := by
        refine SetLike.lt_iff_le_and_exists.mpr ⟨?_, X 0 - C (a 0), ?_, ?_⟩
        · intro p hp
          change h p = 0 at hp
          change φ (g p) = 0
          have hf := AlgHom.congr_fun hcomp p
          change Polynomial.aeval (a 0) (h p) = φ (g p) at hf
          rw [hp, map_zero] at hf
          exact hf.symm
        · change φ (g (X 0 - C (a 0))) = 0
          simp [a]
        · change h (X 0 - C (a 0)) ≠ 0
          have hX : h (X 0 - C (a 0)) = Polynomial.X - Polynomial.C (a 0) := by
            simp [h, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
          simpa [hX, sub_ne_zero] using Polynomial.X_ne_C (a 0)
      obtain ⟨R, hRM, hR, hRover⟩ :=
        M.exists_ideal_lt_liesOver_of_lt (p := J) (q := M.under A) hJ
      have hcomap : R.comap g = J := hRover.over.symm
      let g' : A ⧸ J →ₐ[K] B ⧸ R := Ideal.quotientMapₐ R g hcomap.ge
      have hg'i : Function.Injective g' := Ideal.quotientMap_injective' hcomap.le
      have hg'f : g'.Finite := by
        apply AlgHom.Finite.of_comp_finite (f := Ideal.Quotient.mkₐ K J)
        rw [Ideal.quotient_map_comp_mkₐ]
        exact (AlgHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective K R)).comp hgf
      let e : A ⧸ J ≃ₐ[K] Polynomial K := Ideal.quotientKerAlgEquivOfSurjective hsurj
      exact ⟨R, hR, hRM, g'.comp e.symm.toAlgHom, hg'i.comp e.symm.injective,
        hg'f.comp (AlgHom.Finite.of_surjective _ e.symm.surjective)⟩

/-- The zero locus of a prime strictly below the point ideal of a
polynomial fiber contains a curve through the point. -/
theorem exists_finite_curve_of_polynomial_fiber_of_prime
    (p : ι → MvPolynomial σ K) (z : σ → K)
    (P : Ideal (MvPolynomial σ K)) (hP : P.IsPrime)
    (hp : ∀ i, p i - C (eval z (p i)) ∈ P)
    (hPQ : P < vanishingIdeal ({z} : Set (σ → K))) :
    ∃ Q : Ideal (MvPolynomial σ K), Q.IsPrime ∧
      (∀ i, p i - C (eval z (p i)) ∈ Q) ∧ Q < vanishingIdeal ({z} : Set (σ → K)) ∧
      ∃ f : Polynomial K →ₐ[K] (MvPolynomial σ K ⧸ Q), Function.Injective f ∧ f.Finite := by
  letI : P.IsPrime := hP
  let B := MvPolynomial σ K ⧸ P
  let q : MvPolynomial σ K →ₐ[K] B := Ideal.Quotient.mkₐ K P
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective K P
  letI : Algebra.FiniteType K B :=
    Algebra.FiniteType.of_surjective (Algebra.FiniteType.mvPolynomial K σ) q hq
  let φ : B →ₐ[K] K := Ideal.Quotient.liftₐ P (MvPolynomial.aeval z) fun f hf => by
    exact (mem_vanishingIdeal_singleton_iff z f).mp (hPQ.le hf)
  have hφeval (f : MvPolynomial σ K) : φ (q f) = eval z f := by
    change (MvPolynomial.aeval z) f = eval z f
    exact DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval z) f
  have hφ : RingHom.ker φ ≠ ⊥ := by
    obtain ⟨_, f, hfQ, hfP⟩ := SetLike.lt_iff_le_and_exists.mp hPQ
    have hf : q f ∈ RingHom.ker φ := (hφeval f).trans ((mem_vanishingIdeal_singleton_iff z f).mp hfQ)
    intro hbot
    apply hfP
    rw [hbot] at hf
    exact Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_bot.mp hf)
  obtain ⟨R, hR, hRM, g, hgi, hgf⟩ := exists_finite_curve_quotient B φ hφ
  letI : R.IsPrime := hR
  let q' : B →ₐ[K] B ⧸ R := Ideal.Quotient.mkₐ K R
  let Q : Ideal (MvPolynomial σ K) := RingHom.ker (q'.comp q)
  have hQR : Q = R.comap q := by
    ext f
    change Ideal.Quotient.mk R (q f) = 0 ↔ q f ∈ R
    exact Ideal.Quotient.eq_zero_iff_mem
  have hQ : Q.IsPrime := RingHom.ker_isPrime (q'.comp q)
  have hQP : Q < vanishingIdeal ({z} : Set (σ → K)) := by
    obtain ⟨hrle, x, hxφ, hxR⟩ := SetLike.lt_iff_le_and_exists.mp hRM
    obtain ⟨f, rfl⟩ := hq x
    refine SetLike.lt_iff_le_and_exists.mpr ⟨?_, f, ?_, ?_⟩
    · intro r hr
      rw [hQR] at hr
      exact (mem_vanishingIdeal_singleton_iff z r).mpr ((hφeval r).symm.trans (hrle hr))
    · exact (mem_vanishingIdeal_singleton_iff z f).mpr ((hφeval f).symm.trans hxφ)
    · rw [hQR]
      exact hxR
  have hsurj : Function.Surjective (q'.comp q) :=
    (Ideal.Quotient.mkₐ_surjective K R).comp hq
  let e : MvPolynomial σ K ⧸ Q ≃ₐ[K] B ⧸ R :=
    Ideal.quotientKerAlgEquivOfSurjective (f := q'.comp q) hsurj
  refine ⟨Q, hQ, ?_, hQP, e.symm.toAlgHom.comp g, e.symm.injective.comp hgi,
    (AlgHom.Finite.of_surjective _ e.symm.surjective).comp hgf⟩
  intro i
  change q' (q _) = 0
  rw [show q (p i - C (eval z (p i))) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (hp i), map_zero]

/-- The polynomial fiber has an irreducible curve through the chosen point
that is finite over an affine line. The curve retains the point even when
the finite projection branches there. -/
theorem exists_finite_curve_of_polynomial_fiber
    (p : ι → MvPolynomial σ K) (z : σ → K)
    (hcard : Fintype.card ι < Fintype.card σ) :
    ∃ Q : Ideal (MvPolynomial σ K), Q.IsPrime ∧
      (∀ i, p i - C (eval z (p i)) ∈ Q) ∧ Q < vanishingIdeal ({z} : Set (σ → K)) ∧
      ∃ f : Polynomial K →ₐ[K] (MvPolynomial σ K ⧸ Q), Function.Injective f ∧ f.Finite := by
  obtain ⟨P, hP, hp, hPQ⟩ := exists_prime_lt_of_polynomial_fiber p z hcard
  exact exists_finite_curve_of_polynomial_fiber_of_prime p z P hP hp hPQ

end

end MOC
