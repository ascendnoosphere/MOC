import MOC.FiniteCurveFibers
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Two polynomial coordinates of a finite affine curve have a monic plane equation. -/

open MvPolynomial

namespace MOC

noncomputable section

variable {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]

set_option maxHeartbeats 800000 in
/-- Every point of the monic plane model lifts to the finite affine curve. -/
theorem exists_monic_plane_image_of_finite_projection
    (Q : Ideal (MvPolynomial σ K)) [Q.IsPrime]
    (f : Polynomial K →ₐ[K] (MvPolynomial σ K ⧸ Q)) (hf : f.Finite)
    (hfi : Function.Injective f)
    (t u : MvPolynomial σ K) (ht : Ideal.Quotient.mk Q t = f Polynomial.X) :
    ∃ P : Polynomial (Polynomial K), P.Monic ∧ ∀ a b : K,
      (P.map (Polynomial.evalRingHom a)).IsRoot b ↔
        ∃ z ∈ zeroLocus Q, eval z t = a ∧ eval z u = b := by
  let A := Polynomial K
  let B := MvPolynomial σ K ⧸ Q
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : Module.Finite A B := hf
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hfi
  let v : B := Ideal.Quotient.mk Q u
  have hv : IsIntegral A v := Algebra.IsIntegral.isIntegral v
  let P := minpoly A v
  let ρ : Polynomial A →+* B := (Polynomial.aeval v).toRingHom
  have hker : RingHom.ker ρ = Ideal.span {P} := minpoly.ker_eval hv
  let S := ρ.range
  letI hAlg : Algebra S B := S.subtype.toAlgebra
  letI : Algebra A S := (ρ.rangeRestrict.comp Polynomial.C).toAlgebra
  letI : IsScalarTower A S B := IsScalarTower.of_algebraMap_eq fun c =>
    (Polynomial.aeval_C (R := A) v c).symm
  letI hInt : Algebra.IsIntegral S B := Algebra.IsIntegral.tower_top (R := A)
  have hinj : Function.Injective (algebraMap S B) := Subtype.val_injective
  refine ⟨P, minpoly.monic hv, fun a b => ?_⟩
  let e₀ := Polynomial.evalRingHom a
  let j₀ : Polynomial A →+* K := (Polynomial.evalRingHom b).comp (Polynomial.mapRingHom e₀)
  constructor
  · intro hroot
    have hker₀ : RingHom.ker ρ ≤ RingHom.ker j₀ := by
      rw [hker, Ideal.span_singleton_le_iff_mem]
      exact hroot
    let e := ρ.quotientKerEquivRange
    let jlift := Ideal.Quotient.lift (RingHom.ker ρ) j₀ fun _ hx => hker₀ hx
    let j : S →+* K := jlift.comp e.symm.toRingHom
    have he (p : Polynomial A) : e (Ideal.Quotient.mk (RingHom.ker ρ) p) = ρ.rangeRestrict p := by
      simp [e, RingHom.quotientKerEquivRange, RingHom.quotientKerEquivOfSurjective]
    have hj (p : Polynomial A) : j (ρ.rangeRestrict p) = j₀ p := by
      rw [← he]
      change jlift (e.symm (e (Ideal.Quotient.mk _ p))) = j₀ p
      simp only [RingEquiv.symm_apply_apply, jlift, Ideal.Quotient.lift_mk]
    have hjconst (c : K) : j₀ (Polynomial.C (Polynomial.C c)) = c := by
      change ((Polynomial.C (Polynomial.C c)).map e₀).eval b = c
      rw [Polynomial.map_C, Polynomial.eval_C] <;> exact Polynomial.eval_C
    have hjs : Function.Surjective j := fun c =>
      ⟨ρ.rangeRestrict (Polynomial.C (Polynomial.C c)), (hj _).trans (hjconst c)⟩
    let I : Ideal S := RingHom.ker j
    letI hMax : I.IsMaximal := RingHom.ker_isMaximal_of_surjective j hjs
    have hbot : RingHom.ker (algebraMap S B) ≤ I := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨M, hM, hMI⟩ := @Ideal.exists_ideal_over_maximal_of_isIntegral S _ B _ hAlg hInt I hMax hbot
    letI : M.IsMaximal := hM
    let N := M.comap (Ideal.Quotient.mk Q)
    have hN : N.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨z, hzN⟩ := (isMaximal_iff_eq_vanishingIdeal_singleton N).mp hN
    have hz : z ∈ zeroLocus Q := by
      intro p hp
      apply (mem_vanishingIdeal_singleton_iff z p).mp
      rw [← hzN]
      show Ideal.Quotient.mk Q p ∈ M
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      exact M.zero_mem
    let φ : B →ₐ[K] K := Ideal.Quotient.liftₐ Q (MvPolynomial.aeval z) fun p hp => hz p hp
    have hzero (x : B) (hx : x ∈ M) : φ x = 0 := by
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hn : p ∈ N := hx
      rw [hzN] at hn
      exact (mem_vanishingIdeal_singleton_iff z p).mp hn
    have hagree (p : Polynomial A) : φ (ρ p) = j₀ p := by
      let d := p - Polynomial.C (Polynomial.C (j₀ p))
      have hd : j₀ d = 0 := by rw [show d = p - Polynomial.C (Polynomial.C (j₀ p)) from rfl,
        map_sub, hjconst, sub_self]
      have hin : ρ.rangeRestrict d ∈ I := (hj d).trans hd
      rw [← hMI] at hin
      have h := hzero (ρ d) hin
      have hC : ρ (Polynomial.C (Polynomial.C (j₀ p))) = algebraMap K B (j₀ p) := by
        change Polynomial.aeval v (Polynomial.C (Polynomial.C (j₀ p))) = _
        rw [Polynomial.aeval_C]
        exact f.commutes (j₀ p)
      change φ (ρ (p - Polynomial.C (Polynomial.C (j₀ p)))) = 0 at h
      rw [map_sub, map_sub, hC, AlgHom.commutes] at h
      exact sub_eq_zero.mp h
    refine ⟨z, hz, ?_, ?_⟩
    · have h := hagree (Polynomial.C Polynomial.X)
      have hρ : ρ (Polynomial.C Polynomial.X) = f Polynomial.X := by
        change Polynomial.aeval v (Polynomial.C Polynomial.X) = f Polynomial.X
        rw [Polynomial.aeval_C]
        rfl
      have hjX : j₀ (Polynomial.C Polynomial.X) = a := by
        change Polynomial.eval b
            (Polynomial.map (Polynomial.evalRingHom a) (Polynomial.C Polynomial.X)) = a
        rw [Polynomial.map_C, Polynomial.eval_C]
        exact Polynomial.eval_X
      have hφt : φ (Ideal.Quotient.mk Q t) = eval z t := rfl
      rw [hρ, ← ht] at h
      exact hφt.symm.trans (h.trans hjX)
    · have h := hagree Polynomial.X
      have hρ : ρ Polynomial.X = v := Polynomial.aeval_X v
      have hjX : j₀ Polynomial.X = b := by
        change Polynomial.eval b (Polynomial.map (Polynomial.evalRingHom a) Polynomial.X) = b
        rw [Polynomial.map_X]
        exact Polynomial.eval_X
      have hφu : φ v = eval z u := rfl
      rw [hρ] at h
      exact hφu.symm.trans (h.trans hjX)
  · rintro ⟨z, hz, rfl, rfl⟩
    let φ : B →ₐ[K] K := Ideal.Quotient.liftₐ Q (MvPolynomial.aeval z) fun p hp => hz p hp
    have he : φ.comp f = Polynomial.aeval (eval z t) := by
      apply Polynomial.algHom_ext
      change φ (f Polynomial.X) = Polynomial.aeval (eval z t) Polynomial.X
      calc
        φ (f Polynomial.X) = φ (Ideal.Quotient.mk Q t) := congrArg φ ht.symm
        _ = eval z t := rfl
        _ = Polynomial.aeval (eval z t) Polynomial.X := (Polynomial.aeval_X _).symm
    have he' : φ.toRingHom.comp (algebraMap A B) = e₀ := congrArg AlgHom.toRingHom he
    have hp : Polynomial.eval₂ (algebraMap A B) v P = 0 := minpoly.aeval A v
    have h := (Polynomial.hom_eval₂ (p := P) (f := algebraMap A B) (g := φ.toRingHom) v).symm.trans
      ((congrArg φ.toRingHom hp).trans (map_zero _))
    rw [he', show φ.toRingHom v = eval z u from rfl] at h
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using h

end

end MOC
