import MOC.FiniteCurveExceptions
import Mathlib.RingTheory.Nullstellensatz

/-! Coordinate equations for the fibers of a finite affine projection. -/

open MvPolynomial

namespace MOC

variable {K σ : Type*} [Field K]

/-- In a finite affine projection, each original coordinate satisfies a
monic univariate equation with coefficients polynomial in the parameter. -/
theorem exists_monic_coordinate_equations_of_finite_projection
    (Q : Ideal (MvPolynomial σ K)) (f : Polynomial K →ₐ[K] (MvPolynomial σ K ⧸ Q))
    (hf : f.Finite) (t : MvPolynomial σ K) (ht : Ideal.Quotient.mk Q t = f Polynomial.X) :
    ∃ P : σ → Polynomial (Polynomial K), (∀ i, (P i).Monic) ∧
      ∀ z ∈ zeroLocus Q, ∀ i, ((P i).map (Polynomial.evalRingHom (eval z t))).IsRoot (z i) := by
  let B := MvPolynomial σ K ⧸ Q
  letI : Algebra (Polynomial K) B := f.toRingHom.toAlgebra
  letI : Module.Finite (Polynomial K) B := hf
  let x (i : σ) : B := Ideal.Quotient.mk Q (X i)
  have hInt (i : σ) := Algebra.IsIntegral.isIntegral (R := Polynomial K) (x i)
  choose P hMonic hRoot using hInt
  refine ⟨P, hMonic, fun z hz i => ?_⟩
  let φ : B →ₐ[K] K := Ideal.Quotient.liftₐ Q (MvPolynomial.aeval z) fun r hr =>
    (mem_zeroLocus_iff.mp hz) r hr
  have hφ (r : MvPolynomial σ K) : φ (Ideal.Quotient.mk Q r) = eval z r := rfl
  have hφx : φ (x i) = z i := (hφ (X i)).trans (eval_X i)
  have he : φ.comp f = Polynomial.aeval (eval z t) := by
    apply Polynomial.algHom_ext
    change φ (f Polynomial.X) = Polynomial.aeval (eval z t) Polynomial.X
    rw [← ht, hφ, Polynomial.aeval_X]
  have he' : φ.toRingHom.comp (algebraMap (Polynomial K) B) = Polynomial.evalRingHom (eval z t) := by
    exact congrArg AlgHom.toRingHom he
  have h := (Polynomial.hom_eval₂ (p := P i) (f := algebraMap (Polynomial K) B)
    (g := φ.toRingHom) (x i)).symm.trans
    ((congrArg φ.toRingHom (hRoot i)).trans (map_zero _))
  rw [he', show φ.toRingHom (x i) = z i from hφx] at h
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using h

/-- An individual fiber of a finite affine projection has finitely many
points because each coordinate lies in a finite root set. -/
theorem finite_points_over_finite_projection [Fintype σ]
    (Q : Ideal (MvPolynomial σ K)) (f : Polynomial K →ₐ[K] (MvPolynomial σ K ⧸ Q))
    (hf : f.Finite) (t : MvPolynomial σ K) (ht : Ideal.Quotient.mk Q t = f Polynomial.X)
    (a : K) : Set.Finite {z : σ → K | z ∈ zeroLocus Q ∧ eval z t = a} := by
  obtain ⟨P, hPm, hP⟩ := exists_monic_coordinate_equations_of_finite_projection Q f hf t ht
  have hfin (i : σ) : Set.Finite {v : K | ((P i).map (Polynomial.evalRingHom a)).IsRoot v} :=
    Polynomial.finite_setOf_isRoot (((hPm i).map _).ne_zero)
  refine (Set.Finite.pi' hfin).subset fun z hz i => ?_
  exact hz.2 ▸ hP z hz.1 i

end MOC
