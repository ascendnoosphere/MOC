import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! A nonzero function on a finite affine curve vanishes over finitely many base values. -/

namespace MOC

variable {K B : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]

/-- For an algebraic projection, the zeros of a nonzero coordinate function
occur only at roots of one nonzero polynomial in the projected parameter. -/
theorem exists_elimination_polynomial_of_algebraic_projection
    (f : Polynomial K →ₐ[K] B)
    (hf : letI := f.toRingHom.toAlgebra; Algebra.IsAlgebraic (Polynomial K) B)
    (r : B) (hr : r ≠ 0) :
    ∃ p : Polynomial K, p ≠ 0 ∧
      ∀ φ : B →ₐ[K] K, φ r = 0 → p.IsRoot (φ (f Polynomial.X)) := by
  letI : Algebra (Polynomial K) B := f.toRingHom.toAlgebra
  letI : Algebra.IsAlgebraic (Polynomial K) B := hf
  let I : Ideal B := Ideal.span {r}
  have hrI : r ∈ I := Ideal.subset_span (Set.mem_singleton r)
  have hn := Ideal.comap_ne_bot_of_algebraic_mem hr hrI
    (Algebra.IsAlgebraic.isAlgebraic (R := Polynomial K) r)
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  refine ⟨p, hp0, fun φ hzero => ?_⟩
  have hp' : f p ∈ I := hp
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hp'
  have hφ : (φ.comp f) p = 0 := by
    change φ (f p) = 0
    rw [hb, map_mul, hzero, zero_mul]
  have heq : φ.comp f = Polynomial.aeval (φ (f Polynomial.X)) := by
    exact Polynomial.algHom_ext (Polynomial.aeval_X _).symm
  rw [heq] at hφ
  simpa only [Polynomial.coe_aeval_eq_eval, Polynomial.IsRoot] using hφ

/-- The exceptional parameter values of a nonzero function on an algebraic
projection form a finite set. -/
theorem finite_exceptional_values_of_algebraic_projection
    (f : Polynomial K →ₐ[K] B)
    (hf : letI := f.toRingHom.toAlgebra; Algebra.IsAlgebraic (Polynomial K) B)
    (r : B) (hr : r ≠ 0) :
    Set.Finite {t : K | ∃ φ : B →ₐ[K] K, φ (f Polynomial.X) = t ∧ φ r = 0} := by
  obtain ⟨p, hp, hroot⟩ := exists_elimination_polynomial_of_algebraic_projection f hf r hr
  refine (Polynomial.finite_setOf_isRoot hp).subset ?_
  rintro _ ⟨φ, rfl, hzero⟩
  exact hroot φ hzero

/-- The exceptional parameter values of a nonzero function on a finite
affine curve form a finite set. -/
theorem finite_exceptional_values_of_finite_projection
    (f : Polynomial K →ₐ[K] B) (hf : f.Finite) (r : B) (hr : r ≠ 0) :
    Set.Finite {t : K | ∃ φ : B →ₐ[K] K, φ (f Polynomial.X) = t ∧ φ r = 0} := by
  refine finite_exceptional_values_of_algebraic_projection f ?_ r hr
  letI : Algebra (Polynomial K) B := f.toRingHom.toAlgebra
  letI : Module.Finite (Polynomial K) B := hf
  exact (inferInstance : Algebra.IsAlgebraic (Polynomial K) B)

end MOC
