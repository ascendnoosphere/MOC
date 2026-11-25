import MOC.FiniteCurveExceptions
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! Every nonconstant parameter on a finite affine curve is an algebraic projection. -/

namespace MOC

variable {K B : Type u} [Field K] [CommRing B] [IsDomain B] [Algebra K B]

/-- A nonscalar element over an algebraically closed field is transcendental. -/
theorem aeval_injective_of_not_scalar [IsAlgClosed K] (x : B)
    (hx : x ∉ Set.range (algebraMap K B)) :
    Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] B) := by
  apply transcendental_iff_injective.mp
  intro halg
  have hi : IsIntegral K x := halg.isIntegral
  have hm := minpoly.monic hi
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have heval := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hdeg, hm.leadingCoeff, Polynomial.C_1, one_mul,
    map_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at heval
  exact hx ⟨- (minpoly K x).coeff 0, (map_neg _ _).trans heval.symm⟩

/-- A finite affine curve has transcendence degree one. Every injective
polynomial projection induces an algebraic extension of its parameter ring. -/
theorem algebraic_of_reprojecting_finite_curve
    (f g : Polynomial K →ₐ[K] B) (hf : f.Finite) (hfi : Function.Injective f)
    (hgi : Function.Injective g) :
    letI := g.toRingHom.toAlgebra
    Algebra.IsAlgebraic (Polynomial K) B := by
  have hdim : Algebra.trdeg K B = 1 := by
    letI : Algebra (Polynomial K) B := f.toRingHom.toAlgebra
    letI : Module.Finite (Polynomial K) B := hf
    letI : FaithfulSMul (Polynomial K) B :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hfi
    letI : IsScalarTower K (Polynomial K) B :=
      IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
    rw [← trdeg_add_eq (A := B) K (Polynomial K), Polynomial.trdeg_of_isDomain,
      trdeg_eq_zero (R := Polynomial K), add_zero]
  letI : Algebra (Polynomial K) B := g.toRingHom.toAlgebra
  letI : FaithfulSMul (Polynomial K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hgi
  letI : IsScalarTower K (Polynomial K) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have hadd := trdeg_add_eq (A := B) K (Polynomial K)
  rw [Polynomial.trdeg_of_isDomain, hdim] at hadd
  apply trdeg_eq_zero_iff.mp
  by_contra h
  have hle : (1 : Cardinal) + 1 ≤ 1 + Algebra.trdeg (Polynomial K) B :=
    add_le_add_left (Cardinal.one_le_iff_ne_zero.mpr h) 1
  rw [hadd, one_add_one_eq_two] at hle
  exact (not_le_of_gt Cardinal.one_lt_two) hle

/-- A nonzero curve function vanishes at only finitely many values of any
nonconstant parameter, including one whose projection fails to be finite. -/
theorem finite_exceptional_values_of_nonconstant_parameter [IsAlgClosed K]
    (f : Polynomial K →ₐ[K] B) (hf : f.Finite) (hfi : Function.Injective f)
    (x : B) (hx : x ∉ Set.range (algebraMap K B)) (r : B) (hr : r ≠ 0) :
    Set.Finite {t : K | ∃ φ : B →ₐ[K] K, φ x = t ∧ φ r = 0} := by
  let g : Polynomial K →ₐ[K] B := Polynomial.aeval x
  have hgi : Function.Injective g := aeval_injective_of_not_scalar x hx
  simpa [g] using finite_exceptional_values_of_algebraic_projection g
    (algebraic_of_reprojecting_finite_curve f g hf hfi hgi) r hr

end MOC
