import MOC.FourMatchingRelations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The matching Hessian is singular on the real parts of spectral matching data. -/

namespace MOC

noncomputable section

open BigOperators

/-- The Hessian columns are the polarizations of the quadratic gradient
against the individual coordinate vectors. -/
def fourMatchingHessian {R : Type*} [CommRing R] (m : Fin 14 → R) :
    Matrix (Fin 14) (Fin 14) R :=
  fun i j =>
    fourMatchingGradient (fun k => m k + Pi.single j 1 k) i -
      fourMatchingGradient m i - fourMatchingGradient (Pi.single j 1) i

set_option maxHeartbeats 4000000 in
private theorem fourMatchingHessian_mulVec_apply {R : Type*} [CommRing R]
    (m n : Fin 14 → R) (i : Fin 14) :
    (fourMatchingHessian m).mulVec n i =
      fourMatchingGradient (fun j => m j + n j) i -
        fourMatchingGradient m i - fourMatchingGradient n i := by
  change (∑ j, fourMatchingHessian m i j * n j) = _
  fin_cases i <;>
    simp [Fin.sum_univ_succ, fourMatchingHessian, fourMatchingGradient, Pi.single_apply] <;> ring

private theorem fourMatchingHessian_mulVec_self (m : Fin 14 → ℝ) (i : Fin 14) :
    (fourMatchingHessian m).mulVec m i = 2 * fourMatchingGradient m i := by
  rw [fourMatchingHessian_mulVec_apply]
  fin_cases i <;> simp [fourMatchingGradient] <;> ring

private theorem fourMatchingHessian_mulVec_im (m : Fin 14 → ℂ) (i : Fin 14) :
    (fourMatchingHessian (fun j => (m j).re)).mulVec (fun j => (m j).im) i =
      (fourMatchingGradient m i).im := by
  rw [fourMatchingHessian_mulVec_apply]
  fin_cases i <;>
    simp [fourMatchingGradient, Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.neg_im] <;>
    ring

/-- Any complex vector with vanishing matching gradient has singular
matching Hessian at its real part. -/
theorem fourMatchingHessian_det_real_part_eq_zero (m : Fin 14 → ℂ)
    (hm : ∀ i, fourMatchingGradient m i = 0) :
    (fourMatchingHessian (fun j => (m j).re)).det = 0 := by
  let u (j : Fin 14) := (m j).re
  let v (j : Fin 14) := (m j).im
  let T := fourMatchingHessian u
  change T.det = 0
  have hker (x : Fin 14 → ℝ) (hx : x ≠ 0) (hTx : T.mulVec x = 0) : T.det = 0 := by
    by_contra hne
    have hunit : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hne)
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
    exact hx (hinj (hTx.trans (Matrix.mulVec_zero T).symm))
  by_cases hv : v = 0
  · by_cases hu : u = 0
    · have hT : T = 0 := by
        change fourMatchingHessian u = 0
        rw [hu]
        ext i j : 1
        fin_cases i <;> simp [fourMatchingHessian, fourMatchingGradient]
      rw [hT, Matrix.det_zero (inferInstance : Nonempty (Fin 14))]
    · apply hker u hu
      have hvi (j : Fin 14) : (m j).im = 0 := congrFun hv j
      funext i
      change (fourMatchingHessian u).mulVec u i = 0
      rw [fourMatchingHessian_mulVec_self]
      have hRe : fourMatchingGradient u i = 0 := by
        have he := congrArg Complex.re (hm i)
        fin_cases i <;>
          simpa [u, fourMatchingGradient, Complex.mul_re, Complex.sub_re, Complex.add_re,
            Complex.neg_re, hvi] using he
      rw [hRe, mul_zero]
  · apply hker v hv
    funext i
    change (fourMatchingHessian (fun j => (m j).re)).mulVec (fun j => (m j).im) i = 0
    rw [fourMatchingHessian_mulVec_im, hm, Complex.zero_im]

/-- The real spectral coordinates used in the contact reductions have a
singular matching Hessian. -/
theorem fourMatchingHessian_det_spectral_real_part_eq_zero (a b : Fin 4 → ℂ) (η : ℂ) :
    (fourMatchingHessian
      (fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re)).det = 0 := by
  apply fourMatchingHessian_det_real_part_eq_zero
  intro i
  rw [fourMatchingGradient_scale, fourMatchingGradient_noncrossing, mul_zero]

end

end MOC
