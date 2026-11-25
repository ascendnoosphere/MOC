import MOC.FourMatchingHessianMatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option Elab.async false

/-! The matching Hessian is singular on the real parts of spectral matching data. -/

namespace MOC

noncomputable section

open BigOperators

private theorem fourMatchingHessian_mulVec_self (m : Fin 14 → ℝ) (i : Fin 14) :
    (fourMatchingHessian m).mulVec m i = 2 * fourMatchingGradient m i := by
  rw [fourMatchingHessian_mulVec_apply]
  fin_cases i <;> simp [fourMatchingGradient] <;> ring

/-- The real Hessian applied to the imaginary coordinates recovers the
imaginary part of the matching gradient. -/
theorem fourMatchingHessian_mulVec_im (m : Fin 14 → ℂ) (i : Fin 14) :
    (fourMatchingHessian (fun j => (m j).re)).mulVec (fun j => (m j).im) i =
      (fourMatchingGradient m i).im := by
  rw [fourMatchingHessian_mulVec_apply]
  fin_cases i <;>
    simp [fourMatchingGradient, Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.neg_im] <;>
    ring

private theorem det_eq_zero_of_nonzero_mulVec_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (x : ι → ℝ) (hx : x ≠ 0) (hTx : T.mulVec x = 0) : T.det = 0 := by
  by_contra hne
  have hunit : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hne)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  exact hx (hinj (hTx.trans (Matrix.mulVec_zero T).symm))

set_option maxRecDepth 10000 in
private theorem fourMatchingHessian_nonzero_kernel_real_part (m : Fin 14 → ℂ)
    (hm : ∀ i, fourMatchingGradient m i = 0) :
    ∃ x : Fin 14 → ℝ, x ≠ 0 ∧ (fourMatchingHessian (fun j => (m j).re)).mulVec x = 0 := by
  let u (j : Fin 14) := (m j).re
  let v (j : Fin 14) := (m j).im
  change ∃ x : Fin 14 → ℝ, x ≠ 0 ∧ (fourMatchingHessian u).mulVec x = 0
  by_cases hv : v = 0
  · by_cases hu : u = 0
    · refine ⟨fun _ => 1, fun hz => one_ne_zero (congrFun hz 0), ?_⟩
      rw [hu]
      funext i
      change (fourMatchingHessian 0).mulVec (fun _ => 1) i = 0
      rw [fourMatchingHessian_mulVec_apply]
      have hz : fourMatchingGradient (0 : Fin 14 → ℝ) i = 0 := by
        fin_cases i <;> simp [fourMatchingGradient]
      simp [hz]
    · refine ⟨u, hu, ?_⟩
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
  · refine ⟨v, hv, ?_⟩
    funext i
    change (fourMatchingHessian (fun j => (m j).re)).mulVec (fun j => (m j).im) i = 0
    rw [fourMatchingHessian_mulVec_im, hm, Complex.zero_im]

/-- Any complex vector with vanishing matching gradient has singular
matching Hessian at its real part. -/
theorem fourMatchingHessian_det_real_part_eq_zero (m : Fin 14 → ℂ)
    (hm : ∀ i, fourMatchingGradient m i = 0) :
    (fourMatchingHessian (fun j => (m j).re)).det = 0 := by
  obtain ⟨x, hx, hTx⟩ := fourMatchingHessian_nonzero_kernel_real_part m hm
  exact det_eq_zero_of_nonzero_mulVec_kernel (fourMatchingHessian (fun j => (m j).re)) x hx hTx

private theorem fourMatchingGradient_spectral_eq_zero (a b : Fin 4 → ℂ) (η : ℂ)
    (i : Fin 14) :
    fourMatchingGradient (fun j => η * fourNoncrossingCoordinates (fourSpectralPoints a b) j) i = 0 := by
  rw [fourMatchingGradient_scale, fourMatchingGradient_noncrossing, mul_zero]

set_option maxRecDepth 10000 in
/-- The real spectral coordinates used in the contact reductions have a
singular matching Hessian. -/
theorem fourMatchingHessian_det_spectral_real_part_eq_zero (a b : Fin 4 → ℂ) (η : ℂ) :
    (fourMatchingHessian
      (fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re)).det = 0 := by
  obtain ⟨x, hx, hTx⟩ := fourMatchingHessian_nonzero_kernel_real_part
    (fun j => η * fourNoncrossingCoordinates (fourSpectralPoints a b) j)
    (fourMatchingGradient_spectral_eq_zero a b η)
  exact det_eq_zero_of_nonzero_mulVec_kernel
    (fourMatchingHessian (fun j => (η * fourNoncrossingCoordinates (fourSpectralPoints a b) j).re))
    x hx hTx

end

end MOC
