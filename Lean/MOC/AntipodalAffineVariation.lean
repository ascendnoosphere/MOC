import MOC.AntipodalDeterminantJet
import Mathlib.Analysis.Complex.RealDeriv

/-! Jacobi's first variation at an invertible antipodal center. -/

open BigOperators Matrix

namespace MOC

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At an invertible antipodal center, an arbitrary affine variation of each
spectral diagonal has logarithmic derivative given by half its signed trace.
The commuting hypotheses express that the velocities keep their own eigenbases. -/
theorem hasDerivAt_det_affine_antipodal (J K V W : Matrix ι ι ℂ)
    (hJ : J * J = 1) (hK : K * K = 1) (hdet : (J + K).det ≠ 0)
    (hV : Commute J V) (hW : Commute K W) :
    HasDerivAt (fun t : ℝ => (J + K + t • (V + W)).det)
      ((J + K).det * (((J * V).trace + (K * W).trace) / 2)) 0 := by
  let S := J + K
  let D := V + W
  let T := S⁻¹ * D
  let M (t : ℝ) := (1 : Matrix ι ι ℂ) + t • T
  have hu : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
  have h₀ : M 0 = diagonal (fun _ => (1 : ℂ)) := by simp [M, Matrix.diagonal_one]
  have hcoe (t : ℝ) : Complex.ofRealCLM t = (t : ℂ) := rfl
  have hderiv (i j : ι) : HasDerivAt (fun t => M t i j) (T i j) 0 := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (T i j)
    simpa only [hcoe, Complex.ofReal_one, one_mul, M, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul] using h.const_add ((1 : Matrix ι ι ℂ) i j)
  have hm : HasDerivAt (fun t => (M t).det) T.trace 0 := by
    simpa [Matrix.trace] using hasDerivAt_det_diagonal M T 0 (fun _ => 1) h₀ hderiv
  have hfactor (t : ℝ) : S.det * (M t).det = (S + t • D).det := by
    rw [← Matrix.det_mul]
    change (S * (1 + t • T)).det = _
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, show S * T = D by
      rw [show T = S⁻¹ * D from rfl, ← Matrix.mul_assoc, S.mul_nonsing_inv hu, Matrix.one_mul]]
  have htrace : T.trace = ((J * V).trace + (K * W).trace) / 2 :=
    trace_inv_add_involutions_mul_split J K V W hJ hK hdet hV hW
  simpa only [S, D, htrace, hfactor] using hm.const_mul S.det

end

end MOC
