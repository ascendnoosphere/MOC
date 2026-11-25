import MOC.FourMatchingPolarization
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! The Hessian condition in Zheng's Group V follows directly by polarizing
the gradient identity on the bracket lift. See Zheng (preprint DOI:
10.13140/RG.2.2.36790.25923, Appendix A and §4), and Howard–Millson–
Snowden–Vakil (DOI: 10.1112/plms/pds016) for the stronger secant rank statement. -/

open BigOperators Matrix

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
open private cubicGradient bracket_gradient_zero from MOC.FourMatchingPolarization

namespace MOC

/-- Mixed polarization of the quadratic gradient, i.e. the Hessian action. -/
@[irreducible] def fourMatchingHessianAction {R : Type*} [CommRing R] (u v : Fin 14 → R) :
    Fin 14 → R :=
  fun i => cubicGradient (fun k => u k + v k) i - cubicGradient u i - cubicGradient v i

set_option maxHeartbeats 1500000 in
private theorem gradient_projection_im (y : Fin 14 → ℂ) (i : Fin 14) :
    (cubicGradient y i).im =
      fourMatchingHessianAction (fun k => (y k).re) (fun k => (y k).im) i := by
  fin_cases i <;>
    simp [cubicGradient, fourMatchingHessianAction, Complex.add_im, Complex.sub_im,
      Complex.mul_im, Complex.mul_re, pow_two] <;> ring

private theorem scaled_gradient_zero {R : Type*} [CommRing R] (z : Fin 8 → R) (η : R)
    (i : Fin 14) : cubicGradient (fun k => η * fourBracketLift z k) i = 0 := by
  have he : cubicGradient (fun k => η * fourBracketLift z k) i =
      η ^ 2 * cubicGradient (fourBracketLift z) i := by
    generalize (fourBracketLift z) = w
    fin_cases i <;> simp [cubicGradient] <;> ring
  rw [he, bracket_gradient_zero, mul_zero]

private theorem matching_hessian_self (u : Fin 14 → ℝ) :
    fourMatchingHessianAction u u = fun i => 2 * cubicGradient u i := by
  funext i
  fin_cases i <;> simp [cubicGradient, fourMatchingHessianAction] <;> ring

/-- A projected point of the bracket cone always gives a nonzero kernel vector
of the polarized cubic Hessian. -/
theorem fourMatchingHessian_has_kernel (z : Fin 8 → ℂ) (η : ℂ) :
    ∃ v : Fin 14 → ℝ, v ≠ 0 ∧
      fourMatchingHessianAction (fun k => (η * fourBracketLift z k).re) v = 0 := by
  let y : Fin 14 → ℂ := fun k => η * fourBracketLift z k
  let u : Fin 14 → ℝ := fun k => (y k).re
  let v : Fin 14 → ℝ := fun k => (y k).im
  have hy (i : Fin 14) : cubicGradient y i = 0 := scaled_gradient_zero z η i
  by_cases hv : v = 0
  · have hre (i : Fin 14) : (u i : ℂ) = y i := by
      apply Complex.ext
      · simp [u]
      · have hi : (y i).im = 0 := congrFun hv i
        simpa only [Complex.ofReal_im] using hi.symm
    have hgu (i : Fin 14) : cubicGradient u i = 0 := by
      apply Complex.ofReal_injective
      have he : ((cubicGradient u i : ℝ) : ℂ) = cubicGradient y i := by
        fin_cases i <;>
          simp [cubicGradient, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
            Complex.ofReal_neg, Complex.ofReal_pow, hre]
      exact he.trans ((hy i).trans Complex.ofReal_zero.symm)
    by_cases hu : u = 0
    · refine ⟨fun _ => 1, ?_, ?_⟩
      · intro h
        have hh := congrFun h 0
        exact one_ne_zero hh
      · change fourMatchingHessianAction u (fun _ => 1) = 0
        rw [hu]
        funext i
        fin_cases i <;> simp [fourMatchingHessianAction, cubicGradient]
    · refine ⟨u, hu, ?_⟩
      change fourMatchingHessianAction u u = 0
      rw [matching_hessian_self]
      funext i
      change 2 * cubicGradient u i = 0
      rw [hgu i, mul_zero]
  · refine ⟨v, hv, ?_⟩
    funext i
    change fourMatchingHessianAction u v i = 0
    rw [← gradient_projection_im y i, hy i, Complex.zero_im]

end MOC
