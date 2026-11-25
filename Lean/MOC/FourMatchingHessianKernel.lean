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

/-- The quadratic gradient of the matching cubic. -/
abbrev fourMatchingGradient {R : Type*} [CommRing R] (u : Fin 14 → R) : Fin 14 → R :=
  cubicGradient u

private theorem gradient_projection_re (y : Fin 14 → ℂ) (i : Fin 14) :
    (fourMatchingGradient y i).re =
      fourMatchingGradient (fun k => (y k).re) i -
        fourMatchingGradient (fun k => (y k).im) i := by
  fin_cases i <;>
    simp [fourMatchingGradient, cubicGradient, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- The singularity equation for a complex lift splits into the real
Hessian kernel equation and equality of the two real gradients. -/
theorem fourMatchingGradient_eq_zero_iff (y : Fin 14 → ℂ) :
    fourMatchingGradient y = 0 ↔
      fourMatchingHessianAction (fun k => (y k).re) (fun k => (y k).im) = 0 ∧
      fourMatchingGradient (fun k => (y k).im) =
        fourMatchingGradient (fun k => (y k).re) := by
  constructor
  · intro h
    have hy (i : Fin 14) : fourMatchingGradient y i = 0 := congrFun h i
    constructor
    · funext i
      change fourMatchingHessianAction (fun k => (y k).re) (fun k => (y k).im) i = 0
      rw [← gradient_projection_im y i]
      exact congrArg Complex.im (hy i)
    · funext i
      have he := gradient_projection_re y i
      rw [hy i, Complex.zero_re] at he
      exact (sub_eq_zero.mp he.symm).symm
  · rintro ⟨hessian, gradient⟩
    funext i
    apply Complex.ext
    · change (fourMatchingGradient y i).re = 0
      rw [gradient_projection_re, congrFun gradient i, sub_self]
    · change (fourMatchingGradient y i).im = 0
      simp only [gradient_projection_im, hessian, Pi.zero_apply]

/-- A scaled exact bracket profile satisfies both real lift equations. -/
theorem fourMatching_real_lift_equations (z : Fin 8 → ℂ) (η : ℂ) :
    let u := fun k => (η * fourBracketLift z k).re
    let v := fun k => (η * fourBracketLift z k).im
    fourMatchingHessianAction u v = 0 ∧ fourMatchingGradient v = fourMatchingGradient u := by
  apply (fourMatchingGradient_eq_zero_iff (fun k => η * fourBracketLift z k)).mp
  funext i
  exact scaled_gradient_zero z η i

/-- A real secant profile that fails the real lift equations. -/
noncomputable def fourRealSecantObstruction : Fin 14 → ℝ :=
  ![4, 0, 12, -18, 4, 0, 0, -12, -4, 9, 3, 3, -3, -11]

private noncomputable def realSecantKernelFirst : Fin 14 → ℝ :=
  ![-15, 0, -3, 33, -11, -21, 0, 24, 8, -18, 15, -6, 13, 0]

private noncomputable def realSecantKernelSecond : Fin 14 → ℝ :=
  ![-1, 0, -21, -3, 27, 9, 0, 12, 4, -9, -12, -3, 0, 13]

private theorem realSecantKernel_coordinates (v : Fin 14 → ℝ)
    (hv : fourMatchingHessianAction fourRealSecantObstruction v = 0) (i : Fin 14) :
    v i = (realSecantKernelFirst i * v 12 + realSecantKernelSecond i * v 13) / 13 := by
  have he (j : Fin 14) : fourMatchingHessianAction fourRealSecantObstruction v j = 0 :=
    congrFun hv j
  have r0 := he 0
  have r1 := he 1
  have r2 := he 2
  have r3 := he 3
  have r4 := he 4
  have r5 := he 5
  have r6 := he 6
  have r7 := he 7
  have r8 := he 8
  have r9 := he 9
  have r10 := he 10
  have r11 := he 11
  norm_num [fourMatchingHessianAction, fourRealSecantObstruction, cubicGradient,
    Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero'] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
  fin_cases i <;> norm_num [realSecantKernelFirst, realSecantKernelSecond,
    Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero'] <;>
    linarith only [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11]

/-- The cubic and Hessian kernel tests can hold although no real
imaginary part satisfies the gradient equation. -/
theorem fourRealSecantObstruction_checks :
    fourMatchingCubic fourRealSecantObstruction = 0 ∧
      (∃ v : Fin 14 → ℝ, v ≠ 0 ∧ fourMatchingHessianAction fourRealSecantObstruction v = 0) ∧
      ¬ ∃ v : Fin 14 → ℝ, fourMatchingHessianAction fourRealSecantObstruction v = 0 ∧
        fourMatchingGradient v = fourMatchingGradient fourRealSecantObstruction := by
  refine ⟨?_, ⟨realSecantKernelFirst, ?_, ?_⟩, ?_⟩
  · norm_num [fourMatchingCubic, fourRealSecantObstruction,
      Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero']
  · intro h
    have hz : realSecantKernelFirst 12 = 0 := congrFun h 12
    norm_num [realSecantKernelFirst, Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero'] at hz
  · funext i
    fin_cases i <;>
      norm_num [fourMatchingHessianAction, fourRealSecantObstruction, realSecantKernelFirst,
        cubicGradient, Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero']
  · rintro ⟨v, hv, hg⟩
    have h0 : fourMatchingGradient fourRealSecantObstruction 0 = 72 := by
      norm_num [fourMatchingGradient, fourRealSecantObstruction, cubicGradient,
        Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero']
    have hp : fourMatchingGradient v 0 =
        -(9 / 169 : ℝ) * (25 * v 12 ^ 2 - 14 * v 12 * v 13 + 29 * v 13 ^ 2) := by
      conv_lhs =>
        rw [show v = (fun i => (realSecantKernelFirst i * v 12 +
          realSecantKernelSecond i * v 13) / 13) from funext (realSecantKernel_coordinates v hv)]
      simp [fourMatchingGradient, cubicGradient, realSecantKernelFirst, realSecantKernelSecond,
        Matrix.cons_val, Matrix.cons_val_succ', Matrix.cons_val_zero']
      <;> ring
    have he : fourMatchingGradient v 0 = 72 := (congrFun hg 0).trans h0
    rw [he] at hp
    nlinarith only [hp, sq_nonneg (5 * v 12 - (7 / 5 : ℝ) * v 13), sq_nonneg (v 13)]

end MOC
