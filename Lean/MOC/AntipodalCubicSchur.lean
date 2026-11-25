import MOC.AntipodalAffineVariation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Instances.Matrix

/-! The normalized Schur term at a crossed two-dimensional kernel has
a first derivative. This extracts the cubic determinant coefficient
without assuming the kernel velocity is invertible. For the Schur complement
formula, see Cottle (DOI: 10.1016/0024-3795(74)90066-4). -/

open BigOperators Matrix Filter
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact Schur factorization after extracting the two kernel row factors. -/
theorem det_antipodal_scaled_two_rows
    (E : Matrix (Fin 2) (Fin 2) ℂ) (L : Matrix (Fin 2) ι ℂ)
    (M : Matrix ι (Fin 2) ℂ) (S : Matrix ι ι ℂ) (t : ℝ) (hS : S.det ≠ 0) :
    (fromBlocks (t • E) (t • L) (t • M) S).det =
      (t : ℂ)^2 * (S.det * (E-t • (L*S⁻¹*M)).det) := by
  have h : IsUnit S := (isUnit_iff_isUnit_det S).mpr (isUnit_iff_ne_zero.mpr hS)
  letI := h.invertible
  rw [Matrix.det_fromBlocks₂₂, ← Matrix.invOf_eq_nonsing_inv,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]
  rw [← smul_sub, Matrix.det_smul_of_tower]
  simp only [Fintype.card_fin, Complex.real_smul, Complex.ofReal_pow]
  ring

private theorem hasDerivAt_sub_mul_continuousAt_zero (a : ℂ) (f : ℝ → ℂ)
    (hf : ContinuousAt f 0) :
    HasDerivAt (fun t : ℝ => a - (t : ℂ) * f t) (-f 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply (hf.tendsto.neg.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht₀ : t ≠ 0 := ht
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht₀
  simp only [zero_add, Complex.ofReal_zero, zero_mul, sub_zero, sub_sub_cancel_left,
    Complex.real_smul, Complex.ofReal_inv]
  field_simp
  ring

/-- Derivative of the normalized determinant factor at the center.
Multiplication by t squared recovers the determinant of the full block
pencil, so the displayed derivative is its cubic term. -/
theorem hasDerivAt_antipodal_normalized_schur
    (J K V W : Matrix ι ι ℂ) (L : Matrix (Fin 2) ι ℂ) (M : Matrix ι (Fin 2) ℂ)
    (a b : ℂ)
    (hJ : J*J = 1) (hK : K*K = 1) (hdet : (J+K).det ≠ 0)
    (hV : Commute J V) (hW : Commute K W) :
    let S := J+K
    let C (t : ℝ) := S + t • (V+W)
    let H (t : ℝ) := L*(C t)⁻¹*M
    HasDerivAt (fun t : ℝ => (C t).det * ((diagonal ![a,b] : Matrix (Fin 2) (Fin 2) ℂ) - t • H t).det)
      (S.det * (a*b*((J*V).trace+(K*W).trace)/2 - b*(H 0) 0 0 - a*(H 0) 1 1)) 0 := by
  intro S C H
  let E : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![a,b]
  let F (t : ℝ) := E - t • H t
  have hC : ContinuousAt C 0 := by unfold C; fun_prop
  have hC₀ : C 0 = S := by simp [C]
  have hI : ContinuousAt (fun t => (C t)⁻¹) 0 := by
    apply ContinuousAt.comp _ hC
    rw [hC₀]
    exact continuousAt_matrix_inv S (by simpa [Ring.inverse_eq_inv] using
      (continuousAt_inv₀ hdet))
  have hH : ContinuousAt H 0 := by
    have hf : Continuous (fun A : Matrix ι ι ℂ => L*A*M) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact hf.continuousAt.comp hI
  have hentry (i j : Fin 2) :
      HasDerivAt (fun t => F t i j) (-H 0 i j) 0 := by
    have h : ContinuousAt (fun t => H t i j) 0 :=
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hH))
    simpa only [F, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
      using hasDerivAt_sub_mul_continuousAt_zero (E i j) _ h
  have hF₀ : F 0 = E := by simp [F]
  have hF : HasDerivAt (fun t => (F t).det) (-(H 0 0 0)*b - a*(H 0 1 1)) 0 := by
    have h := ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
    simpa only [Matrix.det_fin_two, hF₀, E, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_ne _ (Fin.zero_ne_one : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (Ne.symm (Fin.zero_ne_one : (0 : Fin 2) ≠ 1)),
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero,
      zero_mul, zero_add, add_zero, sub_zero, mul_neg, neg_zero, sub_eq_add_neg] using h
  have hFdet₀ : (F 0).det = a*b := by
    rw [hF₀, Matrix.det_fin_two]
    simp [E]
  have hd := hasDerivAt_det_affine_antipodal J K V W hJ hK hdet hV hW
  change HasDerivAt (fun t => (C t).det) _ 0 at hd
  convert hd.mul hF using 1
  simp only [hC₀, hFdet₀]
  ring


end

end MOC
