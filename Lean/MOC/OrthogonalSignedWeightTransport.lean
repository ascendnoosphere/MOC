import MOC.Realification
import MOC.Weights
import Mathlib.Tactic.Ring

open BigOperators Matrix

namespace MOC

theorem realSignedWeight_ofReal_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Matrix.orthogonalGroup ι ℝ) (π : Equiv.Perm ι) :
    realSignedWeight (Complex.ofRealHom.mapMatrix O.val) π.symm =
      O.val.det * ((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ i, O.val i (π i) := by
  have hO := (Matrix.mem_orthogonalGroup_iff ι ℝ).mp O.property
  have hd : O.val.det * O.val.det = 1 := by
    have hd' := congrArg Matrix.det hO
    simpa only [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_transpose, Matrix.det_one] using hd'
  have hdne : O.val.det ≠ 0 := by
    intro hz
    simp only [hz, zero_mul, zero_ne_one] at hd
  have hprod : (∏ j, O.val (π.symm j) j) = ∏ i, O.val i (π i) := by
    simpa only [π.symm_apply_apply] using
      (Equiv.prod_comp π (fun j => O.val (π.symm j) j)).symm
  have hterm (σ : Equiv.Perm ι) :
      leibnizTerm (Complex.ofRealHom.mapMatrix O.val) σ =
        Complex.ofReal (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, O.val (σ j) j) := by
    simp only [leibnizTerm, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_prod]
    rfl
  rw [realSignedWeight, signedWeight, hterm, ← Complex.ofRealHom.map_det, Equiv.Perm.sign_symm, hprod]
  change ((Complex.ofReal _ / Complex.ofReal O.val.det).re : ℝ) = _
  rw [← Complex.ofReal_div, Complex.ofReal_re]
  apply (div_eq_iff hdne).2
  calc
    _ = (O.val.det * O.val.det) *
        (((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ i, O.val i (π i)) := by rw [hd, one_mul]
    _ = _ := by ring

theorem correctedWeight_submatrix_cols {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Matrix ι ι ℝ) (σ τ : Equiv.Perm ι) (correction : ℝ) :
    let A := O.submatrix id σ
    O.det * ((Equiv.Perm.sign (σ * τ) : ℤ) : ℝ) * (∏ i, O i ((σ * τ) i)) +
        (O.det * correction) * ((Equiv.Perm.sign (σ * τ) : ℤ) : ℝ) =
      A.det * ((Equiv.Perm.sign τ : ℤ) : ℝ) * (∏ i, A i (τ i)) +
        (A.det * correction) * ((Equiv.Perm.sign τ : ℤ) : ℝ) := by
  change _ = (O.submatrix id σ).det * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
    (∏ i, O i (σ (τ i))) + ((O.submatrix id σ).det * correction) *
      ((Equiv.Perm.sign τ : ℤ) : ℝ)
  rw [Matrix.det_permute', Equiv.Perm.sign_mul]
  simp only [Units.val_mul, Int.cast_mul, Equiv.Perm.mul_apply]
  ring

end MOC
