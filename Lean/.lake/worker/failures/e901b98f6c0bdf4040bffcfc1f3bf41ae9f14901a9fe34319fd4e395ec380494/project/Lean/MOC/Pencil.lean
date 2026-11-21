import MOC.Core
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Rank-one completion pencils. The determinant is affine in each of the
two independent completion amplitudes, even when the matrices are singular. -/

open Matrix

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem det_rankOne_affine (A : Matrix ι ι ℂ) (u : Matrix ι (Fin 1) ℂ)
    (v : Matrix (Fin 1) ι ℂ) (z : ℂ) :
    (A + z • (u * v)).det = (1 - z) * A.det + z * (A + u * v).det := by
  let G (w : ℂ) : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) ℂ := fromBlocks A u (-(w • v)) 1
  have hdet (w : ℂ) : (G w).det = (A + w • (u * v)).det := by
    simp only [G, det_fromBlocks_one₂₂, Matrix.mul_neg, sub_neg_eq_add, Matrix.mul_smul]
  have hrow (w : ℂ) :
      G w = (G 0).updateRow (.inr 0) ((1 - w) • G 0 (.inr 0) + w • G 1 (.inr 0)) := by
    ext i j
    cases i with
    | inl i => cases j <;> simp [G, Matrix.updateRow_apply]
    | inr i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        cases j with
        | inl j => simp [G, Matrix.updateRow_apply, Matrix.smul_apply, smul_eq_mul]
        | inr j =>
            have hj : j = 0 := Subsingleton.elim _ _
            subst j
            simp [G, Matrix.updateRow_apply, smul_eq_mul]
  rw [← hdet z, hrow z, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_smul]
  have hzero := hrow 0
  have hone := hrow 1
  simp only [sub_zero, one_smul, zero_smul, add_zero] at hzero
  simp only [sub_self, one_smul, zero_smul, zero_add] at hone
  rw [← hzero, ← hone, hdet 0, hdet 1, zero_smul, add_zero, one_smul]

/-- Amplitudes `s` and `t` can be varied independently. For a completion and its
adjoint they are complex conjugates. The four evaluations determine the pencil. -/
theorem det_completion_biaffine (A : Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (D : Matrix ι κ ℂ) (E : Matrix κ ι ℂ) (R : Matrix κ κ ℂ)
    (c : Matrix ι (Fin 1) ℂ) (r : Matrix (Fin 1) κ ℂ)
    (c' : Matrix κ (Fin 1) ℂ) (r' : Matrix (Fin 1) ι ℂ) (s t : ℂ) :
    let p (z w : ℂ) := (A + L * (D + z • (c * r)) * R * (E + w • (c' * r'))).det
    p s t = p 0 0 + s * (p 1 0 - p 0 0) + t * (p 0 1 - p 0 0) +
      s * t * (p 1 1 - p 1 0 - p 0 1 + p 0 0) := by
  intro p
  have hleft (z w : ℂ) : p z w = (1 - z) * p 0 w + z * p 1 w := by
    let V := E + w • (c' * r')
    have he (a : ℂ) : p a w =
        (A + L * D * R * V + a • ((L * c) * (r * R * V))).det := by
      change (A + L * (D + a • (c * r)) * R * V).det = _
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_assoc, add_assoc]
    rw [he z, he 0, he 1, det_rankOne_affine]
    simp
  have hright (a z : ℂ) : p a z = (1 - z) * p a 0 + z * p a 1 := by
    let W := L * (D + a • (c * r)) * R
    have he (w : ℂ) : p a w =
        (A + W * E + w • ((W * c') * r')).det := by
      change (A + W * (E + w • (c' * r'))).det = _
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, add_assoc]
    rw [he z, he 0, he 1, det_rankOne_affine]
    simp
  rw [hleft s t, hright 0 t, hright 1 t]
  ring

end

end MOC
