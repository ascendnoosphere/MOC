import MOC.Pencil
import MOC.ProjectionConditioning

/-! A determinant identity for deleting one coordinate of a projection. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_scalar_border (a : ℂ) (v : Matrix (Fin 1) ι ℂ)
    (u : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) :
    (fromBlocks (scalar (Fin 1) a) v u D).det =
      (D - u * v).det + (a - 1) * D.det := by
  let N := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) v u D
  let T := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) (0 : Matrix (Fin 1) ι ℂ) u D
  let e : Fin 1 ⊕ ι := Sum.inl 0
  have hT : N.updateRow e (T e) = T := by
    ext (i | i) j
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact congrFun Matrix.updateRow_self j
    · rcases j with j | j <;> simp [N, T, e]
  have hN : N.updateRow e (N e + (a - 1) • T e) =
      fromBlocks (scalar (Fin 1) a) v u D := by
    ext (i | i) (j | j)
    · have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i
      subst j
      simp [N, T, e, scalar_apply, smul_eq_mul]
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [N, T, e, smul_eq_mul]
    · simp [N, e]
    · simp [N, e]
  rw [← hN, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, hT]
  simp [N, T, det_fromBlocks_one₁₁, det_fromBlocks_zero₁₂]

/-- The determinant identity holds for any block `D`, even when the border
or the lower-right block is singular. -/
theorem det_projection_border_mixture (a k p : ℂ) (hp : p ≠ 0) (hp' : 1 - p ≠ 0)
    (q : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ) :
    (fromBlocks (scalar (Fin 1) (a + k * p)) (k • qᴴ) (k • q) D).det =
      p * (a + k) * (D + (-(k / p)) • (q * qᴴ)).det +
      (1 - p) * a * (D + (k / (1 - p)) • (q * qᴴ)).det := by
  have hmat : D - (k • q) * (k • qᴴ) = D + (-(k * k)) • (q * qᴴ) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_smul, sub_eq_add_neg]
  rw [det_scalar_border, hmat, det_rankOne_affine, det_rankOne_affine D q qᴴ,
    det_rankOne_affine D q qᴴ]
  field_simp
  ring

private theorem det_projection_border_mixture_of_endpoint (a k p : ℂ)
    (q : Matrix ι (Fin 1) ℂ) (D : Matrix ι ι ℂ)
    (hq : p = 0 ∨ p = 1 → q = 0) :
    (fromBlocks (scalar (Fin 1) (a + k * p)) (k • qᴴ) (k • q) D).det =
      p * (a + k) * (D + (-(k / p)) • (q * qᴴ)).det +
      (1 - p) * a * (D + (k / (1 - p)) • (q * qᴴ)).det := by
  by_cases hp : p = 0
  · simp [hp, hq (Or.inl hp), det_fromBlocks_zero₁₂, det_fin_one, scalar_apply]
  by_cases hp' : p = 1
  · simp [hp', hq (Or.inr hp'), det_fromBlocks_zero₁₂, det_fin_one, scalar_apply]
  exact det_projection_border_mixture a k p hp (sub_ne_zero.mpr (Ne.symm hp')) q D

private theorem det_sum_projection_leaf_of_endpoint (s k r : ℂ) (p : ℝ)
    (q : Matrix ι (Fin 1) ℂ) (J B : Matrix ι ι ℂ)
    (hq : p = 0 ∨ p = 1 → q = 0) :
    (s • (1 : Matrix (Fin 1 ⊕ ι) (Fin 1 ⊕ ι) ℂ) +
      k • fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J +
      fromBlocks (scalar (Fin 1) r) 0 0 B).det =
      (p : ℂ) * (s + k + r) * (s • (1 : Matrix ι ι ℂ) +
        k • (J + (-(p : ℂ)⁻¹) • (q * qᴴ)) + B).det +
      (1 - (p : ℂ)) * (s + r) * (s • (1 : Matrix ι ι ℂ) +
        k • (J + (1 - (p : ℂ))⁻¹ • (q * qᴴ)) + B).det := by
  let D := s • (1 : Matrix ι ι ℂ) + k • J + B
  have hmatrix :
      s • (1 : Matrix (Fin 1 ⊕ ι) (Fin 1 ⊕ ι) ℂ) +
        k • fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J +
        fromBlocks (scalar (Fin 1) r) 0 0 B =
      fromBlocks (scalar (Fin 1) (s + r + k * (p : ℂ))) (k • qᴴ) (k • q) D := by
    rw [← fromBlocks_one (l := Fin 1) (m := ι)]
    simp only [fromBlocks_smul, fromBlocks_add, smul_zero, add_zero, zero_add,
      fromBlocks_inj, D, and_self, and_true]
    ext i j : 1
    have h : i = j := Subsingleton.elim _ _
    subst j
    simp [scalar_apply, smul_eq_mul, add_right_comm]
  have hchild (t : ℂ) :
      s • (1 : Matrix ι ι ℂ) + k • (J + t • (q * qᴴ)) + B = D + (k * t) • (q * qᴴ) := by
    rw [smul_add, smul_smul]
    dsimp [D]
    abel
  have hscalar : s + k + r = s + r + k := by ring
  have hq' : (p : ℂ) = 0 ∨ (p : ℂ) = 1 → q = 0 := by
    intro hp
    rcases hp with hp | hp
    · exact hq (Or.inl (by exact_mod_cast hp))
    · exact hq (Or.inr (by exact_mod_cast hp))
  rw [hmatrix, hchild, hchild, hscalar,
    det_projection_border_mixture_of_endpoint (s + r) k (p : ℂ) q D hq']
  simp only [mul_neg, div_eq_mul_inv]

/-- Delete one coordinate where the other summand has a scalar block.
The two terms assign the projection eigenvalues one and zero to that coordinate.
The determinant identity includes the endpoints where one weight vanishes. -/
theorem det_sum_projection_leaf (s k r : ℂ) (p : ℝ)
    (q : Matrix ι (Fin 1) ℂ) (J B : Matrix ι ι ℂ)
    (hP : fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J *
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J =
      fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J) :
    (s • (1 : Matrix (Fin 1 ⊕ ι) (Fin 1 ⊕ ι) ℂ) +
      k • fromBlocks (scalar (Fin 1) (p : ℂ)) qᴴ q J +
      fromBlocks (scalar (Fin 1) r) 0 0 B).det =
      (p : ℂ) * (s + k + r) * (s • (1 : Matrix ι ι ℂ) +
        k • projectionConditionOne p q J + B).det +
      (1 - (p : ℂ)) * (s + r) * (s • (1 : Matrix ι ι ℂ) +
        k • projectionConditionZero p q J + B).det :=
  det_sum_projection_leaf_of_endpoint s k r p q J B
    (fun hp => (projection_border_endpoint p q J hP hp).1)

end

end MOC
