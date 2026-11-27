import MOC.SecularBoundaryResidueTransfer
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Polynomial evaluations at two equal secular nodes are affine in the
transfer of residue. The difference has a fixed row factor. -/

open BigOperators Finset Matrix Polynomial

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The column model is diagonally similar to the Hermitian update at positive residues. -/
def secularColumnModel (d r : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal d + Matrix.of fun _ j => r j

private def powerCorrection (A : Matrix ι ι ℝ) (u : Matrix ι (Fin 1) ℝ) (t : ℝ) :
    ℕ → Matrix ι (Fin 1) ℝ
  | 0 => 0
  | m + 1 => A ^ m * u + t • powerCorrection A u t m

private theorem pow_add_rankOne_eigenrow
    (A : Matrix ι ι ℝ) (u : Matrix ι (Fin 1) ℝ) (v : Matrix (Fin 1) ι ℝ)
    (t x : ℝ) (hvu : v * u = 0) (hvA : v * A = t • v) (m : ℕ) :
    (A + x • (u * v)) ^ m = A ^ m + x • (powerCorrection A u t m * v) := by
  induction m with
  | zero => simp only [pow_zero, powerCorrection, Matrix.zero_mul, smul_zero, add_zero]
  | succ m ih =>
      let C := powerCorrection A u t m
      have hCA : (C * v) * A = t • (C * v) := by
        rw [Matrix.mul_assoc, hvA, Matrix.mul_smul]
      have hCv : (C * v) * (u * v) = 0 := by
        rw [← Matrix.mul_assoc _ u v, Matrix.mul_assoc C v u, hvu,
          Matrix.mul_zero, Matrix.zero_mul]
      have hcontract : powerCorrection A u t (m + 1) * v =
          (A ^ m * (u * v)) + t • (C * v) := by
        rw [powerCorrection, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [pow_succ, ih, pow_succ, hcontract, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      change A ^ m * A + A ^ m * (x • (u * v)) +
        ((x • (C * v)) * A + (x • (C * v)) * (x • (u * v))) =
        A ^ m * A + x • (A ^ m * (u * v) + t • (C * v))
      simp only [Matrix.mul_smul, Matrix.smul_mul, hCA, hCv, smul_zero, add_zero, smul_add]
      abel

private theorem aeval_add_rankOne_eigenrow
    (A : Matrix ι ι ℝ) (u : Matrix ι (Fin 1) ℝ) (v : Matrix (Fin 1) ι ℝ)
    (t : ℝ) (hvu : v * u = 0) (hvA : v * A = t • v) (p : ℝ[X]) :
    ∃ z : Matrix ι (Fin 1) ℝ, ∀ x : ℝ,
      Polynomial.aeval (A + x • (u * v)) p = Polynomial.aeval A p + x • (z * v) := by
  let z := ∑ m ∈ Finset.range (p.natDegree + 1), p.coeff m • powerCorrection A u t m
  refine ⟨z, fun x => ?_⟩
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  simp_rw [pow_add_rankOne_eigenrow A u v t x hvu hvA, smul_add, sum_add_distrib]
  congr 1
  simp only [z, Matrix.sum_mul, Matrix.smul_mul, smul_sum]
  apply sum_congr rfl
  intro m _
  rw [smul_smul, smul_smul, mul_comm]

private theorem secularColumnModel_transfer
    (d r : ι → ℝ) {i j : ι} (hd : d i = d j) :
    ∃ (u : Matrix ι (Fin 1) ℝ) (v : Matrix (Fin 1) ι ℝ),
      v * u = 0 ∧ v * secularColumnModel d r = d i • v ∧
      ∀ x : ℝ, secularColumnModel d (secularTransfer r i j x) =
        secularColumnModel d r + x • (u * v) := by
  let u : Matrix ι (Fin 1) ℝ := Matrix.of fun _ _ => 1
  let f (k : ι) : ℝ := (if k = i then 1 else 0) - (if k = j then 1 else 0)
  let v : Matrix (Fin 1) ι ℝ := Matrix.of fun _ k => f k
  have hf : (∑ k, f k) = 0 := by simp [f, sum_sub_distrib]
  have hvu : v * u = 0 := by
    ext a b : 1
    simp only [Matrix.mul_apply, u, v, Matrix.of_apply, mul_one, Matrix.zero_apply, hf]
  refine ⟨u, v, hvu, ?_, ?_⟩
  · have hdiag : v * diagonal d = d i • v := by
      ext a k : 1
      simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, v, Matrix.of_apply, f]
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj, hd] <;> ring
    have hr : v * (Matrix.of fun (_ : ι) k => r k) = 0 := by
      ext a k : 1
      simp only [Matrix.mul_apply, v, Matrix.of_apply, ← Finset.sum_mul, hf, zero_mul,
        Matrix.zero_apply]
    rw [secularColumnModel, Matrix.mul_add, hdiag, hr, add_zero]
  · intro x
    ext a k : 1
    simp only [secularColumnModel, secularTransfer, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.mul_apply, Matrix.of_apply, u, v, f, Fin.sum_univ_one, one_mul]
    ring

private theorem det_rankOne_affine_real {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) (u : Matrix κ (Fin 1) ℝ) (v : Matrix (Fin 1) κ ℝ) (x : ℝ) :
    (A + x • (u * v)).det = (1 - x) * A.det + x * (A + u * v).det := by
  let G (w : ℝ) : Matrix (κ ⊕ Fin 1) (κ ⊕ Fin 1) ℝ := fromBlocks A u (-(w • v)) 1
  have hdet (w : ℝ) : (G w).det = (A + w • (u * v)).det := by
    simp only [G, det_fromBlocks_one₂₂, Matrix.mul_neg, sub_neg_eq_add, Matrix.mul_smul]
  have hrow (w : ℝ) :
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
  rw [← hdet x, hrow x, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.det_updateRow_smul]
  have hzero := hrow 0
  have hone := hrow 1
  simp only [sub_zero, one_smul, zero_smul, add_zero] at hzero
  simp only [sub_self, one_smul, zero_smul, zero_add] at hone
  rw [← hzero, ← hone, hdet 0, hdet 1, zero_smul, add_zero, one_smul]

/-- The determinant of any principal polynomial submatrix depends affinely on
residue transfer between two coincident diagonal nodes. -/
theorem det_secular_evaluation_transfer {κ : Type*} [Fintype κ] [DecidableEq κ]
    (d r : ι → ℝ) (p : ℝ[X]) (e : κ → ι) (B : Matrix κ κ ℝ)
    {i j : ι} (hd : d i = d j)
    (x : ℝ) :
    let F (y : ℝ) :=
      (B + (Polynomial.aeval (secularColumnModel d (secularTransfer r i j y)) p).submatrix e e).det
    F x = (1 - x) * F 0 + x * F 1 := by
  dsimp only
  obtain ⟨u, v, hvu, hvA, htransfer⟩ := secularColumnModel_transfer d r hd
  obtain ⟨z, hz⟩ := aeval_add_rankOne_eigenrow (secularColumnModel d r) u v (d i) hvu hvA p
  let A := Polynomial.aeval (secularColumnModel d r) p
  let U := z.submatrix e id
  let V := v.submatrix id e
  have hsub (y : ℝ) :
      B + (Polynomial.aeval (secularColumnModel d (secularTransfer r i j y)) p).submatrix e e =
        (B + A.submatrix e e) + y • (U * V) := by
    rw [htransfer, hz]
    ext a b : 1
    simp only [A, U, V, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.mul_apply, id_eq]
    abel
  rw [hsub x, hsub 0, hsub 1, zero_smul, add_zero, one_smul]
  exact det_rankOne_affine_real _ _ _ _


end

end MOC
