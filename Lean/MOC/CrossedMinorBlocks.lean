import MOC.Core
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! The determinant row/column identities for the crossed minor transport. -/

open BigOperators Finset Matrix

namespace MOC

noncomputable section

private theorem det_add_marked_row_multiples {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i : ι) (w : ι → ℂ) (hw : w i = 0) :
    (Matrix.of fun j k => M j k + w j * M i k).det = M.det := by
  classical
  let c := replicateCol Unit w
  let r := replicateRow Unit (Pi.single i (1 : ℂ))
  have ht : (1 + c * r).det = 1 := by
    change (1 + replicateCol Unit w * replicateRow Unit (Pi.single i (1 : ℂ))).det = _
    rw [det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct, Pi.single_apply, hw]
  have hm : (1 + c * r) * M = Matrix.of fun j k => M j k + w j * M i k := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    ext j k
    have hr : (r * M) () k = M i k := by simp [r, Matrix.mul_apply, Pi.single_apply]
    change M j k + (∑ t : Unit, c j t * (r * M) t k) = _
    simp [c, hr]
  rw [← hm, det_mul, ht, one_mul]

private theorem det_add_marked_column_multiples {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i : ι) (w : ι → ℂ) (hw : w i = 0) :
    (Matrix.of fun j k => M j k + M j i * w k).det = M.det := by
  rw [← Matrix.det_transpose (M := M)]
  convert det_add_marked_row_multiples Mᵀ i w hw using 1
  rw [← Matrix.det_transpose]
  congr 1
  ext j k
  simp [mul_comm]

/-- For a block unitary with normalized crossed row and column, one
rank-one change to the spectator block makes both marked directions
vacant. No coordinate change in the spectator labels is used. -/
theorem crossed_spectator_block_annihilates
    {n : ℕ} (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hU : IsUnitary U)
    (s : ℝ) (hs : s ≠ 0) (x y : Fin n → ℂ)
    (hx : ∀ j, U 0 j.succ = (s : ℂ) * star (x j))
    (hy : ∀ i, U i.succ 0 = (s : ℂ) * y i)
    (hx₁ : ∑ i, Complex.normSq (x i) = 1) (hy₁ : ∑ i, Complex.normSq (y i) = 1) :
    let W : Matrix (Fin n) (Fin n) ℂ := Matrix.of
      (fun i j => U i.succ j.succ + star (U 0 0) * y i * star (x j))
    (∀ i, ∑ j, W i j * x j = 0) ∧ (∀ j, ∑ i, star (y i) * W i j = 0) := by
  intro W
  have hsn : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hx' : (∑ j, star (x j) * x j) = (1 : ℂ) := by
    rw [← Complex.ofReal_one, ← hx₁, Complex.ofReal_sum]
    simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  have hy' : (∑ i, star (y i) * y i) = (1 : ℂ) := by
    rw [← Complex.ofReal_one, ← hy₁, Complex.ofReal_sum]
    simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  constructor
  · intro i
    have h := congrFun (congrFun hU.1 i.succ) 0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, hy, hx,
      Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_conj, Matrix.one_apply_ne i.succ_ne_zero] at h
    have he : (∑ j, U i.succ j.succ * x j) + star (U 0 0) * y i = 0 := by
      apply mul_left_cancel₀ hsn
      rw [mul_zero, mul_add, Finset.mul_sum]
      convert h using 1
      rw [add_comm]
      congr 1
      · simp only [Complex.star_def]
        ring
      · apply sum_congr rfl
        intro j _
        ring
    simp only [W, Matrix.of_apply, add_mul, sum_add_distrib, mul_assoc (star (U 0 0) * y i),
      ← Finset.mul_sum, hx', mul_one]
    exact he
  · intro j
    have h := congrFun (congrFun hU.2 0) j.succ
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, hy, hx,
      Complex.star_def, map_mul, Complex.conj_ofReal, Matrix.one_apply_ne j.succ_ne_zero.symm] at h
    have he : (∑ i, star (y i) * U i.succ j.succ) +
        star (U 0 0) * star (x j) = 0 := by
      apply mul_left_cancel₀ hsn
      rw [mul_zero, mul_add, Finset.mul_sum]
      convert h using 1
      rw [add_comm]
      congr 1
      · simp only [Complex.star_def]
        ring
      · apply sum_congr rfl
        intro i _
        simp only [Complex.star_def, mul_assoc]
    simp only [W, Matrix.of_apply, mul_add, sum_add_distrib]
    have hs : (∑ i, star (y i) * (star (U 0 0) * y i * star (x j))) =
        (star (U 0 0) * star (x j)) := by
      calc
        _ = (∑ i, star (y i) * y i) * (star (U 0 0) * star (x j)) := by
          rw [sum_mul]
          apply sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hy', one_mul]
    rwa [hs]

/-- Adding a multiple of the marked row to each spectator row replaces the
spectator block by its common deflation in every crossed row minor. -/
theorem det_crossed_row_of_deflation {n k : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (s : ℝ) (hs : s ≠ 0) (x y : Fin n → ℂ)
    (hx : ∀ j, U 0 j.succ = (s : ℂ) * star (x j))
    (i : Fin k → Fin n) (j : Fin (k+1) → Fin n) :
    let W : Matrix (Fin n) (Fin n) ℂ := Matrix.of
      (fun i j => U i.succ j.succ + star (U 0 0) * y i * star (x j))
    let M : Matrix (Fin (k+1)) (Fin (k+1)) ℂ := Matrix.of
      (fun a b => Fin.cases (U 0 (j b).succ) (fun r => U (i r).succ (j b).succ) a)
    let D : Matrix (Fin (k+1)) (Fin (k+1)) ℂ := Matrix.of
      (fun a b => Fin.cases (star (x (j b))) (fun r => W (i r) (j b)) a)
    M.det = (s : ℂ) * D.det := by
  intro W M D
  have hsn : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  let v : Fin (k+1) → ℂ := Fin.cases (s : ℂ) (fun _ => 1)
  let w : Fin (k+1) → ℂ := Fin.cases 0 (fun r => star (U 0 0) * y (i r) / (s : ℂ))
  have hm : (Matrix.of fun a b => M a b + w a * M 0 b) = Matrix.of (fun a b => v a * D a b) := by
    ext a b
    refine Fin.cases ?_ (fun r => ?_) a
    · simp [M, w, v, D, hx]
    · simp only [M, W, w, v, D, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, one_mul, hx]
      field_simp
      ring
  calc
    M.det = (Matrix.of fun a b => M a b + w a * M 0 b).det :=
      (det_add_marked_row_multiples M 0 w rfl).symm
    _ = (∏ a, v a) * D.det := by rw [hm, det_mul_column]
    _ = _ := by simp [v, Fin.prod_univ_succ]


/-- The same deflation replaces the spectator block in the crossed
column minor after adding multiples of its marked column. -/
theorem det_crossed_column_of_deflation {n k : ℕ}
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (s : ℝ) (hs : s ≠ 0) (x y : Fin n → ℂ)
    (hy : ∀ i, U i.succ 0 = (s : ℂ) * y i)
    (i : Fin (k+1) → Fin n) (j : Fin k → Fin n) :
    let W : Matrix (Fin n) (Fin n) ℂ := Matrix.of
      (fun i j => U i.succ j.succ + star (U 0 0) * y i * star (x j))
    let M : Matrix (Fin (k+1)) (Fin (k+1)) ℂ := Matrix.of
      (fun a b => Fin.cases (U (i a).succ 0) (fun t => U (i a).succ (j t).succ) b)
    let D : Matrix (Fin (k+1)) (Fin (k+1)) ℂ := Matrix.of
      (fun a b => Fin.cases (y (i a)) (fun t => W (i a) (j t)) b)
    M.det = (s : ℂ) * D.det := by
  intro W M D
  have hsn : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  let v : Fin (k+1) → ℂ := Fin.cases (s : ℂ) (fun _ => 1)
  let w : Fin (k+1) → ℂ := Fin.cases 0 (fun t => star (U 0 0) * star (x (j t)) / (s : ℂ))
  have hm : (Matrix.of fun a b => M a b + M a 0 * w b) = Matrix.of (fun a b => v b * D a b) := by
    ext a b
    refine Fin.cases ?_ (fun t => ?_) b
    · simp [M, w, v, D, hy]
    · simp only [M, W, w, v, D, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, one_mul, hy]
      field_simp
      ring
  calc
    M.det = (Matrix.of fun a b => M a b + M a 0 * w b).det :=
      (det_add_marked_column_multiples M 0 w rfl).symm
    _ = (∏ a, v a) * D.det := by rw [hm, det_mul_row]
    _ = _ := by simp [v, Fin.prod_univ_succ]


end

end MOC
