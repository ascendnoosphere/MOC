import MOC.Pencil
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Convex.Segment
import Mathlib.Algebra.BigOperators.Fin

/-! A collision of diagonal nodes permits a convex transfer between two
secular residue vectors, each with a vanishing residue. -/

open BigOperators Finset Matrix Polynomial

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Transfer a scalar amount from residue coordinate `j` to coordinate `i`. -/
def secularTransfer (r : ι → ℝ) (i j : ι) (x : ℝ) (k : ι) : ℝ :=
  r k + x * ((if k = i then 1 else 0) - (if k = j then 1 else 0))

/-- Transfer preserves total residue. -/
theorem sum_secularTransfer (r : ι → ℝ) (i j : ι) (x : ℝ) :
    ∑ k, secularTransfer r i j x k = ∑ k, r k := by
  simp only [secularTransfer, sum_add_distrib, mul_sub, sum_sub_distrib, ← mul_sum]
  simp

/-- A diagonal model for a quadratic spectral transform of a rank-one
secular matrix and its arbitrary complex diagonal partner. -/
def secularQuadraticColumnMatrix (d r : ι → ℝ) (c e : ℂ) (a : ι → ℂ) : Matrix ι ι ℂ :=
  diagonal (fun i => (d i : ℂ)^2 + c * d i + e + a i) +
    Matrix.of fun i j => ((d i : ℂ) + d j + c + ((∑ k, r k : ℝ) : ℂ)) * r j

/-- At equal diagonal values, redistribution of the two residues
perturbs the column matrix by rank one. Its determinant is affine. -/
theorem det_secularQuadraticColumnMatrix_transfer (d r : ι → ℝ)
    (c e : ℂ) (a : ι → ℂ) {i j : ι} (hd : d i = d j) (x : ℝ) :
    (secularQuadraticColumnMatrix d (secularTransfer r i j x) c e a).det =
      (1-(x : ℂ)) * (secularQuadraticColumnMatrix d r c e a).det +
        (x : ℂ) * (secularQuadraticColumnMatrix d (secularTransfer r i j 1) c e a).det := by
  let u : Matrix ι (Fin 1) ℂ := Matrix.of fun k _ =>
    (d k : ℂ) + d i + c + ((∑ e, r e : ℝ) : ℂ)
  let v : Matrix (Fin 1) ι ℂ := Matrix.of fun _ k =>
    (if k = i then 1 else 0) - (if k = j then 1 else 0)
  have hA (y : ℝ) : secularQuadraticColumnMatrix d (secularTransfer r i j y) c e a =
      secularQuadraticColumnMatrix d r c e a + (y : ℂ) • (u*v) := by
    ext k l : 1
    simp only [secularQuadraticColumnMatrix, sum_secularTransfer, Matrix.add_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_one, u, v]
    simp only [secularTransfer, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
    by_cases hi : l = i
    · subst l
      by_cases hj : i = j
      · simp [hj]
      · simp [hj]
        ring
    · by_cases hj : l = j
      · subst l
        simp [hi, hd]
        ring
      · simp [hi, hj]
  rw [hA x, det_rankOne_affine, hA 1, Complex.ofReal_one, one_smul]

/-- The secular characteristic polynomial, written without division
and therefore also defined at repeated diagonal values. -/
def secularCharacteristic (d r : ι → ℝ) : ℝ[X] :=
    (∏ k, (X - C (d k))) -
      ∑ j, C (r j) * ∏ k ∈ univ.erase j, (X - C (d k))

/-- At a collision the two pole-deleted nodal polynomials agree, so
transferring residue preserves the secular characteristic polynomial. -/
theorem secularCharacteristic_transfer (d r : ι → ℝ) {i j : ι} (hd : d i = d j) (x : ℝ) :
    secularCharacteristic d (secularTransfer r i j x) = secularCharacteristic d r := by
  let P (k : ι) : ℝ[X] := ∏ l ∈ univ.erase k, (X - C (d l))
  have hP : P i = P j := by
    have hi : P i * (X - C (d i)) = ∏ l, (X - C (d l)) := prod_erase_mul _ _ (mem_univ i)
    have hj : P j * (X - C (d j)) = ∏ l, (X - C (d l)) := prod_erase_mul _ _ (mem_univ j)
    rw [hd] at hi
    exact mul_right_cancel₀ (X_sub_C_ne_zero (d j)) (hi.trans hj.symm)
  have he :
      (∑ k, C (secularTransfer r i j x k) * P k) = ∑ k, C (r k) * P k := by
    simp only [secularTransfer, map_add, map_mul, map_sub, add_mul, sub_mul, mul_assoc,
      sum_add_distrib, sum_sub_distrib, ← mul_sum]
    have hsum (k : ι) : (∑ l, C (if l = k then (1 : ℝ) else 0) * P l) = P k := by
      simp_rw [apply_ite (C : ℝ →+* ℝ[X]), map_one, map_zero, ite_mul, one_mul, zero_mul]
      simpa only [mem_univ, if_true] using sum_ite_eq' univ k P
    simp only [hsum, hP, sub_self, mul_zero, add_zero]
  unfold secularCharacteristic
  congr 1

/-- The convex coefficients for a collision depend only on its two
residues, so the same interpolation applies to every spectral quadratic. -/
theorem det_secularQuadraticColumnMatrix_transfer_weights (d r : ι → ℝ)
    (c e : ℂ) (a : ι → ℂ) {i j : ι}
    (hd : d i = d j) (hi : 0 ≤ r i) (hj : 0 ≤ r j) :
    let x := r i / (r i + r j)
    (1-x) • (secularQuadraticColumnMatrix d (secularTransfer r i j (-r i)) c e a).det +
      x • (secularQuadraticColumnMatrix d (secularTransfer r i j (r j)) c e a).det =
    (secularQuadraticColumnMatrix d r c e a).det := by
  intro x
  let F (x : ℝ) := (secularQuadraticColumnMatrix d (secularTransfer r i j x) c e a).det
  let D := (secularQuadraticColumnMatrix d r c e a).det
  change (1-x) • F (-r i) + x • F (r j) = D
  by_cases hz : r i + r j = 0
  · have hi' : r i = 0 := by linarith
    have hR : secularTransfer r i j 0 = r := by
      funext k
      simp [secularTransfer]
    have hF : F (-r i) = D := by
      simp only [F, D, hi', neg_zero, hR]
    simp [x, hz, hF]
  · have hmul : (x : ℂ) * ((r i : ℂ) + r j) = (r i : ℂ) := by
      rw [← Complex.ofReal_add, ← Complex.ofReal_mul, div_mul_cancel₀ _ hz]
    have hF (z : ℝ) : F z = (1-(z : ℂ))*D + (z : ℂ) * F 1 :=
      det_secularQuadraticColumnMatrix_transfer d r c e a hd z
    rw [hF (-r i), hF (r j)]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg]
    linear_combination (F 1-D) * hmul

/-- At a collision, the determinant lies on the segment between the
two residue allocations that leave one colliding coordinate idle. -/
theorem det_secularQuadraticColumnMatrix_mem_transfer_segment (d r : ι → ℝ)
    (c e : ℂ) (a : ι → ℂ) {i j : ι}
    (hd : d i = d j) (hi : 0 ≤ r i) (hj : 0 ≤ r j) :
    (secularQuadraticColumnMatrix d r c e a).det ∈ segment ℝ
      (secularQuadraticColumnMatrix d (secularTransfer r i j (-r i)) c e a).det
      (secularQuadraticColumnMatrix d (secularTransfer r i j (r j)) c e a).det := by
  let x := r i / (r i + r j)
  have hle : x ≤ 1 := by
    by_cases hz : r i + r j = 0
    · simp [x, hz]
    · exact (div_le_one (lt_of_le_of_ne (add_nonneg hi hj) (Ne.symm hz))).mpr (by linarith)
  refine ⟨1-x, x, sub_nonneg.mpr hle, div_nonneg hi (add_nonneg hi hj), sub_add_cancel _ _, ?_⟩
  exact det_secularQuadraticColumnMatrix_transfer_weights d r c e a hd hi hj

/-- With a zero residue, the determinant factors out its diagonal
coordinate and leaves the same problem in the smaller order. -/
theorem det_secularQuadraticColumnMatrix_zero_residue {n : ℕ}
    (d r : Fin (n+1) → ℝ) (c e : ℂ) (a : Fin (n+1) → ℂ) (i : Fin (n+1))
    (hr : r i = 0) :
    (secularQuadraticColumnMatrix d r c e a).det =
      ((d i : ℂ)^2 + c * d i + e + a i) *
        (secularQuadraticColumnMatrix (d ∘ i.succAbove) (r ∘ i.succAbove)
          c e (a ∘ i.succAbove)).det := by
  let M := secularQuadraticColumnMatrix d r c e a
  have hcol (j : Fin (n+1)) :
      M j i = diagonal (fun k => (d k : ℂ)^2 + c*d k + e + a k) j i := by
    simp [M, secularQuadraticColumnMatrix, hr]
  have hsum : (∑ j : Fin (n+1), r j) = ∑ j : Fin n, r (i.succAbove j) := by
    rw [Fin.sum_univ_succAbove _ i, hr, zero_add]
  have hsub : M.submatrix i.succAbove i.succAbove =
      secularQuadraticColumnMatrix (d ∘ i.succAbove) (r ∘ i.succAbove) c e (a ∘ i.succAbove) := by
    ext j k : 1
    simp only [M, secularQuadraticColumnMatrix, Matrix.submatrix_apply, Matrix.add_apply,
      Matrix.diagonal_apply, Fin.succAbove_right_inj, Function.comp_apply, Matrix.of_apply, hsum]
  change M.det = _
  rw [Matrix.det_succ_column M i, sum_eq_single i]
  · have hs : (-1 : ℂ) ^ ((i : ℕ) + (i : ℕ)) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [hcol i, Matrix.diagonal_apply_eq, hsub, hs, one_mul]
  · intro j _ hji
    rw [hcol j, Matrix.diagonal_apply_ne _ hji, mul_zero, zero_mul]
  · exact fun h => (h (mem_univ i)).elim

end

end MOC
