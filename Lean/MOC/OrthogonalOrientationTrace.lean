import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The trace bound for orientation-reversing orthogonal matrices. -/

open BigOperators Matrix

namespace MOC

/-- A real orthogonal matrix with determinant minus one has trace at
most its order minus two. The proof uses a vector that it negates. -/
theorem orthogonal_trace_le_of_det_neg_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q * Qᵀ = 1) (hd : Q.det = -1) :
    Q.trace ≤ (Fintype.card ι : ℝ) - 2 := by
  have hprod : Q * (Qᵀ + 1) = Q + 1 := by
    rw [Matrix.mul_add, hQ, Matrix.mul_one, add_comm]
  have ht : Qᵀ + 1 = (Q + 1)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hd, ht, Matrix.det_transpose] at hdet
  have hs : (Q + 1).det = 0 := by linarith only [hdet]
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hs
  rw [Matrix.add_mulVec, Matrix.one_mulVec] at hz
  let B := Q - 1
  let N := ∑ j, v j ^ 2
  have hN : 0 < N := by
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    exact Finset.sum_pos' (fun i _ => sq_nonneg (v i)) ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩
  have hcomponent (i : ι) : (∑ j, B i j * v j) = -2 * v i := by
    have h := congrFun hz i
    change (Q *ᵥ v) i + v i = 0 at h
    change (B *ᵥ v) i = _
    simp only [B, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    linarith only [h]
  have hrow (i : ι) : 4 * v i ^ 2 ≤ (∑ j, B i j ^ 2) * N := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) v
    rw [hcomponent] at h
    nlinarith only [h]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hrow i)
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  have hF : (4 : ℝ) ≤ ∑ i, ∑ j, B i j ^ 2 := (mul_le_mul_right hN).mp hsum
  have hF_eq : (∑ i, ∑ j, B i j ^ 2) = (B * Bᵀ).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have htrace : (B * Bᵀ).trace = 2 * (Fintype.card ι : ℝ) - 2 * Q.trace := by
    simp only [B, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul,
      hQ, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_transpose]
    ring
  rw [hF_eq, htrace] at hF
  linarith only [hF]

noncomputable section

/-- The modulus of the linear coordinate of a real two-plane map when
`positive` is true, and of the conjugate-linear coordinate otherwise. -/
def orientedPlaneAmplitude (positive : Bool) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  let x := A 0 0 + if positive then A 1 1 else -A 1 1
  let y := A 1 0 + if positive then -A 0 1 else A 0 1
  Real.sqrt (x ^ 2 + y ^ 2) / 2

/-- The squared amplitude is half the sum of the normalized square norm
and the signed determinant of the two-plane block. -/
theorem orientedPlaneAmplitude_sq (positive : Bool) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    orientedPlaneAmplitude positive A ^ 2 =
      ((∑ i, ∑ j, A i j ^ 2) / 2 + (if positive then A.det else -A.det)) / 2 := by
  unfold orientedPlaneAmplitude
  dsimp only
  rw [div_pow, Real.sq_sqrt (by positivity), Matrix.det_fin_two]
  cases positive <;> simp only [Fin.sum_univ_two, Bool.false_eq_true, if_false, if_true] <;> ring

private theorem exists_plane_unit_pair (x y : ℝ) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ x * c + y * s = Real.sqrt (x ^ 2 + y ^ 2) := by
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := hxy
    exact ⟨1, 0, by norm_num, by simp⟩
  · have hn : 0 < x ^ 2 + y ^ 2 := by
      by_cases hx : x = 0
      · have hy : y ≠ 0 := fun h => hxy ⟨hx, h⟩
        simpa [hx] using sq_pos_of_ne_zero hy
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y)
    let r := Real.sqrt (x ^ 2 + y ^ 2)
    have hr : r ≠ 0 := (Real.sqrt_pos.2 hn).ne'
    have hs : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hn.le
    refine ⟨x / r, y / r, ?_, ?_⟩
    · rw [div_pow, div_pow, ← add_div, ← hs, div_self (pow_ne_zero 2 hr)]
    · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
      have he : x * x + y * y = r * r := by nlinarith only [hs]
      rw [he, mul_div_cancel_right₀ _ hr]

private theorem exists_aligned_plane (positive : Bool) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℝ,
      B * Bᵀ = 1 ∧ B.det = (if positive then 1 else -1) ∧
        (Bᵀ * A).trace = 2 * orientedPlaneAmplitude positive A := by
  let x := A 0 0 + if positive then A 1 1 else -A 1 1
  let y := A 1 0 + if positive then -A 0 1 else A 0 1
  obtain ⟨c, s, hs, hp⟩ := exists_plane_unit_pair x y
  let B : Matrix (Fin 2) (Fin 2) ℝ := if positive then !![c, -s; s, c] else !![c, s; s, -c]
  refine ⟨B, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> cases positive <;>
      norm_num [B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
      nlinarith only [hs]
  · rw [Matrix.det_fin_two]
    cases positive <;> norm_num [B] <;> nlinarith only [hs]
  · rw [Matrix.trace_fin_two]
    have he : 2 * orientedPlaneAmplitude positive A = Real.sqrt (x ^ 2 + y ^ 2) := by
      change 2 * (Real.sqrt (x ^ 2 + y ^ 2) / 2) = _
      ring
    rw [he, ← hp]
    cases positive <;> norm_num [B, x, y, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;> ring

/-- The selected two-plane block of a matrix indexed by plane coordinates
and plane labels. -/
def orthogonalPlaneBlock {ι : Type*} (Q : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) (i j : ι) :
    Matrix (Fin 2) (Fin 2) ℝ := Q.submatrix (fun a => (a, i)) (fun b => (b, j))

/-- An orientation-reversing signed plane assignment cannot have total
selected amplitude above the number of planes minus one. -/
theorem forbidden_plane_assignment_amplitude_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) (hQ : Q * Qᵀ = 1) (hd : Q.det = 1)
    (π : Equiv.Perm ι) (positive : ι → Bool)
    (hneg : (∏ i, if positive i then (1 : ℝ) else -1) = -1) :
    (∑ i, orientedPlaneAmplitude (positive i) (orthogonalPlaneBlock Q i (π i))) ≤
      (Fintype.card ι : ℝ) - 1 := by
  classical
  let τ : Equiv.Perm (Fin 2 × ι) := Equiv.prodCongrRight (fun _ : Fin 2 => π)
  let T : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ := Q.submatrix id τ
  have hτ : Equiv.Perm.sign τ = 1 := by
    change Equiv.Perm.sign (Equiv.prodCongrRight (fun _ : Fin 2 => π)) = _
    rw [Equiv.Perm.sign_prodCongrRight, Fin.prod_univ_two, Int.units_mul_self]
  have hTd : T.det = 1 := by
    rw [T, Matrix.det_permute', hτ, hd] <;> norm_num
  have hTo : T * Tᵀ = 1 := by
    ext i j
    have he := congrArg (fun M : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ => M i j) hQ
    change (∑ k, Q i (τ k) * Q j (τ k)) = (1 : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ) i j
    rw [Equiv.sum_comp τ (fun k => Q i k * Q j k)]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using he
  choose W hWo hWd hWtrace using fun i =>
    exists_aligned_plane (positive i) (orthogonalPlaneBlock Q i (π i))
  let B := Matrix.blockDiagonal W
  have hBo : B * Bᵀ = 1 := by
    rw [B, Matrix.blockDiagonal_transpose, ← Matrix.blockDiagonal_mul]
    rw [show (fun i => W i * (W i)ᵀ) = 1 from funext hWo, Matrix.blockDiagonal_one]
  have hBd : B.det = -1 := by
    rw [B, Matrix.det_blockDiagonal]
    simpa only [hWd] using hneg
  have hV : (Bᵀ * T) * (Bᵀ * T)ᵀ = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc T, hTo, Matrix.one_mul, Matrix.mul_eq_one_comm.mp hBo]
  have hVd : (Bᵀ * T).det = -1 := by
    rw [Matrix.det_mul, Matrix.det_transpose, hBd, hTd, mul_one]
  have ht := orthogonal_trace_le_of_det_neg_one (Bᵀ * T) hV hVd
  have htr : (Bᵀ * T).trace =
      ∑ i, ((W i)ᵀ * orthogonalPlaneBlock Q i (π i)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_prod_type, B, Matrix.blockDiagonal_apply]
    simp_rw [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm] <;> rfl
  rw [htr] at ht
  simp only [hWtrace, ← Finset.mul_sum, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_ofNat] at ht
  linarith only [ht]

end

end MOC
