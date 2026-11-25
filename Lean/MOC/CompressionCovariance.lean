import MOC.NormalCompressionLine
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The compression self-commutator measures the determinant of the
two-dimensional covariance of the deleted row's weighted spectrum. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

private theorem sum_normSq_entries_eq_trace {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    (∑ i, ∑ j, Complex.normSq (A i j)) = (A * Aᴴ).trace.re := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

private theorem sum_normSq_entries_unitaryConj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U E : Matrix ι ι ℂ) (hU : IsUnitary U) :
    (∑ i, ∑ j, Complex.normSq ((U * E * Uᴴ) i j)) = ∑ i, ∑ j, Complex.normSq (E i j) := by
  rw [sum_normSq_entries_eq_trace, sum_normSq_entries_eq_trace]
  have hprod : (U * E * Uᴴ) * (U * E * Uᴴ)ᴴ = U * (E * Eᴴ) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]
  rw [hprod, Matrix.trace_mul_cycle, hU.2, Matrix.one_mul]

/-- The diagonal entry at the deleted row is the spectral mean with
squared-unitary row weights. -/
theorem deleted_row_spectral_mean {n : ℕ} (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1)) :
    (∑ i, Complex.normSq (U p i)) = 1 ∧
      (U * diagonal β * Uᴴ) p p = ∑ i, (Complex.normSq (U p i) : ℂ) * β i := by
  constructor
  · have h := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => (A p p).re) hU.1
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re] using h
  · rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self,
      Complex.star_def]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Eight times the covariance determinant is the squared Frobenius norm
of the principal compression's self-commutator. The covariance uses the
squared moduli in the deleted unitary row as weights. -/
theorem principalCompression_selfCommutator_covariance {n : ℕ} (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1)) :
    let M := U * diagonal β * Uᴴ
    let C := M.submatrix p.succAbove p.succAbove
    let δ (i : Fin (n + 1)) := β i - M p p
    let w (i : Fin (n + 1)) := Complex.normSq (U p i)
    (∑ i, ∑ j, Complex.normSq ((C * Cᴴ - Cᴴ * C) i j)) =
      8 * ((∑ i, w i * (δ i).re ^ 2) * (∑ i, w i * (δ i).im ^ 2) -
        (∑ i, w i * (δ i).re * (δ i).im) ^ 2) := by
  intro M C δ w
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i j =>
    star (U p i) * U p j * (star (δ i) * δ j - δ i * star (δ j))
  let T := U * E * Uᴴ
  have hLift : T.submatrix p.succAbove p.succAbove = C * Cᴴ - Cᴴ * C ∧
      (∀ i, T p i = 0) ∧ (∀ i, T i p = 0) :=
    principalCompression_selfCommutator_spectral_lift β U hU p
  obtain ⟨hsub, hrow, hcol⟩ := hLift
  have hpad : (∑ i, ∑ j, Complex.normSq (T i j)) =
      ∑ i : Fin n, ∑ j : Fin n, Complex.normSq ((T.submatrix p.succAbove p.succAbove) i j) := by
    rw [Fin.sum_univ_succAbove _ p]
    simp only [hrow, Complex.normSq_zero, Finset.sum_const_zero, zero_add, Matrix.submatrix_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succAbove _ p, hcol, Complex.normSq_zero, zero_add]
  rw [← hsub, ← hpad, show T = U * E * Uᴴ from rfl, sum_normSq_entries_unitaryConj U E hU]
  let a (i : Fin (n + 1)) := w i * (δ i).re ^ 2
  let b (i : Fin (n + 1)) := w i * (δ i).im ^ 2
  let c (i : Fin (n + 1)) := w i * (δ i).re * (δ i).im
  change (∑ i, ∑ j, Complex.normSq (E i j)) = 8 * ((∑ i, a i) * (∑ i, b i) - (∑ i, c i) ^ 2)
  have hentry (i j : Fin (n + 1)) : Complex.normSq (E i j) =
      4 * (a i * b j + b i * a j - 2 * (c i * c j)) := by
    have hcross (z t : ℂ) : Complex.normSq (conj z * t - z * conj t) =
        4 * (z.re * t.im - z.im * t.re) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    simp only [E, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, hcross, a, b, c, w]
    ring
  calc
    (∑ i, ∑ j, Complex.normSq (E i j)) =
        4 * ((∑ i, ∑ j, a i * b j) + (∑ i, ∑ j, b i * a j) - 2 * (∑ i, ∑ j, c i * c j)) := by
      simp only [hentry, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, ← Finset.sum_mul_sum]
      ring

/-- A nonnormal pole must have positive spectral covariance determinant. -/
theorem principalCompression_covariance_pos {n : ℕ} (β : Fin (n + 1) → ℂ)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U) (p : Fin (n + 1))
    (hn : ¬ IsStarNormal ((U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove)) :
    let μ := (U * diagonal β * Uᴴ) p p
    let δ (i : Fin (n + 1)) := β i - μ
    let w (i : Fin (n + 1)) := Complex.normSq (U p i)
    0 < (∑ i, w i * (δ i).re ^ 2) * (∑ i, w i * (δ i).im ^ 2) -
      (∑ i, w i * (δ i).re * (δ i).im) ^ 2 := by
  intro μ δ w
  let C := (U * diagonal β * Uᴴ).submatrix p.succAbove p.succAbove
  let K := C * Cᴴ - Cᴴ * C
  have hne : K ≠ 0 := by
    intro hz
    apply hn
    exact ⟨(sub_eq_zero.mp hz).symm⟩
  have hentry : ∃ i j, K i j ≠ 0 := by
    by_contra! hz
    apply hne
    ext i j : 1
    exact hz i j
  obtain ⟨i, j, hij⟩ := hentry
  have hnorm : 0 < ∑ i, ∑ j, Complex.normSq (K i j) := by
    refine Finset.sum_pos' (fun a _ => Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _))
      ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun b _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hij⟩
  have he : (∑ i, ∑ j, Complex.normSq (K i j)) =
      8 * ((∑ i, w i * (δ i).re ^ 2) * (∑ i, w i * (δ i).im ^ 2) -
        (∑ i, w i * (δ i).re * (δ i).im) ^ 2) :=
    principalCompression_selfCommutator_covariance β U hU p
  rw [he] at hnorm
  exact pos_of_mul_pos_right hnorm (by norm_num)

end

end MOC
