import MOC.Core
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.LinearCombination

/-! Exact determinant compression for rank-one unitary phase updates. The
Householder reflection is the phase `z = -1` (Drury, LAA 298, 1999). -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one phase update in the direction of `v`. -/
def rankOnePhase (v : ι → ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  1 + (z - 1) • vecMulVec v (star ∘ v)

theorem rankOnePhase_unitary (v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1) :
    IsUnitary (rankOnePhase v z) := by
  let P : Matrix ι ι ℂ := vecMulVec v (star ∘ v)
  have hPstar : Pᴴ = P := by
    ext i j
    simp only [P, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Function.comp_apply,
      star_mul', star_star]
    ring
  have hPmul : P * P = P := by
    ext i j
    simp only [P, Matrix.mul_apply, Matrix.vecMulVec_apply, Function.comp_apply]
    calc
      _ = ∑ k, (v i * star (v j)) * (star (v k) * v k) :=
        Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [← Finset.mul_sum, hv, mul_one]
  have hstar : (rankOnePhase v z)ᴴ = 1 + (star z - 1) • P := by
    simp only [rankOnePhase, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, star_sub, star_one, ← show P = vecMulVec v (star ∘ v) from rfl,
      hPstar]
  have hmul (x y : ℂ) (hxy : x * y = 1) :
      (1 + (x - 1) • P) * (1 + (y - 1) • P) = 1 := by
    have hsum : (y - 1) + ((x - 1) + (x - 1) * (y - 1)) = 0 := by
      calc
        _ = x * y - 1 := by ring
        _ = 0 := sub_eq_zero.mpr hxy
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPmul]
    rw [add_assoc, ← add_smul, ← add_smul, hsum, zero_smul, add_zero]
  change rankOnePhase v z * (rankOnePhase v z)ᴴ = 1 ∧
    (rankOnePhase v z)ᴴ * rankOnePhase v z = 1
  rw [hstar]
  exact ⟨hmul z (star z) hz, hmul (star z) z (by rwa [mul_comm])⟩

theorem det_rankOnePhase (v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) :
    (rankOnePhase v z).det = z := by
  let L : Matrix ι (Fin 1) ℂ := Matrix.of fun i _ => v i
  let R : Matrix (Fin 1) ι ℂ := Matrix.of fun _ j => star (v j)
  have hLR : L * R = vecMulVec v (star ∘ v) := by
    ext i j
    simp [L, R, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hRL : R * L = 1 := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [L, R, Matrix.mul_apply, hv]
  rw [rankOnePhase, ← hLR, ← Matrix.smul_mul, Matrix.det_one_add_mul_comm,
    Matrix.mul_smul, hRL, Matrix.det_fin_one]
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- The two-by-two compression of the regular spectral determinant. Each
summand is a rank-one matrix scaled by the corresponding coordinate mass. -/
def rankOneSpectralCompression (a b v : ι → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => ∑ k,
    (if i = 0 then 1 else b k) * (star (v k) * v k / (a k + b k)) *
      (if j = 0 then a k else 1)

theorem rankOneSpectralCompression_diagonal_sum (a b v : ι → ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hreg : ∀ i, a i + b i ≠ 0) :
    let N := rankOneSpectralCompression a b v
    N 0 0 + N 1 1 = 1 := by
  simp [rankOneSpectralCompression, ← Finset.sum_add_distrib]
  calc
    _ = ∑ i, star (v i) * v i :=
      Finset.sum_congr rfl fun i _ => by field_simp [hreg i] <;> ring
    _ = 1 := hv

/-- With nonzero identity matching factors, the determinant for a rank-one
phase update is its diagonal matching product times a two-by-two formula. -/
theorem determinantValue_rankOnePhase (a b v : ι → ℂ) (z : ℂ)
    (hv : ∑ i, star (v i) * v i = 1) (hz : z * star z = 1)
    (hreg : ∀ i, a i + b i ≠ 0) :
    determinantValue a b (rankOnePhase v z) =
      (∏ i, (a i + b i)) *
        (1 - (2 - z - star z) * (rankOneSpectralCompression a b v).det) := by
  let U := rankOnePhase v z
  let N := rankOneSpectralCompression a b v
  let X : Matrix ι (Fin 2) ℂ := Matrix.of fun i j =>
    (v i / (a i + b i)) * (if j = 0 then a i else 1)
  let Y : Matrix (Fin 2) ι ℂ := Matrix.of fun i j =>
    (if i = 0 then 1 else b j) * star (v j)
  have hYX : Y * X = N := by
    ext i j
    simp only [X, Y, N, rankOneSpectralCompression, Matrix.mul_apply, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hXY (i j : ι) :
      (a i + b i) * (X * Y) i j = (a i + b j) * (v i * star (v j)) := by
    simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hreg i]
    <;> ring
  have hU : IsUnitary U := rankOnePhase_unitary v z hv hz
  have hmat : (diagonal a + U * diagonal b * Uᴴ) * U =
      diagonal (fun i => a i + b i) * (1 + (z - 1) • (X * Y)) := by
    rw [Matrix.add_mul, Matrix.mul_assoc (U * diagonal b), hU.2, Matrix.mul_one]
    ext i j
    have hd : (a i + b j) * (1 : Matrix ι ι ℂ) i j =
        (a i + b i) * (1 : Matrix ι ι ℂ) i j := by
      by_cases hij : i = j
      · subst j
        rfl
      · simp [Matrix.one_apply_ne hij]
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, U, rankOnePhase,
      Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Function.comp_apply]
    calc
      _ = (a i + b j) * (1 : Matrix ι ι ℂ) i j +
          (z - 1) * ((a i + b j) * (v i * star (v j))) := by ring
      _ = _ := by rw [hd, ← hXY]; ring
  have hdet : determinantValue a b U * z =
      (∏ i, (a i + b i)) * (1 + (z - 1) • N).det := by
    change (diagonal a + U * diagonal b * Uᴴ).det * z = _
    rw [← det_rankOnePhase v z hv, ← Matrix.det_mul]
    change ((diagonal a + U * diagonal b * Uᴴ) * U).det = _
    rw [hmat, Matrix.det_mul, Matrix.det_diagonal, ← Matrix.smul_mul,
      Matrix.det_one_add_mul_comm, Matrix.mul_smul, hYX]
  have htr : N 0 0 + N 1 1 = 1 :=
    rankOneSpectralCompression_diagonal_sum a b v hv hreg
  have hsmall : (1 + (z - 1) • N).det = z + (z - 1)^2 * N.det := by
    simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
    linear_combination (z - 1) * htr
  have hphase : z + (z - 1)^2 * N.det = (1 - (2 - z - star z) * N.det) * z := by
    linear_combination -N.det * hz
  have hzn : z ≠ 0 := by
    intro h
    simp [h] at hz
  apply mul_right_cancel₀ hzn
  change determinantValue a b U * z = ((∏ i, (a i + b i)) *
    (1 - (2 - z - star z) * N.det)) * z
  rw [hdet, hsmall, hphase, mul_assoc]

end

end MOC
