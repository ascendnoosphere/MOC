import MOC.Core
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Linarith

/-! The trace annihilator of a rank stratum vanishes when the real spectrum
is simple and the second spectrum has pairwise distinct imaginary parts. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem diagonal_of_commute_injective {d : ι → ℂ} (hd : Function.Injective d)
    {Z : Matrix ι ι ℂ} (hZ : Commute (diagonal d) Z) : Z = diagonal Z.diag := by
  ext i j : 1
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.diag_apply]
  · have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hZ.eq
    change (diagonal d * Z) i j = (Z * diagonal d) i j at he
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (Z i j)] at he
    rw [Matrix.diagonal_apply_ne _ hij]
    by_contra hz
    exact hij (hd (mul_right_cancel₀ hz he))

/-- A matrix in the real trace annihilator of the rank-stratum tangent space,
the real diagonal variations, and the unitary orbit variations is zero. The
hypotheses express these annihilator conditions through matrix products and
the Hermitian commutator. -/
theorem singular_orbit_annihilator_eq_zero (a : ι → ℝ) (b : ι → ℂ)
    (U Y : Matrix ι ι ℂ) (hU : IsUnitary U) (ha : Function.Injective a)
    (hb : Function.Injective fun i => (b i).im)
    (hsum : ∀ i j, (a i : ℂ) + b j ≠ 0) :
    let A := diagonal fun i => (a i : ℂ)
    let B := U * diagonal b * Uᴴ
    (A + B) * Y = 0 → Y * (A + B) = 0 → (∀ i, (Y i i).re = 0) →
      (B * Y - Y * B).IsHermitian → Y = 0 := by
  intro A B hleft hright hre hBY
  have hbalance : A * Y - Y * A = -(B * Y - Y * B) := by
    calc
      _ = (A + B) * Y - Y * (A + B) - (B * Y - Y * B) := by
        rw [Matrix.add_mul, Matrix.mul_add]
        abel
      _ = _ := by rw [hleft, hright, sub_self, zero_sub]
  have hAH : Aᴴ = A := by
    simp only [A, Matrix.diagonal_conjTranspose]
    exact congrArg diagonal (funext fun i => by
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal])
  have hAX : Yᴴ * A - A * Yᴴ = A * Y - Y * A := by
    have h : (A * Y - Y * A)ᴴ = A * Y - Y * A := by
      rw [hbalance, Matrix.conjTranspose_neg, hBY.eq]
    simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hAH] using h
  have hAplus : Commute A (Y + Yᴴ) := by
    change A * (Y + Yᴴ) = (Y + Yᴴ) * A
    simp only [Matrix.mul_add, Matrix.add_mul]
    calc
      _ = (A * Y - Y * A) + A * Yᴴ + Y * A := by abel
      _ = _ := by rw [← hAX]; abel
  have hYsum : Y + Yᴴ = 0 := by
    rw [diagonal_of_commute_injective (Complex.ofReal_injective.comp ha) hAplus]
    ext i j : 1
    by_cases hij : i = j
    · subst j
      simp [Matrix.diag_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
        Complex.star_def, Complex.add_conj, hre i]
    · simp [Matrix.diagonal_apply_ne _ hij]
  have hY : Yᴴ = -Y := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hYsum)
  have hBstar : Bᴴ * Y - Y * Bᴴ = B * Y - Y * B := by
    calc
      _ = (B * Y - Y * B)ᴴ := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hY,
          Matrix.neg_mul, Matrix.mul_neg]
        abel
      _ = _ := hBY.eq
  have hD : Commute (B - Bᴴ) Y := by
    change (B - Bᴴ) * Y = Y * (B - Bᴴ)
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    calc
      _ = (B * Y - Y * B) - (Bᴴ * Y - Y * Bᴴ) + (Y * B - Y * Bᴴ) := by abel
      _ = _ := by rw [hBstar, sub_self, zero_add]
  let c : ι → ℂ := fun i => b i - star (b i)
  have hc : Function.Injective c := by
    intro i j hij
    apply hb
    have he := congrArg Complex.im hij
    simp only [c, Complex.star_def, Complex.sub_im, Complex.conj_im] at he
    linarith
  have hBc : B - Bᴴ = U * diagonal c * Uᴴ := by
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_sub, Matrix.diagonal_sub]
    simp [Matrix.mul_assoc]
  let Z := Uᴴ * Y * U
  have hDZ : Commute (diagonal c) Z := by
    have he : (U * diagonal c * Uᴴ) * Y = Y * (U * diagonal c * Uᴴ) := by
      simpa only [hBc] using hD.eq
    change diagonal c * Z = Z * diagonal c
    calc
      _ = Uᴴ * ((U * diagonal c * Uᴴ) * Y) * U := by
        simp only [Z, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]
      _ = Uᴴ * (Y * (U * diagonal c * Uᴴ)) * U := by rw [he]
      _ = _ := by simp only [Z, Matrix.mul_assoc, hU.2, Matrix.mul_one]
  have hBZ : Commute (diagonal b) Z := by
    change diagonal b * Z = Z * diagonal b
    rw [diagonal_of_commute_injective hc hDZ]
    simp only [Matrix.diagonal_mul_diagonal, mul_comm]
  have hUZ : U * Z = Y * U := by
    simp only [Z, ← Matrix.mul_assoc, hU.1, Matrix.one_mul]
  have hZUH : Z * Uᴴ = Uᴴ * Y := by
    simp only [Z, Matrix.mul_assoc, hU.1, Matrix.mul_one]
  have hcommB : B * Y = Y * B := by
    calc
      _ = U * (diagonal b * Z) * Uᴴ := by simp only [B, Matrix.mul_assoc, hZUH]
      _ = U * (Z * diagonal b) * Uᴴ := by rw [hBZ.eq]
      _ = _ := by simp only [B, ← Matrix.mul_assoc, hUZ]
  have hcommA : A * Y = Y * A := by
    rw [hcommB, sub_self, neg_zero] at hbalance
    exact sub_eq_zero.mp hbalance
  let T := Uᴴ * Y
  have hT : T * A + diagonal b * T = 0 := by
    calc
      _ = Uᴴ * ((A + B) * Y) := by
        simp only [T, B, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        rw [← hcommA, ← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]
      _ = _ := by rw [hleft, Matrix.mul_zero]
  have hTzero : T = 0 := by
    ext i j : 1
    have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hT
    change (T * diagonal (fun i => (a i : ℂ)) + diagonal b * T) i j = 0 at he
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      mul_comm (T i j), ← add_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (hsum j i)
  calc
    Y = U * T := by simp only [T, ← Matrix.mul_assoc, hU.1, Matrix.one_mul]
    _ = 0 := by rw [hTzero, Matrix.mul_zero]

end
