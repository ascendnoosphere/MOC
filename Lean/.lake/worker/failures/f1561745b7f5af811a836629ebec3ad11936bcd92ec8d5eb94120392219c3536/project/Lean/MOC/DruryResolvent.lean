import MOC.Variational
import Mathlib.Tactic.LinearCombination

/-! The resolvent quadratic at a stationary pair from Drury, Essentially
Hermitian matrices revisited, Proposition 2.1. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem commute_resolvent_real_part (A W : Matrix ι ι ℂ) (ω : ℂ)
    (hA : A.IsHermitian) (h : (ω • (W * A - A * W)).IsHermitian) :
    Commute A (ω • W + star ω • Wᴴ) := by
  have he := h.eq
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, hA.eq] at he
  change A * (ω • W + star ω • Wᴴ) = (ω • W + star ω • Wᴴ) * A
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  have hij := congrArg (fun M : Matrix ι ι ℂ => M i j) he
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hij ⊢
  linear_combination hij

private theorem resolvent_inverse_of_factor (A P T W : Matrix ι ι ℂ)
    (hA : A * A⁻¹ = 1) (hP : P * A = T) (hTW : T * W = 1) (hWT : W * T = 1) :
    P * (A * W) = 1 ∧ (A * W) * P = 1 := by
  have hPT : P = T * A⁻¹ := by
    rw [← hP, Matrix.mul_assoc, hA, Matrix.mul_one]
  constructor
  · rw [← Matrix.mul_assoc, hP, hTW]
  · calc
      (A * W) * P = A * (W * T) * A⁻¹ := by rw [hPT]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hWT, Matrix.mul_one, hA]

private theorem commute_resolvent_of_inverse (X R : Matrix ι ι ℂ) (κ : ℂ)
    (h₁ : (1 - κ • X) * R = 1) (h₂ : R * (1 - κ • X) = 1) : Commute X R := by
  let P : Matrix ι ι ℂ := 1 - κ • X
  have hPR : P * R = 1 := h₁
  have hRP : R * P = 1 := h₂
  have hXP : X * P = P * X := by
    simp only [P, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  change X * R = R * X
  calc
    X * R = (R * P) * (X * R) := by rw [hRP, Matrix.one_mul]
    _ = R * ((P * X) * R) := by simp only [Matrix.mul_assoc]
    _ = R * (X * (P * R)) := by rw [← hXP, Matrix.mul_assoc X P R]
    _ = R * X := by rw [hPR, Matrix.mul_one]

private theorem drury_quadratic_of_resolvent_sum (X R S : Matrix ι ι ℂ)
    (κ ω ell : ℂ) (hκ : κ * star κ = 1)
    (hR : (1 - κ • X) * R = 1) (hS : S * (1 - star κ • X) = 1)
    (h : ω • R + star ω • S = ell • (1 : Matrix ι ι ℂ)) :
    ell • (X * X) +
        (ω * star κ + star ω * κ - ell * (κ + star κ)) • X +
        (ell - ω - star ω) • (1 : Matrix ι ι ℂ) = 0 := by
  let P : Matrix ι ι ℂ := 1 - κ • X
  let Q : Matrix ι ι ℂ := 1 - star κ • X
  have hPR : P * R = 1 := hR
  have hSQ : S * Q = 1 := hS
  have he : ω • Q + star ω • P = ell • (P * Q) := by
    calc
      _ = P * (ω • R + star ω • S) * Q := by
        rw [Matrix.mul_add, Matrix.add_mul]
        simp only [Matrix.mul_smul, Matrix.smul_mul, hPR, Matrix.one_mul,
          Matrix.mul_assoc, hSQ, Matrix.mul_one]
      _ = _ := by rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hκ' : star κ * κ = 1 := (mul_comm _ _).trans hκ
  have hPQ : P * Q = 1 - κ • X - star κ • X + X * X := by
    simp only [P, Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul, hκ, hκ', one_smul] <;> abel
  rw [hPQ] at he
  ext i j
  have hij := congrArg (fun M : Matrix ι ι ℂ => M i j) he
  simp only [P, Q, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.zero_apply] at hij ⊢
  linear_combination -hij

/-- The Hermitian inverse commutator condition forces a real quadratic for
`X = C * A⁻¹` when the common commutant of `A` and `X` consists of scalars.
At a support maximum the multiplier `ω` is the support direction times the determinant. -/
theorem exists_drury_quadratic_of_stationarity [Nonempty ι] (A C : Matrix ι ι ℂ)
    (κ ω : ℂ) (hκ : κ * star κ = 1) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hinv : IsUnit A.det) (hdet : IsUnit (A - κ • C).det)
    (hcrit : (ω • ((A - κ • C)⁻¹ * A - A * (A - κ • C)⁻¹)).IsHermitian)
    (hcentral : ∀ Y : Matrix ι ι ℂ, Commute A Y → Commute (C * A⁻¹) Y →
      ∃ μ : ℂ, Y = μ • (1 : Matrix ι ι ℂ)) :
    let X := C * A⁻¹
    ∃ ell : ℝ, (ell : ℂ) • (X * X) +
        (ω * star κ + star ω * κ - (ell : ℂ) * (κ + star κ)) • X +
        ((ell : ℂ) - ω - star ω) • (1 : Matrix ι ι ℂ) = 0 := by
  classical
  let X := C * A⁻¹
  let T := A - κ • C
  let R := A * T⁻¹
  let S := A * (T⁻¹)ᴴ
  let Y := A * (ω • T⁻¹ + star ω • (T⁻¹)ᴴ)
  have hAAi := A.mul_nonsing_inv hinv
  have hTi := T.nonsing_inv_mul hdet
  have hT := T.mul_nonsing_inv hdet
  have hfactor (ζ : ℂ) : (1 - ζ • X) * A = A - ζ • C := by
    simp only [X, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc,
      A.nonsing_inv_mul hinv, Matrix.mul_one]
  have hfactorStar : (1 - star κ • X) * A = Tᴴ := by
    rw [hfactor]
    simp only [T, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq, hC.eq]
  have hTStar : Tᴴ * (T⁻¹)ᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hTi
  have hTiStar : (T⁻¹)ᴴ * Tᴴ = 1 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_one] using
      congrArg Matrix.conjTranspose hT
  obtain ⟨hR₁, hR₂⟩ := resolvent_inverse_of_factor A (1 - κ • X) T T⁻¹
    hAAi (hfactor κ) hT hTi
  obtain ⟨hS₁, hS₂⟩ := resolvent_inverse_of_factor A (1 - star κ • X) Tᴴ (T⁻¹)ᴴ
    hAAi hfactorStar hTStar hTiStar
  have hY : Y = ω • R + star ω • S := by
    simp only [Y, R, S, Matrix.mul_add, Matrix.mul_smul]
  have hcomm := commute_resolvent_real_part A T⁻¹ ω hA hcrit
  have hAY : Commute A Y := (Commute.refl A).mul_right hcomm
  have hXY : Commute X Y := by
    rw [hY]
    exact ((commute_resolvent_of_inverse X R κ hR₁ hR₂).smul_right ω).add_right
      ((commute_resolvent_of_inverse X S (star κ) hS₁ hS₂).smul_right (star ω))
  obtain ⟨μ, hμ⟩ := hcentral Y hAY hXY
  have hYStar : Yᴴ = Y := by
    simp only [Y, Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, star_star, hA.eq]
    rw [add_comm]
    exact hcomm.eq.symm
  have hμStar : star μ = μ := by
    let i : ι := Classical.choice ‹Nonempty ι›
    have hi := congrArg (fun M : Matrix ι ι ℂ => M i i) hYStar
    simpa only [hμ, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hi
  have hμReal : (μ.re : ℂ) = μ := by
    apply Complex.ext
    · exact Complex.ofReal_re _
    · have hi := congrArg Complex.im hμStar
      simp only [Complex.star_def, Complex.conj_im] at hi
      simp only [Complex.ofReal_im]
      linarith
  refine ⟨μ.re, ?_⟩
  exact drury_quadratic_of_resolvent_sum X R S κ ω (μ.re : ℂ) hκ hR₁ hS₂
    (hY.symm.trans (hμ.trans (congrArg (fun ζ : ℂ => ζ • (1 : Matrix ι ι ℂ)) hμReal.symm)))

end

end MOC
