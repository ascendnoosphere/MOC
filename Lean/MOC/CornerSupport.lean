import MOC.StrongSupport
import MOC.Support
import Mathlib.Tactic.LinearCombination

/-! The two-direction corner theorem of Bebiano and Queiró, with the
singular case supplied by determinant inclusion for singular sums. -/

open Matrix

namespace MOC

private theorem eq_of_two_noncollinear_projections {η ξ z w : ℂ}
    (hdir : η * star ξ ≠ ξ * star η)
    (hη : (η * z).re = (η * w).re) (hξ : (ξ * z).re = (ξ * w).re) : z = w := by
  let D := η.re * ξ.im - η.im * ξ.re
  have hD : D ≠ 0 := by
    intro hzero
    apply hdir
    apply Complex.ext
    · simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · dsimp only [D] at hzero
      simp only [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      linear_combination (-2 : ℝ) * hzero
  have h₁ : (η * (z - w)).re = 0 := by rw [mul_sub, Complex.sub_re, hη, sub_self]
  have h₂ : (ξ * (z - w)).re = 0 := by rw [mul_sub, Complex.sub_re, hξ, sub_self]
  simp only [Complex.mul_re] at h₁ h₂
  have hre : D * (z - w).re = 0 := by
    dsimp only [D]
    linear_combination ξ.im * h₁ - η.im * h₂
  have him : D * (z - w).im = 0 := by
    dsimp only [D]
    linear_combination ξ.re * h₁ - η.re * h₂
  exact sub_eq_zero.mp (Complex.ext ((mul_eq_zero.mp hre).resolve_left hD)
    ((mul_eq_zero.mp him).resolve_left hD))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem normal_sum_of_commuting_spectral_pair (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hAB : Commute (diagonal a) (U * diagonal b * Uᴴ)) :
    IsStarNormal (diagonal a + U * diagonal b * Uᴴ) := by
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  have hn (c : ι → ℂ) : (diagonal c)ᴴ * diagonal c = diagonal c * (diagonal c)ᴴ := by
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm (star (c i)) (c i))
  have ha : Aᴴ * A = A * Aᴴ := hn a
  have hmul (X Y : Matrix ι ι ℂ) :
      (U * X * Uᴴ) * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hU.2, Matrix.one_mul]
  have hBstar : Bᴴ = U * (diagonal b)ᴴ * Uᴴ := by
    simp only [B, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hb : Bᴴ * B = B * Bᴴ := by
    rw [hBstar]
    change (U * (diagonal b)ᴴ * Uᴴ) * (U * diagonal b * Uᴴ) =
      (U * diagonal b * Uᴴ) * (U * (diagonal b)ᴴ * Uᴴ)
    rw [hmul, hmul, hn b]
  have hBAstar : Commute B Aᴴ :=
    commute_adjoint_of_commute_spectral_diagonalization b U A hU hAB.symm
  have hOne : IsUnitary (1 : Matrix ι ι ℂ) := by simp [IsUnitary]
  have hA1 : Commute ((1 : Matrix ι ι ℂ) * diagonal a * (1 : Matrix ι ι ℂ)ᴴ) B := by
    simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one] using hAB
  have hABstar : Commute A Bᴴ := by
    simpa only [A, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one] using
      (commute_adjoint_of_commute_spectral_diagonalization a 1 B hOne hA1)
  constructor
  change (A + B)ᴴ * (A + B) = (A + B) * (A + B)ᴴ
  simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul,
    ha, hb, ← hBAstar.eq, ← hABstar.eq]
  abel

/-- Any determinant value that maximizes two noncollinear real projections
is a matching product. The conclusion includes zero determinants. -/
theorem exists_matchingProduct_eq_of_two_support_maxima (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η ξ : ℂ) (hdir : η * star ξ ≠ ξ * star η)
    (hη : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re)
    (hξ : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (ξ * determinantValue a b V).re ≤ (ξ * determinantValue a b U).re) :
    ∃ σ, matchingProduct a b σ = determinantValue a b U := by
  obtain ⟨W, hW, hmax, htie⟩ := exists_support_frobenius_maximizer a b (η + ξ)
  have hηW := hη W hW
  have hξW := hξ W hW
  have hsumW := hmax U hU
  simp only [add_mul, Complex.add_re] at hsumW
  have hWD : determinantValue a b W = determinantValue a b U :=
    eq_of_two_noncollinear_projections hdir (by linarith only [hηW, hξW, hsumW])
      (by linarith only [hηW, hξW, hsumW])
  have hholds : Holds a b W := by
    by_cases hzero : determinantValue a b W = 0
    · exact holds_of_singular a b hW hzero
    let B := W * diagonal b * Wᴴ
    have hbase (μ : ℂ) (hμ : ∀ V : Matrix ι ι ℂ, IsUnitary V →
        (μ * determinantValue a b V).re ≤ (μ * determinantValue a b U).re)
        (R : Matrix ι ι ℂ) (hR : IsUnitary R) :
        (μ * (diagonal a + R * B * Rᴴ).det).re ≤ (μ * (diagonal a + B).det).re := by
      have hR' : IsUnitary Rᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hR.2,
        by simpa only [Matrix.conjTranspose_conjTranspose] using hR.1⟩
      have hRW : IsUnitary (R * W) := by
        simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ W hR' hW
      have h := hμ (R * W) hRW
      rw [← hWD] at h
      simpa only [determinantValue, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h
    have hcomm : Commute (diagonal a) B :=
      commute_of_two_support_maxima (diagonal a) B η ξ hzero hdir (hbase η hη) (hbase ξ hξ)
    exact holds_of_normal_support_frobenius_maximum a b hW (η + ξ)
      (normal_sum_of_commuting_spectral_pair a b W hW hcomm) hmax htie
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a b W).mp hholds (η + ξ)
  rw [hWD] at hσ
  simp only [add_mul, Complex.add_re] at hσ
  obtain ⟨V, hV, hVσ⟩ := matchingProduct_mem_determinantRange a b σ
  have hηV := hη V hV
  have hξV := hξ V hV
  rw [hVσ] at hηV hξV
  exact ⟨σ, eq_of_two_noncollinear_projections hdir (by linarith only [hηV, hξV, hσ])
    (by linarith only [hηV, hξV, hσ])⟩

end MOC
