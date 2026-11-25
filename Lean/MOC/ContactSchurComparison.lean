import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Complex.Order
import Mathlib.Tactic.Ring

/-! Codimension-one compressions to the complements of two unit vectors
can be aligned so the cross-projection scales one coordinate by `ρ`.
This is the resulting block determinant comparison. -/

open Matrix
open scoped ComplexOrder

namespace MOC

private theorem nonneg_unit_entry {M : Matrix Unit Unit ℂ} (hM : M.PosSemidef) :
    0 ≤ M () () := by
  simpa [Matrix.mulVec, dotProduct] using hM.2 (fun _ => 1)

/-- The determinant difference of two aligned compressions. Their common
block is `K`. The real parameter `ρ` is the overlap of the exceptional
unit vectors. Positivity of the augmented `c)-block is the Schur bound
needed to control the difference. -/
theorem det_aligned_contact_compressions_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℂ) (c d : Matrix ι Unit ℂ) (w u v ρ : ℝ)
    (hK : K.PosDef)
    (hc : (fromBlocks K c cᴴ (scalar Unit (u : ℂ))).PosSemidef)
    (hv : 0 ≤ v) (hρ : ρ ^ 2 ≤ 1) :
    let x := (ρ : ℂ) • c - d
    let y := c - (ρ : ℂ) • d
    (fromBlocks K x xᴴ (scalar Unit ((w + ρ ^ 2 * u - v : ℝ) : ℂ))).det.re ≤
      (fromBlocks K y yᴴ (scalar Unit ((w + u - ρ ^ 2 * v : ℝ) : ℂ))).det.re := by
  letI : Invertible K := hK.isUnit.invertible
  let Q (x : Matrix ι Unit ℂ) : ℂ := (xᴴ * K⁻¹ * x) () ()
  let B (x : Matrix ι Unit ℂ) (z : ℂ) := (fromBlocks K x xᴴ (scalar Unit z)).det
  have hB (x : Matrix ι Unit ℂ) (z : ℂ) : B x z = K.det * (z - Q x) := by
    dsimp only [B, Q]
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
      Matrix.det_unique (scalar Unit z - xᴴ * K⁻¹ * x)]
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.sub_apply]
  have hstar : star (ρ : ℂ) = (ρ : ℂ) := by simp
  have hQ :
      Q (c - (ρ : ℂ) • d) - Q ((ρ : ℂ) • c - d) =
        (1 - (ρ : ℂ) ^ 2) * (Q c - Q d) := by
    simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hstar,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have huv : 0 ≤ u - (Q c).re := by
    have hh := (Matrix.PosSemidef.fromBlocks₁₁ c _ hK).mp hc
    have h := (Complex.nonneg_iff.mp (nonneg_unit_entry hh)).1
    simpa only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Complex.sub_re, Complex.ofReal_re, Q] using h
  have hd : 0 ≤ (Q d).re :=
    (Complex.nonneg_iff.mp (nonneg_unit_entry
      (hK.inv.posSemidef.conjTranspose_mul_mul_same d))).1
  have hdiff :
      B (c - (ρ : ℂ) • d) (↑(w + u - ρ ^ 2 * v : ℝ)) -
          B ((ρ : ℂ) • c - d) (↑(w + ρ ^ 2 * u - v : ℝ)) =
        K.det * (1 - (ρ : ℂ) ^ 2) * ((u : ℂ) - Q c + ((v : ℂ) + Q d)) := by
    calc
      _ = K.det * ((1 - (ρ : ℂ) ^ 2) * ((u : ℂ) + (v : ℂ)) -
          (Q (c - (ρ : ℂ) • d) - Q ((ρ : ℂ) • c - d))) := by
        rw [hB, hB]
        simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
        ring
      _ = _ := by rw [hQ]; ring
  have hcast : 1 - (ρ : ℂ) ^ 2 = ((1 - ρ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  have hKre := Complex.nonneg_iff.mp hK.det_pos.le
  have hdre := congrArg Complex.re hdiff
  simp only [Complex.sub_re, hcast, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.ofReal_im, Complex.ofReal_re, ← hKre.2, Complex.zero_im, zero_mul, mul_zero,
    sub_zero, zero_add, add_zero] at hdre
  change (B ((ρ : ℂ) • c - d) (↑(w + ρ ^ 2 * u - v : ℝ))).re ≤
    (B (c - (ρ : ℂ) • d) (↑(w + u - ρ ^ 2 * v : ℝ))).re
  apply sub_nonneg.mp
  rw [hdre]
  exact mul_nonneg (mul_nonneg hKre.1 (sub_nonneg.mpr hρ))
    (add_nonneg huv (add_nonneg hv hd))

end MOC
