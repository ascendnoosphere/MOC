import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Complex.Order

/-! Comparison certificates for the two-dimensional Schur complement that
carries a pair of rank-one imaginary outliers. For background on block
Hermitian elimination, see E. V. Haynsworth, DOI: 10.1016/0024-3795(68)90050-5. -/

open Matrix
open scoped ComplexOrder Matrix

namespace MOC
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Schur elimination preserves the lower top-block bound and keeps the
result below the old top-block upper bound. The lower-bound hypothesis
only asks that subtracting the proposed lower bound on the top block
leaves a positive semidefinite full matrix. -/
theorem schurPlane_posSemidef_sandwich
    (A L U : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)
    (hD : D.PosDef)
    (hL : (fromBlocks (A - L) B Bᴴ D).PosSemidef)
    (hU : (U - A).PosSemidef) :
    ((A - B * D⁻¹ * Bᴴ) - L).PosSemidef ∧ (U - (A - B * D⁻¹ * Bᴴ)).PosSemidef := by
  letI := hD.isUnit.invertible
  constructor
  · have hh := (Matrix.PosSemidef.fromBlocks₂₂ (A - L) B hD).mp hL
    rwa [sub_right_comm] at hh
  · have hb := hD.inv.posSemidef.mul_mul_conjTranspose_same B
    have hh := hU.add hb
    rwa [sub_sub_eq_add_sub, add_sub_right_comm]

variable [DecidableEq m]

private theorem det_one_add_posSemidef_re_ge_one
    (C : Matrix m m ℂ) (hC : C.PosSemidef) : 1 ≤ (1 + C).det.re := by
  let V := hC.1.eigenvectorUnitary
  let e := hC.1.eigenvalues
  have hV : V.val * V.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp V.property
  have hdiag : C = V.val * diagonal (fun i => (e i : ℂ)) * V.valᴴ := hC.1.spectral_theorem
  have hf : 1 + C = V.val * diagonal (fun i => ((1 + e i : ℝ) : ℂ)) * V.valᴴ := by
    simp only [Complex.ofReal_add, Complex.ofReal_one]
    rw [← Matrix.diagonal_add, Matrix.diagonal_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      hV, ← hdiag]
  have hd : (1 + C).det = (∏ i, (1 + e i) : ℝ) := by
    rw [hf, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Complex.ofReal_prod]
    have he : V.val.det * V.valᴴ.det = 1 := by rw [← Matrix.det_mul, hV, Matrix.det_one]
    rw [mul_right_comm, he, one_mul]
  rw [hd, Complex.ofReal_re]
  simpa only [Finset.prod_const_one] using
    (Finset.prod_le_prod (s := Finset.univ) (fun i _ => (zero_le_one : (0 : ℝ) ≤ 1))
      (fun i _ => le_add_of_nonneg_right (hC.eigenvalues_nonneg i)))

/-- A positive definite Hermitian matrix's determinant is monotone under
positive semidefinite additions. Normalizing by its square root reduces
the claim to nonnegative eigenvalues of a single matrix. -/
theorem det_re_mono_of_posDef {A B : Matrix m m ℂ} (hA : A.PosDef)
    (hAB : (B - A).PosSemidef) : A.det.re ≤ B.det.re := by
  let S := hA.posSemidef.sqrt
  have hS : S.IsHermitian := hA.posSemidef.posSemidef_sqrt.1
  have hSS : S * S = A := by
    rw [← pow_two]
    exact hA.posSemidef.sq_sqrt
  have hunit : IsUnit S.det := by
    have h := Matrix.isUnit_iff_isUnit_det A |>.mp hA.isUnit
    rw [← hSS, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  let T := S⁻¹
  have hT : Tᴴ = T := hS.inv.eq
  have hTAT : Tᴴ * A * T = 1 := by
    change S⁻¹ᴴ * A * S⁻¹ = 1
    rw [hT, ← hSS, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hunit]
  let C := Tᴴ * (B - A) * T
  have hC : C.PosSemidef := hAB.conjTranspose_mul_mul_same T
  have hTC : Tᴴ * B * T = 1 + C := by
    dsimp only [C]
    rw [Matrix.mul_sub, Matrix.sub_mul, hTAT, add_sub_cancel]
  have he : B.det = A.det * (1 + C).det := by
    have h₁ := congrArg Matrix.det hTAT
    have h₂ := congrArg Matrix.det hTC
    simp only [Matrix.det_mul, Matrix.det_one] at h₁ h₂
    linear_combination -B.det * h₁ + A.det * h₂
  have hAre : 0 ≤ A.det.re := (Complex.nonneg_iff.mp (le_of_lt hA.det_pos)).1
  have hAim : A.det.im = 0 := (Complex.nonneg_iff.mp (le_of_lt hA.det_pos)).2.symm
  rw [he, Complex.mul_re, hAim, zero_mul, sub_zero]
  exact le_mul_of_one_le_right hAre (det_one_add_posSemidef_re_ge_one C hC)

end
end MOC
