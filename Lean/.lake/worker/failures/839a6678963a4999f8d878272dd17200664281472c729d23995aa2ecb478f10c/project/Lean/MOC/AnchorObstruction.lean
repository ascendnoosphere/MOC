import MOC.Pencil
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! The Walsh example obstructs monotone rounding by a single paired
coordinate completion. Four phase evaluations check each completion circle. -/

open Matrix

namespace MOC

local notation "gauss" => GaussianInt.toComplex

private def gaussI : GaussianInt := ⟨0, 1⟩

private theorem gaussI_toComplex : gauss gaussI = Complex.I := by
  change ((⟨0, 1⟩ : GaussianInt) : ℂ) = Complex.I
  rw [GaussianInt.toComplex_def']
  simp

private def walshSigns : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]

private def walshLeftInt : Fin 4 → GaussianInt := ![1, -1, -3 * gaussI, 3 * gaussI]

private def walshRightInt : Fin 4 → GaussianInt := ![-3, 3, -gaussI, gaussI]

private theorem walshSigns_cases (i j : Fin 4) :
    walshSigns i j = 1 ∨ walshSigns i j = -1 := by
  fin_cases i <;> fin_cases j <;> decide

private def completionInt (i j : Fin 4) (z : GaussianInt) : Matrix (Fin 3) (Fin 3) GaussianInt :=
  Matrix.of fun k l => 3 * walshSigns (i.succAbove k) (j.succAbove l) +
    (walshSigns i j + 2 * z) * (walshSigns (i.succAbove k) j * walshSigns i (j.succAbove l))

private def scaledSum {n : ℕ} (a b : Fin n → GaussianInt) (d : ℕ)
    (V : Matrix (Fin n) (Fin n) GaussianInt) : Matrix (Fin n) (Fin n) GaussianInt :=
  ((d : GaussianInt) ^ 2) • diagonal a + V * diagonal b * Vᴴ

private def scaledSupport {n : ℕ} (a b : Fin n → GaussianInt) (d : ℕ)
    (V : Matrix (Fin n) (Fin n) GaussianInt) (k : GaussianInt) : ℤ :=
  (k * (scaledSum a b d V).det).re

private def scaledCompletionSupport (i j : Fin 4) (z : GaussianInt) : ℤ :=
  scaledSupport (walshLeftInt ∘ i.succAbove) (walshRightInt ∘ j.succAbove) 6
    (completionInt i j z) (gaussI * (walshLeftInt i + walshRightInt j))

noncomputable section

private def walsh : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • walshSigns.map gauss

private def walshLeft : Fin 4 → ℂ := gauss ∘ walshLeftInt

private def walshRight : Fin 4 → ℂ := gauss ∘ walshRightInt

private theorem walsh_re (i j : Fin 4) :
    (walsh i j).re = ((walshSigns i j).re : ℝ) / 2 := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.ofReal_div (1 : ℝ) 2).symm
  rw [walsh, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, h, Complex.re_ofReal_mul]
  rw [← GaussianInt.to_real_re]
  ring

private def completionColumn (i j : Fin 4) : Matrix (Fin 3) (Fin 1) ℂ :=
  Matrix.of fun k _ => (4 / 3 : ℂ) * walsh (i.succAbove k) j

private def completionRow (i j : Fin 4) : Matrix (Fin 1) (Fin 3) ℂ :=
  Matrix.of fun _ l => walsh i (j.succAbove l)

private def completionCenter (i j : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  walsh.submatrix i.succAbove j.succAbove + star (walsh i j) •
    (completionColumn i j * completionRow i j)

private def completion (i j : Fin 4) (z : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  completionCenter i j + z • (completionColumn i j * completionRow i j)

private def completionSupport (i j : Fin 4) (z : ℂ) : ℂ :=
  Complex.I * (walshLeft i + walshRight j) *
    determinantValue (walshLeft ∘ i.succAbove) (walshRight ∘ j.succAbove) (completion i j z)

theorem walsh_unitary : IsUnitary walsh := by
  have hs : walshSigns * walshSignsᴴ = (4 : GaussianInt) • (1 : Matrix (Fin 4) (Fin 4) GaussianInt) ∧
      walshSignsᴴ * walshSigns = (4 : GaussianInt) • (1 : Matrix (Fin 4) (Fin 4) GaussianInt) := by
    constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;> decide +kernel
  have ht := Matrix.conjTranspose_map (A := walshSigns) gauss GaussianInt.toComplex_star
  have h₁ := congrArg (fun M : Matrix (Fin 4) (Fin 4) GaussianInt => M.map gauss) hs.1
  have h₂ := congrArg (fun M : Matrix (Fin 4) (Fin 4) GaussianInt => M.map gauss) hs.2
  simp only [Matrix.map_mul, ht, Matrix.map_smul' gauss _ _ (map_mul gauss),
    Matrix.map_one gauss (map_zero gauss) (map_one gauss), map_ofNat] at h₁ h₂
  constructor <;>
    simp only [walsh, Matrix.conjTranspose_smul, star_div₀, star_one, star_ofNat,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, h₁, h₂] <;> norm_num

private theorem completionInt_map (i j : Fin 4) (z : GaussianInt) :
    (completionInt i j z).map gauss = (6 : ℂ) • completion i j (gauss z) := by
  ext k l
  have hentry : (completionColumn i j * completionRow i j) k l =
      (4 / 3 : ℂ) * walsh (i.succAbove k) j * walsh i (j.succAbove l) := by
    simp only [completionColumn, completionRow, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one]
  have hstar : star (gauss (walshSigns i j)) = gauss (walshSigns i j) := by
    rcases walshSigns_cases i j with h | h <;> simp [h]
  simp only [completionInt, Matrix.map_apply, Matrix.of_apply, map_add, map_mul, map_ofNat,
    completion, completionCenter, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.submatrix_apply, hentry, walsh, star_mul', hstar, star_div₀, star_one, star_ofNat]
  ring

private theorem scaledSupport_re {n : ℕ} (a b : Fin n → GaussianInt) (d : ℕ)
    (V : Matrix (Fin n) (Fin n) GaussianInt) (k : GaussianInt)
    (U : Matrix (Fin n) (Fin n) ℂ) (hV : V.map gauss = (d : ℂ) • U) :
    (scaledSupport a b d V k : ℝ) = ((d : ℝ) ^ 2) ^ n *
      (gauss k * determinantValue (gauss ∘ a) (gauss ∘ b) U).re := by
  have hstar := Matrix.conjTranspose_map (A := V) gauss GaussianInt.toComplex_star
  have hm : (scaledSum a b d V).map gauss = ((d : ℂ) ^ 2) •
      (diagonal (gauss ∘ a) + U * diagonal (gauss ∘ b) * Uᴴ) := by
    change (scaledSum a b d V).map gauss = ((d : ℂ) ^ 2) •
      (diagonal (fun i => gauss (a i)) + U * diagonal (fun i => gauss (b i)) * Uᴴ)
    simp only [scaledSum, Matrix.map_add gauss (map_add gauss),
      Matrix.map_smul' gauss _ _ (map_mul gauss), map_mul, map_natCast, Matrix.map_mul,
      Matrix.diagonal_map (map_zero gauss), hstar, hV, Matrix.conjTranspose_smul, star_natCast,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two, smul_add]
  have hd : ((((d : ℝ) ^ 2) ^ n : ℝ) : ℂ) = ((d : ℂ) ^ 2) ^ n := by
    simp only [Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [scaledSupport, GaussianInt.to_real_re]
  change (gauss (k * (scaledSum a b d V).det)).re = _
  rw [map_mul, RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_smul,
    Fintype.card_fin, ← hd, mul_left_comm, Complex.re_ofReal_mul, determinantValue]

private theorem scaledCompletionSupport_re (i j : Fin 4) (z : GaussianInt) :
    (scaledCompletionSupport i j z : ℝ) = 46656 * (completionSupport i j (gauss z)).re := by
  have h := scaledSupport_re (walshLeftInt ∘ i.succAbove) (walshRightInt ∘ j.succAbove)
    6 (completionInt i j z) (gaussI * (walshLeftInt i + walshRightInt j)) _
    (completionInt_map i j z)
  norm_num only [scaledCompletionSupport, completionSupport, walshLeft, walshRight,
    Function.comp_apply, map_mul, map_add, gaussI_toComplex, Nat.cast_ofNat] at h ⊢
  exact h

private theorem completion_biaffine (i j : Fin 4) :
    ∃ a b c d : ℂ, ∀ z : ℂ,
      completionSupport i j z = a + b * z + c * star z + d * (z * star z) := by
  let A := diagonal (walshLeft ∘ i.succAbove)
  let B := diagonal (walshRight ∘ j.succAbove)
  let L := completionColumn i j
  let R := completionRow i j
  let D := completionCenter i j
  let p (s t : ℂ) := (A + (D + s • (L * R)) * B * (Dᴴ + t • (Rᴴ * Lᴴ))).det
  let k := Complex.I * (walshLeft i + walshRight j)
  refine ⟨k * p 0 0, k * (p 1 0 - p 0 0), k * (p 0 1 - p 0 0),
    k * (p 1 1 - p 1 0 - p 0 1 + p 0 0), fun z => ?_⟩
  have hf : completionSupport i j z = k * p z (star z) := by
    simp only [completionSupport, determinantValue, completion, p, A, B, D, L, R, k,
      Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  have hp : p z (star z) = p 0 0 + z * (p 1 0 - p 0 0) + star z * (p 0 1 - p 0 0) +
      z * star z * (p 1 1 - p 1 0 - p 0 1 + p 0 0) := by
    simpa only [p, Matrix.one_mul] using
      det_completion_biaffine A 1 D Dᴴ B L R Rᴴ Lᴴ z (star z)
  rw [hf, hp]
  ring

-- Clear the denominator of the completion before evaluating the four phases.
private theorem completion_four_phases_int (i j : Fin 4) :
    scaledCompletionSupport i j 1 = 46656 * (-16 - 32 * (walshSigns i j).re) ∧
    scaledCompletionSupport i j (-1) = 46656 * (-16 + 32 * (walshSigns i j).re) ∧
    scaledCompletionSupport i j gaussI = -746496 ∧
    scaledCompletionSupport i j (-gaussI) = -746496 := by
  fin_cases i <;> fin_cases j <;>
    simp only [scaledCompletionSupport, scaledSupport, Matrix.det_fin_three] <;> decide +kernel

private theorem completion_four_phases (i j : Fin 4) :
    (completionSupport i j 1).re = -16 - 64 * (walsh i j).re ∧
    (completionSupport i j (-1)).re = -16 + 64 * (walsh i j).re ∧
    (completionSupport i j Complex.I).re = -16 ∧
    (completionSupport i j (-Complex.I)).re = -16 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := completion_four_phases_int i j
  have hp₁ := scaledCompletionSupport_re i j 1
  have hp₂ := scaledCompletionSupport_re i j (-1)
  have hp₃ := scaledCompletionSupport_re i j gaussI
  have hp₄ := scaledCompletionSupport_re i j (-gaussI)
  rw [h₁, map_one] at hp₁
  rw [h₂, map_neg, map_one] at hp₂
  rw [h₃, gaussI_toComplex] at hp₃
  rw [h₄, map_neg, gaussI_toComplex] at hp₄
  push_cast at hp₁ hp₂ hp₃ hp₄
  rw [walsh_re]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem walsh_completion_bound (i j : Fin 4) (z : ℂ) (hz : Complex.normSq z = 1) :
    (completionSupport i j z).re ≤ 16 := by
  obtain ⟨a, b, c, d, h⟩ := completion_biaffine i j
  obtain ⟨h₁, h₂, h₃, h₄⟩ := completion_four_phases i j
  have hf := re_biaffine_circle _ a b c d h z hz
  rw [h₁, h₂, h₃, h₄] at hf
  have hnorm : ‖z‖ = 1 := by simp [Complex.norm_def, hz]
  have hre := Complex.abs_re_le_norm z
  rw [hnorm, abs_le] at hre
  have hw : (walsh i j).re = 1 / 2 ∨ (walsh i j).re = -(1 / 2) := by
    rcases walshSigns_cases i j with h | h <;> norm_num [walsh_re, h]
  rcases hw with hw | hw <;> rw [hw] at hf <;> nlinarith [hre.1, hre.2]

theorem walsh_original_support :
    (Complex.I * determinantValue walshLeft walshRight walsh).re = 24 := by
  have hv : walshSigns.map gauss = (2 : ℂ) • walsh := by
    rw [walsh, smul_smul]
    norm_num
  have hc : scaledSupport walshLeftInt walshRightInt 2 walshSigns gaussI = 6144 := by
    unfold scaledSupport
    rw [Matrix.det_succ_row_zero]
    simp only [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.sum_univ_zero]
    decide +kernel
  have hs := scaledSupport_re walshLeftInt walshRightInt 2 walshSigns gaussI walsh hv
  rw [hc, gaussI_toComplex] at hs
  norm_num only [Nat.cast_ofNat, Int.cast_ofNat] at hs
  change (6144 : ℝ) = 256 * (Complex.I * determinantValue walshLeft walshRight walsh).re at hs
  linarith [hs]

end

end MOC
