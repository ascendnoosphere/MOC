import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! A spectra-dependent three-frame law still cannot always preserve the
probabilities of the unordered selected row triples. -/

open BigOperators Matrix

namespace MOC

private def frameInt : Matrix (Fin 4) (Fin 3) GaussianInt :=
  !![-37, 16, 20; -8, -31, -26; -12, 30, -39; 32, 22, 2]

private def leftInt : Fin 3 → GaussianInt :=
  ![⟨-16800, 21⟩, ⟨16800, 21⟩, ⟨2100, -21⟩]

private def rightInt : Fin 4 → GaussianInt :=
  ![⟨-2100, 21⟩, ⟨-14700, -21⟩, ⟨-12600, -19⟩, ⟨16800, -21⟩]

private def directionInt : GaussianInt := ⟨1, 630⟩

private def matrixInt : Matrix (Fin 3) (Fin 3) GaussianInt :=
  (51 : GaussianInt) ^ 2 • diagonal leftInt + frameIntᴴ * diagonal rightInt * frameInt

private def supportInt : ℤ := (directionInt * matrixInt.det).re

private def massInt (j : Fin 4) : ℤ := (frameInt.submatrix j.succAbove id).det.norm

private def costInt (j : Fin 4) (σ : Equiv.Perm (Fin 3)) : ℤ :=
  (directionInt * ∏ i : Fin 3, (leftInt i + rightInt (j.succAbove (σ i)))).re

private def capInt : Fin 4 → ℤ := ![0, 56448000, 2400510470400, 4656960]

private theorem costInt_le (j : Fin 4) (σ : Equiv.Perm (Fin 3)) :
    costInt j σ ≤ capInt j := by
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h)
  simp only [costInt, Fin.prod_univ_three]
  generalize σ 0 = r at *
  generalize σ 1 = s at *
  generalize σ 2 = t at *
  fin_cases j <;> fin_cases r <;> fin_cases s <;> fin_cases t <;>
    norm_num [Fin.ext_iff] at h01 h02 h12 <;> decide +kernel

private theorem capInt_lt_supportInt :
    ∑ j : Fin 4, massInt j * capInt j < supportInt := by
  simp only [massInt, supportInt, Matrix.det_fin_three, Fin.sum_univ_four]
  decide +kernel

/-- There is an isometric three-frame and a particular pair of complex spectra
for which no nonnegative matching law with the prescribed triple masses
recovers the compressed determinant. The index `j` is the excluded row. -/
theorem no_fixed_triple_marginal_for_three_compression :
    ∃ (F : Matrix (Fin 4) (Fin 3) ℂ) (x : Fin 3 → ℂ) (y : Fin 4 → ℂ),
      Fᴴ * F = 1 ∧
      ¬ ∃ w : Fin 4 → Equiv.Perm (Fin 3) → ℝ,
        (∀ j σ, 0 ≤ w j σ) ∧
        (∀ j, ∑ σ, w j σ = Complex.normSq (F.submatrix j.succAbove id).det) ∧
        (∑ j, ∑ σ, (w j σ : ℂ) *
          ∏ i : Fin 3, (x i + y (j.succAbove (σ i)))) =
          (diagonal x + Fᴴ * diagonal y * F).det := by
  classical
  let gauss := GaussianInt.toComplex
  let G := frameInt.map gauss
  let F := (1 / 51 : ℂ) • G
  let x := gauss ∘ leftInt
  let y := gauss ∘ rightInt
  let η := gauss directionInt
  let C := diagonal x + Fᴴ * diagonal y * F
  have hmap : frameInt.map gauss = (51 : ℂ) • F := by
    simp [F, G, smul_smul] <;> norm_num
  have hstar := Matrix.conjTranspose_map (A := frameInt) gauss GaussianInt.toComplex_star
  have hGramInt : frameIntᴴ * frameInt =
      (2601 : GaussianInt) • (1 : Matrix (Fin 3) (Fin 3) GaussianInt) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have hGram : Fᴴ * F = 1 := by
    have hG := congrArg (fun M : Matrix (Fin 3) (Fin 3) GaussianInt => M.map gauss) hGramInt
    simp only [Matrix.map_mul, hstar, Matrix.map_smul' gauss _ _ (map_mul gauss), map_ofNat,
      Matrix.map_one gauss (map_zero gauss) (map_one gauss)] at hG
    simp only [F, Matrix.conjTranspose_smul, star_div₀, star_one, star_ofNat, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, G, hG]
    norm_num
  have hC : matrixInt.map gauss = (51 : ℂ) ^ 2 • C := by
    change matrixInt.map gauss = (51 : ℂ) ^ 2 •
      (diagonal (fun i => gauss (leftInt i)) + Fᴴ * diagonal (fun i => gauss (rightInt i)) * F)
    simp only [matrixInt, Matrix.map_add gauss (map_add gauss),
      Matrix.map_smul' gauss _ _ (map_mul gauss), map_pow, map_mul, map_ofNat, Matrix.map_mul,
      Matrix.diagonal_map (map_zero gauss), hstar, hmap, Matrix.conjTranspose_smul,
      star_ofNat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two, smul_add]
  have hsupport : (supportInt : ℝ) = (51 : ℝ) ^ 6 * (η * C.det).re := by
    have hreal : (51 : ℂ) ^ 6 = (((51 : ℝ) ^ 6 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow] <;> norm_num
    rw [supportInt, GaussianInt.to_real_re]
    change (gauss (directionInt * matrixInt.det)).re = _
    rw [map_mul, RingHom.map_det, RingHom.mapMatrix_apply, hC, Matrix.det_smul, Fintype.card_fin,
      ← pow_mul, show 2 * 3 = 6 from rfl, hreal, mul_left_comm, Complex.re_ofReal_mul]
  have hmass (j : Fin 4) : (massInt j : ℝ) =
      (51 : ℝ) ^ 6 * Complex.normSq (F.submatrix j.succAbove id).det := by
    have hm : (frameInt.submatrix j.succAbove id).map gauss =
        (51 : ℂ) • F.submatrix j.succAbove id := by
      ext i l
      exact congrArg (fun A : Matrix (Fin 4) (Fin 3) ℂ => A (j.succAbove i) l) hmap
    rw [massInt, GaussianInt.intCast_real_norm]
    change Complex.normSq (gauss (frameInt.submatrix j.succAbove id).det) = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_smul, Fintype.card_fin,
      Complex.normSq_mul, map_pow]
    norm_num
  let v (j : Fin 4) (σ : Equiv.Perm (Fin 3)) :=
    ∏ i : Fin 3, (x i + y (j.succAbove (σ i)))
  have hv (j : Fin 4) (σ : Equiv.Perm (Fin 3)) : (η * v j σ).re ≤ (capInt j : ℝ) := by
    have hv' : (η * v j σ).re = (costInt j σ : ℝ) := by
      rw [costInt, GaussianInt.to_real_re]
      simp only [η, v, x, y, gauss, Function.comp_apply, map_mul, map_prod, map_add]
    rw [hv']
    exact_mod_cast costInt_le j σ
  refine ⟨F, x, y, hGram, ?_⟩
  rintro ⟨w, hw, hm, he⟩
  change (∑ j, ∑ σ, (w j σ : ℂ) * v j σ) = C.det at he
  have hterm (a : ℝ) (z : ℂ) : (η * ((a : ℂ) * z)).re = a * (η * z).re := by
    rw [← mul_assoc, mul_comm η, mul_assoc, Complex.re_ofReal_mul]
  have hvalue : (η * C.det).re ≤
      ∑ j : Fin 4, Complex.normSq (F.submatrix j.succAbove id).det * (capInt j : ℝ) := by
    rw [← he, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← hm j, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_le_sum
    intro σ _
    rw [hterm]
    exact mul_le_mul_of_nonneg_left (hv j σ) (hw j σ)
  have hvalue' := mul_le_mul_of_nonneg_left hvalue (show (0 : ℝ) ≤ (51 : ℝ) ^ 6 by norm_num)
  simp only [← hsupport, Finset.mul_sum, ← mul_assoc, ← hmass, ← Int.cast_mul,
    ← Int.cast_sum] at hvalue'
  have hbound : supportInt ≤ ∑ j : Fin 4, massInt j * capInt j := by exact_mod_cast hvalue'
  exact (not_lt_of_ge hbound) capInt_lt_supportInt

end MOC
