import MOC.Core
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A real support direction can have a global maximum at a fully supported
mixer even when the relative product satisfies no quadratic relation. -/

open Matrix

namespace MOC

noncomputable section

private def exampleA : Fin 3 → ℂ := ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]

private def exampleB : Fin 3 → ℂ :=
  ![⟨3 / 5, 4 / 5⟩, ⟨-3 / 5, 4 / 5⟩, ⟨-7 / 25, 24 / 25⟩]

private def exampleU : Matrix (Fin 3) (Fin 3) ℂ :=
  (!![1 / 3, -2 / 3, -2 / 3; -2 / 3, 1 / 3, -2 / 3; -2 / 3, -2 / 3, 1 / 3] :
    Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal

private def exampleDirection : ℂ := ⟨3, -4⟩

private theorem exampleU_entry_star (i j : Fin 3) : star (exampleU i j) = exampleU i j := by
  simp only [exampleU, Matrix.map_apply, Complex.star_def, Complex.conj_ofReal]

private theorem exampleU_unitary : IsUnitary exampleU := by
  constructor <;> apply Matrix.ext <;> intro i j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      exampleU_entry_star] <;>
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [exampleU, Matrix.map_apply, Matrix.one_apply, Matrix.cons_val', Matrix.cons_val_two,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

private theorem unitary_of_unit_entries (d : Fin 3 → ℂ)
    (hd : ∀ i, Complex.normSq (d i) = 1) : IsUnitary (diagonal d) := by
  have h (i : Fin 3) : d i * star (d i) = 1 := by
    simp only [Complex.star_def, Complex.mul_conj, hd, Complex.ofReal_one]
  have h' (i : Fin 3) : star (d i) * d i = 1 := (mul_comm _ _).trans (h i)
  constructor <;> rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  · simp only [Pi.star_apply, h, Matrix.diagonal_one]
  · simp only [Pi.star_apply, h', Matrix.diagonal_one]

private theorem exampleA_unitary : IsUnitary (diagonal exampleA) := by
  apply unitary_of_unit_entries
  intro i
  fin_cases i <;> norm_num [exampleA, Complex.normSq_apply]

private theorem exampleB_unitary : IsUnitary (diagonal exampleB) := by
  apply unitary_of_unit_entries
  intro i
  fin_cases i <;> norm_num [exampleB, Complex.normSq_apply]

private theorem example_support_zero (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : IsUnitary V) :
    (exampleDirection * determinantValue exampleA exampleB V).re = 0 := by
  let A := diagonal exampleA
  let D := diagonal exampleB
  let W := V * D * Vᴴ
  let C := A + W
  have hA : Aᴴ * A = 1 := exampleA_unitary.2
  have hD : D * Dᴴ = 1 := exampleB_unitary.1
  have hW : W * Wᴴ = 1 := by
    calc
      _ = V * (D * ((Vᴴ * V) * (Dᴴ * Vᴴ))) := by
        simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by rw [hV.2, Matrix.one_mul, ← Matrix.mul_assoc D Dᴴ, hD,
        Matrix.one_mul, hV.1]
  have hC : Cᴴ = Aᴴ * C * Wᴴ := by
    simp only [C, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
    rw [hA, Matrix.one_mul, Matrix.mul_assoc Aᴴ W Wᴴ, hW, Matrix.mul_one, add_comm]
  have hdA : A.det = 1 := by
    apply Complex.ext <;>
      norm_num [A, Matrix.det_diagonal, Fin.prod_univ_three, exampleA,
        Matrix.cons_val_two, Complex.mul_re, Complex.mul_im]
  have hdD : D.det = (⟨7 / 25, -24 / 25⟩ : ℂ) := by
    apply Complex.ext <;>
      norm_num [D, Matrix.det_diagonal, Fin.prod_univ_three, exampleB,
        Matrix.cons_val_two, Complex.mul_re, Complex.mul_im]
  have hdW : W.det = D.det := det_unitary_conjugation V D hV
  have hdet : star C.det = star A.det * C.det * star W.det := by
    rw [← Matrix.det_conjTranspose, hC, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_conjTranspose, Matrix.det_conjTranspose]
  rw [hdA, hdW, hdD, star_one, one_mul] at hdet
  have hre := congrArg Complex.re hdet
  norm_num [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re] at hre
  change (exampleDirection * C.det).re = 0
  norm_num [exampleDirection, Complex.mul_re] <;> linarith only [hre]

private def exampleOrbitB : Matrix (Fin 3) (Fin 3) ℂ :=
  !![⟨-73 / 225, 196 / 225⟩, ⟨-28 / 225, 16 / 225⟩, ⟨-76 / 225, -8 / 225⟩;
     ⟨-28 / 225, 16 / 225⟩, ⟨17 / 225, 196 / 225⟩, ⟨104 / 225, -8 / 225⟩;
     ⟨-76 / 225, -8 / 225⟩, ⟨104 / 225, -8 / 225⟩, ⟨-7 / 225, 184 / 225⟩]

private theorem exampleOrbitB_eq : exampleU * diagonal exampleB * exampleUᴴ = exampleOrbitB := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply (M := exampleU * diagonal exampleB), Matrix.mul_diagonal,
    Fin.sum_univ_three, Matrix.conjTranspose_apply, exampleU_entry_star]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [exampleU, exampleB, exampleOrbitB, Matrix.map_apply, Matrix.cons_val',
      Matrix.cons_val_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

private theorem example_det_ne_zero : determinantValue exampleA exampleB exampleU ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [determinantValue, exampleOrbitB_eq, exampleOrbitB, exampleA, Matrix.det_fin_three,
    Matrix.add_apply, Matrix.diagonal_apply, Matrix.cons_val', Matrix.cons_val_two,
    h02, h02.symm, h12, h12.symm, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] at hre

private def exampleRelative : Matrix (Fin 3) (Fin 3) ℂ :=
  !![⟨-73 / 225, 196 / 225⟩, ⟨16 / 225, 28 / 225⟩, ⟨8 / 225, -76 / 225⟩;
     ⟨-28 / 225, 16 / 225⟩, ⟨196 / 225, -17 / 225⟩, ⟨8 / 225, 104 / 225⟩;
     ⟨-76 / 225, -8 / 225⟩, ⟨-8 / 225, -104 / 225⟩, ⟨-184 / 225, -7 / 225⟩]

private theorem exampleRelative_eq :
    (exampleU * diagonal exampleB * exampleUᴴ) * (diagonal exampleA)⁻¹ = exampleRelative := by
  rw [exampleOrbitB_eq, Matrix.inv_eq_right_inv exampleA_unitary.1, Matrix.diagonal_conjTranspose]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_diagonal, Pi.star_apply]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [exampleRelative, exampleOrbitB, exampleA, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_re, Complex.mul_im]

private theorem example_no_quadratic (p q r : ℂ)
    (h : p • (exampleRelative * exampleRelative) + q • exampleRelative +
      r • (1 : Matrix (Fin 3) (Fin 3) ℂ) = 0) : p = 0 ∧ q = 0 ∧ r = 0 := by
  let X := exampleRelative
  change p • (X * X) + q • X + r • (1 : Matrix (Fin 3) (Fin 3) ℂ) = 0 at h
  have hminor : (X * X) 0 1 * X 0 2 - (X * X) 0 2 * X 0 1 ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num [X, exampleRelative, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val',
      Matrix.cons_val_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.mul_re,
      Complex.mul_im] at hre
  have hx : X 0 1 ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num [X, exampleRelative] at hre
  have he (j : Fin 3) (hj : (0 : Fin 3) ≠ j) : p * (X * X) 0 j + q * X 0 j = 0 := by
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne hj,
      mul_zero, add_zero, Matrix.zero_apply] using
      congrArg (fun Y : Matrix (Fin 3) (Fin 3) ℂ => Y 0 j) h
  have he₁ := he 1 (by decide)
  have he₂ := he 2 (by decide)
  have hp : p = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hminor
    calc
      _ = (p * (X * X) 0 1 + q * X 0 1) * X 0 2 -
          (p * (X * X) 0 2 + q * X 0 2) * X 0 1 := by ring
      _ = 0 := by simp only [he₁, he₂, zero_mul, sub_self]
  have hq : q = 0 := by
    rw [hp, zero_mul, zero_add] at he₁
    exact (mul_eq_zero.mp he₁).resolve_right hx
  refine ⟨hp, hq, ?_⟩
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hp, hq, zero_mul, zero_add,
    Matrix.one_apply_eq, mul_one, Matrix.zero_apply] using
    congrArg (fun Y : Matrix (Fin 3) (Fin 3) ℂ => Y 0 0) h

/-- Simple spectra and a fully supported directional maximizer do not imply
a quadratic relation for the relative product. The support direction is
constant on this orbit, and the determinant at the witness is nonzero. -/
theorem exists_directional_maximizer_without_relative_quadratic :
    ∃ (a b : Fin 3 → ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) (η : ℂ),
      Function.Injective a ∧ Function.Injective b ∧ IsUnitary U ∧
      (∀ i j, U i j ≠ 0) ∧ (∀ i j, a i + b j ≠ 0) ∧ η ≠ 0 ∧
      determinantValue a b U ≠ 0 ∧
      (∀ V : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary V → (η * determinantValue a b V).re = 0) ∧
      let X := (U * diagonal b * Uᴴ) * (diagonal a)⁻¹
      ∀ p q r : ℂ, p • (X * X) + q • X + r • (1 : Matrix (Fin 3) (Fin 3) ℂ) = 0 →
        p = 0 ∧ q = 0 ∧ r = 0 := by
  refine ⟨exampleA, exampleB, exampleU, exampleDirection, ?_, ?_, exampleU_unitary,
    ?_, ?_, ?_, example_det_ne_zero, example_support_zero, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      norm_num [exampleA] at hre him
  · intro i j h
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      have hre := congrArg Complex.re h
      norm_num [exampleB] at hre
  · intro i j h
    have hre := congrArg Complex.re h
    fin_cases i <;> fin_cases j <;> norm_num [exampleU, Matrix.map_apply] at hre
  · intro i j h
    have hre := congrArg Complex.re h
    fin_cases i <;> fin_cases j <;> norm_num [exampleA, exampleB, Complex.add_re] at hre
  · intro h
    have hre := congrArg Complex.re h
    norm_num [exampleDirection] at hre
  · dsimp only
    rw [exampleRelative_eq]
    exact example_no_quadratic

end

end MOC
