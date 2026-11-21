import MOC.Core
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Reflection at an invariant subspace of a possibly nonnormal sum. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]

private def energy {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

private theorem energy_eq_trace {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    energy A = (A * Aᴴ).trace.re := by
  simp only [energy, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

omit [DecidableEq κ] [DecidableEq ι] in
private theorem energy_fromBlocks (X : Matrix κ κ ℂ) (P : Matrix κ ι ℂ)
    (Q : Matrix ι κ ℂ) (Y : Matrix ι ι ℂ) :
    energy (fromBlocks X P Q Y) = energy X + energy P + energy Q + energy Y := by
  simp only [energy, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Finset.sum_add_distrib]
  ring

omit [DecidableEq κ] [DecidableEq ι] in
private theorem off_diagonal_energy_eq (X : Matrix κ κ ℂ) (P : Matrix κ ι ℂ)
    (Q : Matrix ι κ ℂ) (Y : Matrix ι ι ℂ)
    (h : let M := fromBlocks X P Q Y; M * Mᴴ = Mᴴ * M) : energy P = energy Q := by
  dsimp only at h
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  have he := congrArg (fun M : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ => M.toBlocks₁₁.trace.re) h
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.trace_add, Complex.add_re,
    Matrix.trace_mul_comm Xᴴ X, Matrix.trace_mul_comm Qᴴ Q] at he
  simpa only [← energy_eq_trace] using add_left_cancel he

private theorem schur_reflection_isUnitary :
    IsUnitary (fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ)) := by
  constructor <;>
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

private theorem schur_reflection_blocks (X A : Matrix κ κ ℂ) (D B : Matrix ι ι ℂ)
    (R P : Matrix κ ι ℂ) (Q : Matrix ι κ ℂ) :
    let C := fromBlocks X R 0 D
    let S := fromBlocks A P Q B
    let J := fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ)
    C - S + J * S * Jᴴ = fromBlocks X (R - (2 : ℂ) • P) (-((2 : ℂ) • Q)) D := by
  dsimp only
  have hconj : (fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ))ᴴ =
      fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ) := by
    rw [Matrix.fromBlocks_conjTranspose]
    simp
  have href : fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ) * fromBlocks A P Q B *
      fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ) = fromBlocks A (-P) (-Q) B := by
    simp [Matrix.fromBlocks_multiply, Matrix.neg_mul, Matrix.mul_neg]
  rw [hconj, href]
  ext i j : 1
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.zero_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      two_smul, sub_add_cancel, zero_sub] <;> abel

/-- Reflection across any invariant subspace of a sum of two normal matrices
raises its squared Frobenius norm by twice the squared changed upper block. -/
theorem schur_reflection_energy (X A : Matrix κ κ ℂ) (D B : Matrix ι ι ℂ)
    (R P : Matrix κ ι ℂ) (Q : Matrix ι κ ℂ)
    (hA : let M := fromBlocks (X - A) (R - P) (-Q) (D - B); M * Mᴴ = Mᴴ * M)
    (hB : let M := fromBlocks A P Q B; M * Mᴴ = Mᴴ * M) :
    let C := fromBlocks X R 0 D
    let S := fromBlocks A P Q B
    let J := fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ)
    (∑ i, ∑ j, Complex.normSq ((C - S + J * S * Jᴴ) i j)) =
      (∑ i, ∑ j, Complex.normSq (C i j)) + 2 * ∑ i, ∑ j, Complex.normSq ((R - (2 : ℂ) • P) i j) := by
  change energy _ = energy _ + 2 * energy _
  rw [schur_reflection_blocks X A D B R P Q, energy_fromBlocks, energy_fromBlocks]
  have hp := off_diagonal_energy_eq A P Q B hB
  have hr := off_diagonal_energy_eq (X - A) (R - P) (-Q) (D - B) hA
  have hneg : energy (-Q) = energy Q := by
    simp only [energy, Matrix.neg_apply, Complex.normSq_neg]
  rw [hneg] at hr
  have hzero : energy (0 : Matrix ι κ ℂ) = 0 := by simp [energy]
  have hscale : energy (-((2 : ℂ) • Q)) = 4 * energy Q := by
    have htwo : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
    simp only [energy, Matrix.neg_apply, Complex.normSq_neg, Matrix.smul_apply,
      smul_eq_mul, Complex.normSq_mul, htwo, Finset.mul_sum]
  have hterm (i : κ) (j : ι) : Complex.normSq ((R - (2 : ℂ) • P) i j) + Complex.normSq (R i j) =
      2 * (Complex.normSq ((R - P) i j) + Complex.normSq (P i j)) := by
    simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] <;> ring
  have hpar := congrArg (fun f : κ → ι → ℝ => ∑ i, ∑ j, f i j) (funext fun i => funext (hterm i))
  have hpar' : energy (R - (2 : ℂ) • P) + energy R =
      2 * (energy (R - P) + energy P) := by
    simpa only [energy, Finset.sum_add_distrib, Finset.mul_sum] using hpar
  rw [hzero, hscale]
  linarith only [hp, hr, hpar']

/-- Schur complement evaluates the determinant after the same reflection. -/
theorem schur_reflection_det (X A : Matrix κ κ ℂ) (D B : Matrix ι ι ℂ)
    (R P : Matrix κ ι ℂ) (Q : Matrix ι κ ℂ) (hD : IsUnit D.det) :
    let C := fromBlocks X R 0 D
    let S := fromBlocks A P Q B
    let J := fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ)
    (C - S + J * S * Jᴴ).det = D.det * (X + (2 : ℂ) • ((R - (2 : ℂ) • P) * D⁻¹ * Q)).det := by
  letI : Invertible D := D.invertibleOfIsUnitDet hD
  dsimp only
  rw [schur_reflection_blocks X A D B R P Q, Matrix.det_fromBlocks₂₂,
    Matrix.invOf_eq_nonsing_inv, Matrix.mul_neg, Matrix.mul_smul, sub_neg_eq_add]

/-- At a support maximum with Frobenius tie-breaking, a Schur reflection that
changes the upper coupling must strictly decrease the determinant support. -/
theorem schur_reflection_strict_at_support_energy_max (X A : Matrix κ κ ℂ) (D B : Matrix ι ι ℂ)
    (R P : Matrix κ ι ℂ) (Q : Matrix ι κ ℂ) (η : ℂ) (hD : IsUnit D.det)
    (hA : let M := fromBlocks (X - A) (R - P) (-Q) (D - B); M * Mᴴ = Mᴴ * M)
    (hB : let M := fromBlocks A P Q B; M * Mᴴ = Mᴴ * M)
    (hne : R ≠ (2 : ℂ) • P)
    (hmax : let C := fromBlocks X R 0 D; let S := fromBlocks A P Q B
      ∀ V : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ, IsUnitary V →
        (η * (C - S + V * S * Vᴴ).det).re ≤ (η * C.det).re)
    (htie : let C := fromBlocks X R 0 D; let S := fromBlocks A P Q B
      ∀ V : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ, IsUnitary V →
        (η * (C - S + V * S * Vᴴ).det).re = (η * C.det).re →
        (∑ i, ∑ j, Complex.normSq ((C - S + V * S * Vᴴ) i j)) ≤ ∑ i, ∑ j, Complex.normSq (C i j)) :
    (η * (D.det * (X + (2 : ℂ) • ((R - (2 : ℂ) • P) * D⁻¹ * Q)).det)).re <
      (η * (X.det * D.det)).re := by
  let J := fromBlocks (-1 : Matrix κ κ ℂ) 0 0 (1 : Matrix ι ι ℂ)
  have hJ : IsUnitary J := schur_reflection_isUnitary
  have hd := schur_reflection_det X A D B R P Q hD
  have he := schur_reflection_energy X A D B R P Q hA hB
  dsimp only at hmax htie hd he
  rw [← hd, ← Matrix.det_fromBlocks_zero₂₁ X R D]
  refine lt_of_le_of_ne (hmax J hJ) fun h => hne (sub_eq_zero.mp ?_)
  have ht := htie J hJ h
  have hn : 0 ≤ energy (R - (2 : ℂ) • P) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hz : energy (R - (2 : ℂ) • P) = 0 := by
    dsimp only [J] at ht
    change energy _ = energy _ + 2 * energy _ at he
    change energy _ ≤ energy _ at ht
    linarith only [he, ht, hn]
  ext i j : 1
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    Finset.sum_nonneg (fun l _ => Complex.normSq_nonneg ((R - (2 : ℂ) • P) k l)))).mp
    hz i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
    Complex.normSq_nonneg ((R - (2 : ℂ) • P) i l))).mp hi j (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp hj

end

end MOC
