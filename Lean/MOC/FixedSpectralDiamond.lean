import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! A fixed first spectrum separates the four simultaneous evaluations at a
minor diamond from every common nonnegative matching law. -/

open BigOperators Matrix

namespace MOC

private def diamondRatio : Fin 4 → GaussianInt :=
  ![⟨2, -2⟩, ⟨-5, 1⟩, ⟨7, 2⟩, ⟨-7, 2⟩]

private def diamondVertexAt (i j k : Fin 4) : Fin 4 → GaussianInt :=
  ![diamondRatio i, diamondRatio i * diamondRatio j, diamondRatio i * diamondRatio k,
    diamondRatio i * diamondRatio j * diamondRatio k]

private def diamondVertex (σ : Equiv.Perm (Fin 4)) : Fin 4 → GaussianInt :=
  diamondVertexAt (σ 0) (σ 1) (σ 3)

private def diamondDirection : Fin 4 → GaussianInt :=
  ![⟨-2469, 12235⟩, ⟨-632, 1815⟩, ⟨-930, 2181⟩, ⟨-206, 252⟩]

private def diamondRotation : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![-37, 16, 20, -24; -8, -31, -26, -30; -12, 30, -39, 6; 32, 22, 2, -33]

private def diamondMask : Fin 4 → Fin 4 → GaussianInt :=
  ![![1,0,0,0], ![1,1,0,0], ![1,0,0,1], ![1,1,0,1]]

private def diamondMatrix (l : Fin 4) : Matrix (Fin 4) (Fin 4) GaussianInt :=
  (2601 : GaussianInt) • 1 + diagonal (fun i => diamondRatio i - 1) *
    diamondRotation * diagonal (diamondMask l) * diamondRotationᵀ

private def diamondNumerator : Fin 4 → GaussianInt :=
  ![⟨-3742, -338⟩, ⟨-33336, 11644⟩, ⟨-210, 20282⟩, ⟨82696, -101372⟩]

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 4000 in
private theorem diamondMatrix_det (l : Fin 4) :
    (diamondMatrix l).det = (2601 : GaussianInt) ^ 3 * diamondNumerator l := by
  rw [Matrix.det_succ_column_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_four]
  fin_cases l <;> decide +kernel

private theorem diamond_vertex_lower (i j k : Fin 4)
    (hij : i ≠ j ∨ i = 1) (hik : i ≠ k ∨ i = 1) (hjk : j ≠ k ∨ j = 1) :
    -8542 ≤ ∑ l, (diamondDirection l * diamondVertexAt i j k l).re := by
  have h : ∀ i j k : Fin 4, (i ≠ j ∨ i = 1) → (i ≠ k ∨ i = 1) → (j ≠ k ∨ j = 1) →
      -8542 ≤ ∑ l, (diamondDirection l * diamondVertexAt i j k l).re := by
    decide +kernel
  exact h i j k hij hik hjk

private theorem diamond_numerator_score :
    (∑ l, (diamondDirection l * diamondNumerator l).re) = -22220454 := by
  simp only [Fin.sum_univ_four]
  decide +kernel

/-- The four normalized corner determinants fail to share a probability
law even when the matching ratio `−5+i` is allowed to repeat. -/
theorem no_fixed_spectral_diamond_law_with_repeated_ratio {κ : Type*} [Fintype κ]
    (i j k : κ → Fin 4) (hij : ∀ σ, i σ ≠ j σ ∨ i σ = 1)
    (hik : ∀ σ, i σ ≠ k σ ∨ i σ = 1) (hjk : ∀ σ, j σ ≠ k σ ∨ j σ = 1) :
    ¬ ∃ w : κ → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧ ∀ l,
      (∑ σ, (w σ : ℂ) * GaussianInt.toComplex (diamondVertexAt (i σ) (j σ) (k σ) l)) =
        GaussianInt.toComplex (diamondMatrix l).det / (2601 : ℂ)^4 := by
  classical
  rintro ⟨w, hw, hs, he⟩
  let g := GaussianInt.toComplex
  let V (σ : κ) := diamondVertexAt (i σ) (j σ) (k σ)
  have hn (l : Fin 4) : g (diamondMatrix l).det / (2601 : ℂ)^4 = g (diamondNumerator l) / 2601 := by
    rw [diamondMatrix_det, map_mul, map_pow, map_ofNat]
    field_simp <;> ring
  have hcorner (l : Fin 4) :
      (∑ σ, w σ * ((diamondDirection l * V σ l).re : ℝ)) =
        ((diamondDirection l * diamondNumerator l).re : ℝ) / 2601 := by
    have h := congrArg (fun z : ℂ => (g (diamondDirection l) * z).re) ((he l).trans (hn l))
    change (g (diamondDirection l) * (∑ σ, (w σ : ℂ) * g (V σ l))).re =
      (g (diamondDirection l) * (g (diamondNumerator l) / 2601)).re at h
    rw [Finset.mul_sum, Complex.re_sum, ← mul_div_assoc, ← map_mul] at h
    have ht (σ : κ) :
        (g (diamondDirection l) * ((w σ : ℂ) * g (V σ l))).re =
          w σ * ((diamondDirection l * V σ l).re : ℝ) := by
      rw [mul_left_comm, Complex.re_ofReal_mul, ← map_mul, ← GaussianInt.to_real_re]
    simp_rw [ht] at h
    rw [show (2601 : ℂ) = ((2601 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re,
      ← GaussianInt.to_real_re] at h
    exact h
  have hlow : (-8542 : ℝ) ≤ ∑ σ, w σ * (∑ l, ((diamondDirection l * V σ l).re : ℝ)) := by
    calc
      _ = ∑ σ, w σ * (-8542 : ℝ) := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left
        (by exact_mod_cast diamond_vertex_lower (i σ) (j σ) (k σ) (hij σ) (hik σ) (hjk σ)) (hw σ))
  simp_rw [Finset.mul_sum] at hlow
  rw [Finset.sum_comm] at hlow
  simp_rw [hcorner, ← Finset.sum_div, ← Int.cast_sum, diamond_numerator_score] at hlow
  norm_num at hlow

/-- The four fixed spectral corners for the original four-dimensional rotation. -/
theorem no_fixed_spectral_diamond_law :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ) = 1 ∧ ∀ l,
      (∑ σ, (w σ : ℂ) * GaussianInt.toComplex (diamondVertex σ l)) =
        GaussianInt.toComplex (diamondMatrix l).det / (2601 : ℂ)^4 := by
  exact no_fixed_spectral_diamond_law_with_repeated_ratio (κ := Equiv.Perm (Fin 4))
    (fun σ => σ 0) (fun σ => σ 1) (fun σ => σ 3)
    (fun σ => Or.inl (fun e => (by decide : (0 : Fin 4) ≠ 1) (σ.injective e)))
    (fun σ => Or.inl (fun e => (by decide : (0 : Fin 4) ≠ 3) (σ.injective e)))
    (fun σ => Or.inl (fun e => (by decide : (1 : Fin 4) ≠ 3) (σ.injective e)))

end MOC
