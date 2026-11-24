import MOC.Core
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.LinearCombination

/-! A genuine proper zero-height face can consist of an entire
fixed-assignment fibre with simple, all-nonzero data. Two imaginary
outlier eigenvalues and positive real spectators give an explicit family. -/

open BigOperators Matrix

namespace MOC
noncomputable section

/-- The plane computation in the positive two-outlier zero-height
certificate. In the two-dimensional span of the outlier eigenvectors,
their orthogonal rank-one projections have coordinates for `(1,0)` and
`(c,s)`. The real part depends on their squared angle, not on the
off-diagonal phase of the Hermitian matrix. -/
theorem re_det_two_outlier_plane (x y c s α β : ℝ) (z : ℂ) :
    (!![(x : ℂ) + Complex.I * (α + β * c^2),
       z + Complex.I * (β * c * s);
       star z + Complex.I * (β * c * s),
       (y : ℂ) + Complex.I * (β * s^2)] : Matrix (Fin 2) (Fin 2) ℂ).det.re =
      x * y - Complex.normSq z - α * β * s^2 := by
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.vecCons, Fin.cons_zero, Fin.cons_one, ← Complex.ofReal_pow,
    Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.normSq_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
    zero_mul, mul_zero, one_mul, zero_add, add_zero, sub_zero]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Replace exactly one diagonal spectral value by a pure imaginary
outlier. The real vector is used only at the remaining labels. -/
def withImaginaryOutlier (x : ι → ℝ) (j : ι) (u : ℝ) : ι → ℂ :=
  Function.update (fun i => (x i : ℂ)) j (Complex.I * u)

/-- When both outliers are matched together, the product is purely
imaginary. Otherwise its real part has the sign of the corresponding
product of spectator entries minus the product of outlier heights. -/
theorem matchingProduct_two_outliers_real (x y : ι → ℝ) (j : ι) (u v : ℝ)
    (σ : Equiv.Perm ι) :
    (matchingProduct (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) σ).re =
      if σ j = j then 0
      else (x (σ j) * y (σ.symm j) - u * v) *
        ∏ t ∈ (Finset.univ.erase j).erase (σ.symm j), (x (σ t) + y t) := by
  let a := withImaginaryOutlier x j u
  let b := withImaginaryOutlier y j v
  let S := (Finset.univ : Finset ι).erase j
  have haj : a j = Complex.I * u := by simp [a, withImaginaryOutlier]
  have hbj : b j = Complex.I * v := by simp [b, withImaginaryOutlier]
  have ha (t : ι) (ht : t ≠ j) : a t = (x t : ℂ) := by simp [a, withImaginaryOutlier, ht]
  have hb (t : ι) (ht : t ≠ j) : b t = (y t : ℂ) := by simp [b, withImaginaryOutlier, ht]
  have hsplit : matchingProduct a b σ =
      (a (σ j) + b j) * ∏ t ∈ S, (a (σ t) + b t) := by
    unfold matchingProduct
    exact (Finset.mul_prod_erase Finset.univ (fun t => a (σ t) + b t) (Finset.mem_univ j)).symm
  change (matchingProduct a b σ).re = _
  rw [hsplit]
  by_cases hj : σ j = j
  · rw [if_pos hj, hj, haj, hbj]
    have htail : (∏ t ∈ S, (a (σ t) + b t)) =
        ((∏ t ∈ S, (x (σ t) + y t) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_prod, Complex.ofReal_add]
      apply Finset.prod_congr rfl
      intro t ht
      have ht' := (Finset.mem_erase.mp ht).1
      have he : σ t ≠ j := fun h => ht' (σ.injective (h.trans hj.symm))
      rw [ha _ he, hb _ ht']
    rw [htail]
    simp only [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.ofReal_im, zero_mul,
      mul_zero, zero_add, sub_self]
  · rw [if_neg hj]
    let k := σ.symm j
    have hk : k ≠ j := fun h => hj ((congrArg σ h).symm.trans (σ.apply_symm_apply j))
    have hsk : σ k = j := Equiv.apply_symm_apply _ _
    have hkm : k ∈ S := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩
    have htail : (∏ t ∈ S.erase k, (a (σ t) + b t)) =
        ((∏ t ∈ S.erase k, (x (σ t) + y t) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_prod, Complex.ofReal_add]
      apply Finset.prod_congr rfl
      intro t ht
      have htj := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
      have htk := (Finset.mem_erase.mp ht).1
      have he : σ t ≠ j := fun h => htk (σ.injective (h.trans hsk.symm))
      rw [ha _ he, hb _ htj]
    rw [← Finset.mul_prod_erase S _ hkm, htail, hsk, haj, hbj, ha _ hj, hb _ hk]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, one_mul,
      zero_add, add_zero, sub_zero]
    dsimp only [S, k]
    ring

/-- Realized contact stratum: if the nonoutlier sums are positive and the
imaginary heights' product exceeds every possible crossed real product,
the supporting line is exactly zero and its active labels are exactly
the matchings of the two outliers to one another. -/
theorem two_outlier_zero_contact_exact (x y : ι → ℝ) (j : ι) (u v : ℝ)
    (hplus : ∀ s t, s ≠ j → t ≠ j → 0 < x s + y t)
    (hprod : ∀ s t, s ≠ j → t ≠ j → x s * y t < u * v) :
    ∀ σ : Equiv.Perm ι,
      (matchingProduct (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) σ).re ≤ 0 ∧
      ((matchingProduct (withImaginaryOutlier x j u) (withImaginaryOutlier y j v) σ).re = 0 ↔
        σ j = j) := by
  intro σ
  rw [matchingProduct_two_outliers_real]
  by_cases h : σ j = j
  · simp [h]
  · rw [if_neg h]
    have hk : σ.symm j ≠ j := fun he => h ((congrArg σ he).symm.trans (σ.apply_symm_apply j))
    have hp : 0 < ∏ t ∈ (Finset.univ.erase j).erase (σ.symm j), (x (σ t) + y t) := by
      apply Finset.prod_pos
      intro t ht
      have ht₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
      have ht₂ := (Finset.mem_erase.mp ht).1
      exact hplus _ _ (fun he => ht₂ (σ.injective (he.trans (σ.apply_symm_apply j).symm))) ht₁
    have hg := mul_neg_of_neg_of_pos (sub_neg.mpr (hprod _ _ h hk)) hp
    exact ⟨hg.le, iff_of_false hg.ne h⟩

end
end MOC
