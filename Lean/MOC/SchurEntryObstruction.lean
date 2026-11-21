import MOC.Householder
import MOC.Weights
import Mathlib.Data.Matrix.Notation

/-! An exact order-three support maximum with strict loss along rank-one
phases that couple two specified directions. -/

open BigOperators Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A rank-one phase creates a formerly zero matrix entry with an exact
product of three squared moduli. -/
theorem rankOnePhase_entry_normSq_of_zero (U : Matrix ι ι ℂ) (v : ι → ℂ)
    (z : ℂ) (i j : ι) (hzero : U i j = 0) :
    Complex.normSq ((rankOnePhase v z * U) i j) =
      Complex.normSq (z - 1) * Complex.normSq (v i) *
        Complex.normSq (∑ k, star (v k) * U k j) := by
  have hp : (vecMulVec v (star ∘ v) * U) i j = v i * ∑ k, star (v k) * U k j := by
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Function.comp_apply, Finset.mul_sum,
      mul_assoc]
  rw [rankOnePhase, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, hzero, zero_add, hp]
  simp only [Complex.normSq_mul]
  ring

private def entryLeft (i : Fin 3) : ℂ := (i.val : ℂ)

private def entryRight : Fin 3 → ℂ :=
  ![Complex.I, 3 * Complex.I, ((-3 / 2 : ℝ) : ℂ)]

private def entryMixer : Matrix (Fin 3) (Fin 3) ℂ :=
  (!![-16 / 25, 12 / 25, 3 / 5; 12 / 25, -9 / 25, 4 / 5; 3 / 5, 4 / 5, 0] :
    Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal

private theorem entryMixer_unitary : IsUnitary entryMixer := by
  have hs (i j : Fin 3) : star (entryMixer i j) = entryMixer i j := by
    simp only [entryMixer, Matrix.map_apply, Complex.star_def, Complex.conj_ofReal]
  constructor <;> apply Matrix.ext <;> intro i j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, hs] <;>
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [entryMixer, Matrix.map_apply, Matrix.one_apply, Matrix.cons_val', Matrix.cons_val_two,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

private theorem entry_matching_real (σ : Equiv.Perm (Fin 3)) :
    (matchingProduct entryLeft entryRight σ).re =
      3 / 2 - 3 * (if σ 2 = 2 then 1 else 0 : ℝ) := by
  have him (i : Fin 3) : (entryLeft i).im = 0 := by simp [entryLeft]
  have hcoeff (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ((entryLeft i).re * (entryLeft j).re - 3) * ((entryLeft k).re - 3 / 2) =
        3 / 2 - 3 * (if k = 2 then 1 else 0 : ℝ) := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [entryLeft, Fin.ext_iff, show ((2 : Fin 3) : ℕ) = 2 from rfl] at hij hik hjk ⊢
  have hreal :
      (matchingProduct entryLeft entryRight σ).re =
        ((entryLeft (σ 0)).re * (entryLeft (σ 1)).re - 3) *
          ((entryLeft (σ 2)).re - 3 / 2) := by
    rw [matchingProduct, Fin.prod_univ_three]
    norm_num [entryRight, him, Matrix.cons_val_two, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, sub_eq_add_neg]
  rw [hreal]
  exact hcoeff (σ 0) (σ 1) (σ 2)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h))

private theorem entry_det_real (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : IsUnitary V) :
    (determinantValue entryLeft entryRight V).re = 3 / 2 - 3 * Complex.normSq (V 2 2) := by
  rw [← real_signed_determinant entryLeft entryRight V hV]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, entry_matching_real]
  have hterm (σ : Equiv.Perm (Fin 3)) :
      realSignedWeight V σ * (3 / 2 - 3 * (if σ 2 = 2 then 1 else 0 : ℝ)) =
        (3 / 2) * realSignedWeight V σ - 3 * (if σ 2 = 2 then realSignedWeight V σ else 0) := by
    by_cases h : σ 2 = 2 <;> simp [h] <;> ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_realSignedWeight V hV,
    marginal_realSignedWeight V hV, mul_one]

/-- There are order-three spectra with an attaining mixer at a support
maximum for which any nontrivial phase coupling the indicated row and
column directions strictly loses support. The support value is attained
by a matching product as well. -/
theorem exists_three_single_entry_support_maximum :
    ∃ (a b : Fin 3 → ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ),
      IsUnitary U ∧ U 2 2 = 0 ∧
      (∀ V : Matrix (Fin 3) (Fin 3) ℂ, IsUnitary V →
        (determinantValue a b V).re = 3 / 2 - 3 * Complex.normSq (V 2 2)) ∧
      (∃ σ : Equiv.Perm (Fin 3), (matchingProduct a b σ).re = 3 / 2) ∧
      ∀ (v : Fin 3 → ℂ) (z : ℂ), (∑ i, star (v i) * v i) = 1 →
        z * star z = 1 → z ≠ 1 → v 2 ≠ 0 → (∑ k, star (v k) * U k 2) ≠ 0 →
        (determinantValue a b (rankOnePhase v z * U)).re < (determinantValue a b U).re := by
  have hzero : entryMixer 2 2 = 0 := rfl
  refine ⟨entryLeft, entryRight, entryMixer, entryMixer_unitary, hzero, entry_det_real, ?_, ?_⟩
  · refine ⟨Equiv.swap 0 2, ?_⟩
    rw [entry_matching_real]
    simp [Equiv.swap_apply_right, show (0 : Fin 3) ≠ 2 by decide]
  · intro v z hv hz hz' hi hj
    let R := rankOnePhase v z
    have hR : IsUnitary R := rankOnePhase_unitary v z hv hz
    have hR' : IsUnitary Rᴴ := by
      simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hR.2 hR.1
    have hRU : IsUnitary (R * entryMixer) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        relative_unitary Rᴴ entryMixer hR' entryMixer_unitary
    rw [entry_det_real _ hRU, entry_det_real _ entryMixer_unitary, hzero, Complex.normSq_zero,
      mul_zero, sub_zero, rankOnePhase_entry_normSq_of_zero _ _ _ _ _ hzero]
    exact sub_lt_self _ (mul_pos (by norm_num) (mul_pos
      (mul_pos (Complex.normSq_pos.mpr (sub_ne_zero.mpr hz')) (Complex.normSq_pos.mpr hi))
      (Complex.normSq_pos.mpr hj)))

end

end MOC
