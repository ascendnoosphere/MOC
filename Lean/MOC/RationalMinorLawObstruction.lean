import MOC.FiniteMinorLaw
import MOC.SubsetMarkerTest
import MOC.UniversalMatchingWeights
import MOC.UniversalWeightsBlockRestriction
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! The four-event rational obstruction to a spectrum-independent law. -/

open Matrix Finset

namespace MOC

private def rationalMinorMixerNumerator : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![-11, 22, -4, -2; -10, -5, 10, -20; -20, -10, -5, 10; 2, -4, -22, -11]

noncomputable section

/-- The rational orthogonal matrix with a strict four-event marginal gap. -/
def rationalMinorMixer : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 25 : ℂ) • rationalMinorMixerNumerator.map GaussianInt.toComplex

theorem rationalMinorMixer_unitary : IsUnitary rationalMinorMixer := by
  let g := GaussianInt.toComplex
  have hg : rationalMinorMixerNumerator * rationalMinorMixerNumeratorᴴ =
      (625 : GaussianInt) • (1 : Matrix (Fin 4) (Fin 4) GaussianInt) := by
    ext i j
    revert i j
    decide +kernel
  have hG := congrArg (fun M : Matrix (Fin 4) (Fin 4) GaussianInt => M.map g) hg
  have hstar := Matrix.conjTranspose_map (A := rationalMinorMixerNumerator) g GaussianInt.toComplex_star
  simp only [Matrix.map_mul, hstar, Matrix.map_smul' g _ _ (map_mul g), map_ofNat,
    Matrix.map_one g (map_zero g) (map_one g)] at hG
  have h : rationalMinorMixer * rationalMinorMixerᴴ = 1 := by
    simp only [rationalMinorMixer, Matrix.conjTranspose_smul, star_div₀, star_one, star_ofNat,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hG]
    norm_num [smul_smul]
  exact ⟨h, Matrix.mul_eq_one_comm.mp h⟩

theorem rationalMinorMixer_det : rationalMinorMixer.det = 1 := by
  have h : rationalMinorMixerNumerator.det = 390625 := by
    rw [Matrix.det_succ_column_zero]
    simp only [Matrix.det_fin_three, Fin.sum_univ_four]
    decide +kernel
  rw [rationalMinorMixer, Matrix.det_smul, ← RingHom.mapMatrix_apply,
    ← GaussianInt.toComplex.map_det, h, map_ofNat]
  norm_num

private theorem rationalMinorMixer_four_masses :
    subsetMinorSq rationalMinorMixer {0, 3} {0, 2} = 4 / 25 ∧
    subsetMinorSq rationalMinorMixer {1} {1} = 1 / 25 ∧
    subsetMinorSq rationalMinorMixer {3} {0} = 4 / 625 ∧
    subsetMinorSq rationalMinorMixer {0, 1} {0, 3} = 64 / 625 := by
  rw [subsetMinorSq_pair _ rationalMinorMixer_unitary (by decide) (by decide),
    subsetMinorSq_singleton _ rationalMinorMixer_unitary,
    subsetMinorSq_singleton _ rationalMinorMixer_unitary,
    subsetMinorSq_pair _ rationalMinorMixer_unitary (by decide) (by decide)]
  norm_num [rationalMinorMixer, rationalMinorMixerNumerator, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.normSq_apply, map_neg, map_ofNat,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.normSq]

/-- The rational mixer violates the union bound by `7/625`. -/
theorem rationalMinorMixer_no_common_minor_law :
    ¬ ∃ w : Equiv.Perm (Fin 4) → ℝ, (∀ σ, 0 ≤ w σ) ∧
      ∀ I J : Finset (Fin 4),
        (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 4) => J.map σ.toEmbedding = I), w σ) =
          subsetMinorSq rationalMinorMixer I J := by
  classical
  rintro ⟨w, hw, hm⟩
  have hInc : ∀ σ : Equiv.Perm (Fin 4), ({0, 2} : Finset (Fin 4)).map σ.toEmbedding = {0, 3} →
      ({1} : Finset (Fin 4)).map σ.toEmbedding = {1} ∨
      ({0} : Finset (Fin 4)).map σ.toEmbedding = {3} ∨
      ({0, 3} : Finset (Fin 4)).map σ.toEmbedding = {0, 1} := by
    decide +kernel
  let A := fun σ : Equiv.Perm (Fin 4) => ({0, 2} : Finset (Fin 4)).map σ.toEmbedding = {0, 3}
  let B := fun σ : Equiv.Perm (Fin 4) => ({1} : Finset (Fin 4)).map σ.toEmbedding = {1}
  let C := fun σ : Equiv.Perm (Fin 4) => ({0} : Finset (Fin 4)).map σ.toEmbedding = {3}
  let D := fun σ : Equiv.Perm (Fin 4) => ({0, 3} : Finset (Fin 4)).map σ.toEmbedding = {0, 1}
  have hbound : (∑ σ ∈ univ.filter A, w σ) ≤
      (∑ σ ∈ univ.filter B, w σ) + (∑ σ ∈ univ.filter C, w σ) + (∑ σ ∈ univ.filter D, w σ) := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro σ _
    by_cases ha : A σ
    · rcases (show B σ ∨ C σ ∨ D σ from hInc σ ha) with h | h | h <;>
        rw [if_pos ha, if_pos h] <;> split_ifs <;> linarith only [hw σ]
    · rw [if_neg ha]
      split_ifs <;> linarith only [hw σ]
  obtain ⟨hA, hB, hC, hD⟩ := rationalMinorMixer_four_masses
  change (∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin 4) =>
      ({0, 2} : Finset (Fin 4)).map σ.toEmbedding = {0, 3}), w σ) ≤ _ at hbound
  dsimp only [B, C, D] at hbound
  rw [hm, hm, hm, hm, hA, hB, hC, hD] at hbound
  norm_num at hbound

/-- The event obstruction rules out weights common to both spectra. -/
theorem rationalMinorMixer_no_universalMatchingWeights :
    ¬ HasUniversalMatchingWeights rationalMinorMixer := by
  classical
  rintro ⟨w, hw, _, hd⟩
  apply rationalMinorMixer_no_common_minor_law
  refine ⟨w, hw, fun I J => ?_⟩
  symm
  apply indexed_minor_law_of_small _ rationalMinorMixer_unitary id w
  intro I' J' hc _
  have h := hd (fun i => if i ∈ I' then 0 else 1) (fun j => if j ∈ J' then 1 else 0)
  rw [determinantValue_subset_marker _ rationalMinorMixer_unitary I' J' hc,
    weightedMatchingValue_subset_marker w I' J' hc] at h
  exact Complex.ofReal_injective h

/-- Appending any number of fixed coordinates preserves this obstruction. -/
theorem rationalMinorMixer_identityPadding_no_universalMatchingWeights
    {κ : Type*} [Fintype κ] [DecidableEq κ] :
    ¬ HasUniversalMatchingWeights (fromBlocks rationalMinorMixer 0 0 (1 : Matrix κ κ ℂ)) := by
  intro h
  apply rationalMinorMixer_no_universalMatchingWeights
  exact universal_matching_weights_left_of_directSum rationalMinorMixer_unitary isUnitary_one h

end

end MOC
