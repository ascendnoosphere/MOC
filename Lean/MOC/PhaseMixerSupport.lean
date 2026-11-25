import MOC.ConicSupport
import MOC.IdentityPadding
import MOC.PhaseMixerCompression
import MOC.SpectralPerturbation
import MOC.Support
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination

/-! A phase mixer of active dimension `r` has the same determinant as one
supported on at most `7 * r^2` original labels. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [LinearOrder κ]

private def rowGram (Y : Matrix ι κ ℂ) (k : ι) (i j : κ) : ℂ :=
  conj (Y k i) * Y k j

private theorem rowGram_conj (Y : Matrix ι κ ℂ) (k : ι) (i j : κ) :
    conj (rowGram Y k i j) = rowGram Y k j i := by
  simp only [rowGram, map_mul, Complex.conj_conj]
  exact mul_comm _ _

private theorem phaseMoment_apply (Y : Matrix ι κ ℂ) (f : ι → ℂ) (i j : κ) :
    phaseMoment Y f i j = ∑ k, f k * rowGram Y k i j := by
  rw [phaseMoment, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def, rowGram]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem phaseMoment_add (Y : Matrix ι κ ℂ) (f g : ι → ℂ) :
    phaseMoment Y (f + g) = phaseMoment Y f + phaseMoment Y g := by
  simp only [phaseMoment, ← Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]

private theorem phaseMoment_smul (Y : Matrix ι κ ℂ) (c : ℂ) (f : ι → ℂ) :
    phaseMoment Y (c • f) = c • phaseMoment Y f := by
  simp only [phaseMoment, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

private theorem exists_rows_preserving_real_moments (Y : Matrix ι κ ℂ)
    (f : Fin 7 → ι → ℝ) :
    ∃ (Z : Matrix ι κ ℂ) (S : Finset ι), S.card ≤ 7 * Fintype.card κ ^ 2 ∧
      (∀ k ∉ S, ∀ j, Z k j = 0) ∧
      ∀ s, phaseMoment Z (fun k => (f s k : ℂ)) = phaseMoment Y (fun k => (f s k : ℂ)) := by
  let v (k : ι) (p : Fin 7 × κ × κ) : ℝ :=
    f p.1 k * (if p.2.1 ≤ p.2.2 then (rowGram Y k p.2.1 p.2.2).re
      else (rowGram Y k p.2.2 p.2.1).im)
  obtain ⟨w, hw, hsum, hcard, _⟩ :=
    exists_conic_support_le_finrank v (fun _ => 1) (fun _ => zero_le_one)
  let S := Finset.univ.filter fun k => w k ≠ 0
  let Z : Matrix ι κ ℂ := fun k j => (Real.sqrt (w k) : ℂ) * Y k j
  have hbound : S.card ≤ 7 * Fintype.card κ ^ 2 := by
    simpa only [S, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      pow_two] using hcard
  refine ⟨Z, S, hbound, ?_, ?_⟩
  · intro k hk j
    have hz : w k = 0 := by simpa [S] using hk
    simp [Z, hz]
  have hentry (k : ι) (i j : κ) : rowGram Z k i j = (w k : ℂ) * rowGram Y k i j := by
    have hsq : (Real.sqrt (w k) : ℂ) * (Real.sqrt (w k) : ℂ) = (w k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw k)]
    simp only [rowGram, Z, map_mul, Complex.conj_ofReal]
    linear_combination (conj (Y k i) * Y k j) * hsq
  have hcoordinate (s : Fin 7) (i j : κ) := congrArg (fun x => x (s, i, j)) hsum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul, v] at hcoordinate
  have hRe (s : Fin 7) (i j : κ) :
      (∑ k, w k * (f s k * (rowGram Y k i j).re)) =
        ∑ k, f s k * (rowGram Y k i j).re := by
    by_cases hij : i ≤ j
    · simpa only [if_pos hij] using hcoordinate s i j
    · have he (k : ι) : (rowGram Y k i j).re = (rowGram Y k j i).re := by
        rw [← rowGram_conj Y k i j, Complex.conj_re]
      simpa only [he, if_pos (le_of_not_ge hij)] using hcoordinate s j i
  have hIm (s : Fin 7) (i j : κ) :
      (∑ k, w k * (f s k * (rowGram Y k i j).im)) =
        ∑ k, f s k * (rowGram Y k i j).im := by
    rcases lt_trichotomy i j with h | rfl | h
    · simpa only [if_neg (not_le_of_gt h)] using hcoordinate s j i
    · have he (k : ι) : (rowGram Y k i i).im = 0 := by
        have hh := congrArg Complex.im (rowGram_conj Y k i i)
        rw [Complex.conj_im] at hh
        linarith
      simp only [he, mul_zero, Finset.sum_const_zero]
    · have he (k : ι) : (rowGram Y k i j).im = -(rowGram Y k j i).im := by
        rw [← rowGram_conj Y k j i, Complex.conj_im]
      simp only [he, mul_neg, Finset.sum_neg_distrib, neg_inj]
      simpa only [if_neg (not_le_of_gt h)] using hcoordinate s i j
  intro s
  ext i j : 1
  rw [phaseMoment_apply, phaseMoment_apply]
  apply Complex.ext
  · simp only [hentry, Complex.re_sum, Complex.re_ofReal_mul]
    rw [show (∑ k, f s k * (w k * (rowGram Y k i j).re)) =
        ∑ k, w k * (f s k * (rowGram Y k i j).re) from
      Finset.sum_congr rfl fun k _ => by ring]
    exact hRe s i j
  · simp only [hentry, Complex.im_sum, Complex.im_ofReal_mul]
    rw [show (∑ k, f s k * (w k * (rowGram Y k i j).im)) =
        ∑ k, w k * (f s k * (rowGram Y k i j).im) from
      Finset.sum_congr rfl fun k _ => by ring]
    exact hIm s i j

/-- A phase mixer may be replaced by one with at most `7 * r^2` nonzero
rows in the isometry, preserving its determinant on the given spectra. -/
theorem exists_sparse_phaseMixer (a b : ι → ℂ) (Y : Matrix ι κ ℂ) (W : Matrix κ κ ℂ)
    (hY : Yᴴ * Y = 1) (hW : IsUnitary W) (hreg : ∀ i, a i + b i ≠ 0) :
    ∃ (Z : Matrix ι κ ℂ) (S : Finset ι), S.card ≤ 7 * Fintype.card κ ^ 2 ∧
      (∀ k ∉ S, ∀ j, Z k j = 0) ∧ Zᴴ * Z = 1 ∧
      determinantValue a b (phaseMixer Z W) = determinantValue a b (phaseMixer Y W) := by
  let c (i : ι) := (a i + b i)⁻¹
  let d (i : ι) := c i * a i
  let e (i : ι) := b i * c i * a i
  let f : Fin 7 → ι → ℝ :=
    ![fun _ => 1, fun i => (c i).re, fun i => (c i).im, fun i => (d i).re,
      fun i => (d i).im, fun i => (e i).re, fun i => (e i).im]
  obtain ⟨Z, S, hS, hz, hm⟩ := exists_rows_preserving_real_moments Y f
  have hZ : Zᴴ * Z = 1 := by
    have h := hm 0
    change phaseMoment Z (fun _ => 1) = phaseMoment Y (fun _ => 1) at h
    simpa only [phaseMoment, Matrix.diagonal_one, Matrix.mul_one, hY] using h
  have hcomplex (g : ι → ℂ)
      (hr : phaseMoment Z (fun i => ((g i).re : ℂ)) = phaseMoment Y (fun i => ((g i).re : ℂ)))
      (hi : phaseMoment Z (fun i => ((g i).im : ℂ)) = phaseMoment Y (fun i => ((g i).im : ℂ))) :
      phaseMoment Z g = phaseMoment Y g := by
    have hg : (fun i => ((g i).re : ℂ)) + Complex.I • (fun i => ((g i).im : ℂ)) = g := by
      funext i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm Complex.I] using
        Complex.re_add_im (g i)
    rw [← hg, phaseMoment_add, phaseMoment_add, phaseMoment_smul, phaseMoment_smul, hr, hi]
  refine ⟨Z, S, hS, hz, hZ, ?_⟩
  exact determinantValue_phaseMixer_eq_of_moments a b Z Y W hZ hY hW hreg
    (hcomplex c (hm 1) (hm 2)) (hcomplex d (hm 3) (hm 4)) (hcomplex e (hm 5) (hm 6))

/-- For a fixed active dimension, inclusion for phase mixers in every ambient
dimension follows from the unrestricted finite orders through `7 * r^2`. -/
theorem holds_phaseMixer_of_small_orders
    (hsmall : ∀ m : ℕ, m ≤ 7 * Fintype.card κ ^ 2 → Conjecture (Fin m))
    (a b : ι → ℂ) (Y : Matrix ι κ ℂ) (W : Matrix κ κ ℂ)
    (hY : Yᴴ * Y = 1) (hW : IsUnitary W) : Holds a b (phaseMixer Y W) := by
  by_contra hbad
  have hsep := mt (holds_iff_directional a b (phaseMixer Y W)).mpr hbad
  push_neg at hsep
  obtain ⟨η, hη⟩ := hsep
  obtain ⟨a', b', hreg, _, hstrict⟩ :=
    exists_regular_spectra_of_support_violation a b _ η hη
  obtain ⟨Z, S, hS, hzero, hZ, hdet⟩ :=
    exists_sparse_phaseMixer a' b' Y W hY hW (fun i => hreg i i)
  have hs : Holds a' b' (phaseMixer Z W) := by
    apply holds_of_supported_unitary_perturbation hsmall a' b'
      (Z * (W - 1) * Zᴴ) S hS (phaseMixer_unitary Z W hZ hW)
    intro i j hij
    rcases hij with hi | hj
    · simp only [Matrix.mul_apply, hzero i hi, zero_mul, Finset.sum_const_zero]
    · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hzero j hj, star_zero,
        mul_zero, Finset.sum_const_zero]
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a' b' _).mp hs η
  rw [hdet] at hσ
  exact (not_le_of_gt (hstrict σ)) hσ

end

end MOC
