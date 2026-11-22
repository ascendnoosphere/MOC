import MOC.ContactCensus
import MOC.WeightedDiamondPolynomial

/-! The two-dimensional split sector distinguishes a general spectral
support profile from a weighted-diamond score. -/

open BigOperators

namespace MOC

private def splitPair (i : Fin 3) : Finset (Fin 4) := ![{0, 1}, {0, 2}, {0, 3}] i

private def splitSum {R : Type*} [AddCommMonoid R] (v : Fin 24 → R) (i j : Fin 3) : R :=
  ∑ k, if (splitPair j).map (fourPerm k).toEmbedding = splitPair i ∨
      (splitPair j).map (fourPerm k).toEmbedding = (splitPair i)ᶜ then v k else 0

/-- Remove the reference row and column from the three-by-three sums over
permutations mapping one split into the other. -/
def fourSplitContrast {R : Type*} [AddCommGroup R] (v : Fin 24 → R) (i j : Fin 2) : R :=
  splitSum v i.castSucc j.castSucc - splitSum v i.castSucc 2 -
    splitSum v 2 j.castSucc + splitSum v 2 2

private theorem splitContrast_map {R S : Type*} [AddCommGroup R] [AddCommGroup S]
    (f : R →+ S) (v : Fin 24 → R) (i j : Fin 2) :
    f (fourSplitContrast v i j) = fourSplitContrast (fun k => f (v k)) i j := by
  simp only [fourSplitContrast, splitSum, map_sub, map_add, map_sum, apply_ite, map_zero]

private def splitPairScore (s : Finset (Fin 4) → ℝ) (i : Fin 3) : ℝ :=
  s (splitPair i) + s (splitPair i)ᶜ

set_option maxHeartbeats 2500000 in
private theorem splitContrast_diamond (t : ℝ) (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ)
    (i j : Fin 2) :
    fourSplitContrast (fun k => weightedDiamondScore t f g s (fourPerm k)) i j =
      6 * (splitPairScore s i.castSucc - splitPairScore s 2) * (![1, t] : Fin 2 → ℝ) j := by
  have hc₁ : (({1} : Finset (Fin 4))ᶜ.erase 0) = {2, 3} := by decide
  have hc₂ : (({2} : Finset (Fin 4))ᶜ.erase 0) = {1, 3} := by decide
  have hc₃ : (({3} : Finset (Fin 4))ᶜ.erase 0) = {1, 2} := by decide
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [fourSplitContrast, splitSum, splitPair, splitPairScore,
      weightedDiamondScore, Fin.sum_univ_succ, fourPerm, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, Finset.map_insert, Finset.map_singleton] <;>
    simp only [hc₁, hc₂, hc₃, Finset.pair_comm] <;> ring

/-- The split contrast of a weighted-diamond score has determinant zero. -/
theorem fourSplitContrast_diamond_det_eq_zero (t : ℝ) (f g : Fin 4 → ℝ)
    (s : Finset (Fin 4) → ℝ) :
    let C := fourSplitContrast fun k => weightedDiamondScore t f g s (fourPerm k)
    C 0 0 * C 1 1 - C 0 1 * C 1 0 = 0 := by
  dsimp only
  simp only [splitContrast_diamond, Matrix.cons_val_zero', Matrix.cons_val_succ']
  ring

/-- The differences of the two complementary pair-product sums from the
third pair-product sum, factored as differences of spectral values. -/
def fourSpectralSplitDifference (a : Fin 4 → ℂ) : Fin 2 → ℂ :=
  ![(a 0 - a 2) * (a 1 - a 3), (a 0 - a 1) * (a 2 - a 3)]

set_option maxHeartbeats 2500000 in
private theorem splitContrast_spectral (a b : Fin 4 → ℂ) (i j : Fin 2) :
    fourSplitContrast (fun k => matchingProduct a b (fourPerm k)) i j =
      6 * fourSpectralSplitDifference a i * fourSpectralSplitDifference b j := by
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [fourSplitContrast, splitSum, splitPair,
      fourSpectralSplitDifference, matchingProduct, Fin.sum_univ_succ, Fin.prod_univ_four,
      fourPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Finset.map_insert,
      Finset.map_singleton] <;> ring

private theorem splitContrast_projected (a b : Fin 4 → ℂ) (η : ℂ) (i j : Fin 2) :
    fourSplitContrast (fun k => (η * matchingProduct a b (fourPerm k)).re) i j =
      (η * (6 * fourSpectralSplitDifference a i * fourSpectralSplitDifference b j)).re := by
  let f : ℂ →+ ℝ := Complex.reLm.toAddMonoidHom.comp (LinearMap.mulLeft ℂ η).toAddMonoidHom
  change fourSplitContrast (fun k => f (matchingProduct a b (fourPerm k))) i j =
    f (6 * fourSpectralSplitDifference a i * fourSpectralSplitDifference b j)
  rw [← splitContrast_map, splitContrast_spectral]

/-- Signed area of the two complex pair-product differences. -/
def fourSpectralSplitArea (a : Fin 4 → ℂ) : ℝ :=
  (fourSpectralSplitDifference a 0).re * (fourSpectralSplitDifference a 1).im -
    (fourSpectralSplitDifference a 1).re * (fourSpectralSplitDifference a 0).im

/-- The split contrast of projected matching products has full rank when
both spectra have nonzero split area and the support multiplier is nonzero. -/
theorem fourSplitContrast_spectral_det (a b : Fin 4 → ℂ) (η : ℂ) :
    let C := fourSplitContrast fun k => (η * matchingProduct a b (fourPerm k)).re
    C 0 0 * C 1 1 - C 0 1 * C 1 0 =
      -36 * Complex.normSq η * fourSpectralSplitArea a * fourSpectralSplitArea b := by
  dsimp only
  simp only [splitContrast_projected]
  simp only [fourSpectralSplitArea, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul,
    sub_zero, zero_add, add_zero]
  ring

/-- A support profile whose two spectra have nonzero split area cannot be
represented by one weighted-diamond score. -/
theorem spectral_projected_ne_weightedDiamond_of_split_area (a b : Fin 4 → ℂ) (η : ℂ)
    (hη : η ≠ 0) (ha : fourSpectralSplitArea a ≠ 0) (hb : fourSpectralSplitArea b ≠ 0)
    (t : ℝ) (f g : Fin 4 → ℝ) (s : Finset (Fin 4) → ℝ) :
    ¬ ∀ σ, (η * matchingProduct a b σ).re = weightedDiamondScore t f g s σ := by
  intro h
  have he : (fun k => (η * matchingProduct a b (fourPerm k)).re) =
      fun k => weightedDiamondScore t f g s (fourPerm k) := funext (fun k => h (fourPerm k))
  have hd := fourSplitContrast_spectral_det a b η
  dsimp only at hd
  rw [he] at hd
  have hz := fourSplitContrast_diamond_det_eq_zero t f g s
  dsimp only at hz
  rw [hz] at hd
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.normSq_pos.mpr hη).ne')
    ha) hb) hd.symm

end MOC
