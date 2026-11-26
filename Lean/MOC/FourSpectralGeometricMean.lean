import MOC.ContactCensus
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A Gaussian integer counterexample to the proposed spectral geometric
mean bound in order four. -/

namespace MOC

private def geometricMeanLeft : Fin 4 → GaussianInt :=
  ![⟨2, 1⟩, ⟨-4, 5⟩, ⟨0, 3⟩, ⟨-7, 0⟩]

private def geometricMeanRight : Fin 4 → GaussianInt :=
  ![⟨2, 0⟩, ⟨1, 1⟩, ⟨-8, -1⟩, ⟨-7, 5⟩]

private def geometricMeanIntegerMatching (p : Fin 24) : GaussianInt :=
  let entry (i : Fin 4) := geometricMeanLeft i + geometricMeanRight (fourPerm p i)
  entry 0 * entry 1 * entry 2 * entry 3

private def geometricMeanProjectionTable : Fin 24 → ℤ :=
  ![-408, 339, 1972, -1548, 2363, -1904, -884, -565, 1508, -2020, 1807, -2040,
    -1938, -1242, -1926, -810, -1950, -1530, -2037, -1660, -1689, -1320, -2012, -2020]

private theorem geometricMeanMatching_map (p : Fin 24) :
    GaussianInt.toComplex (geometricMeanIntegerMatching p) =
      matchingProduct (fun i => GaussianInt.toComplex (geometricMeanLeft i))
        (fun i => GaussianInt.toComplex (geometricMeanRight i)) (fourPerm p).symm := by
  rw [matchingProduct_inverse, Fin.prod_univ_four]
  simp only [geometricMeanIntegerMatching, map_mul, map_add]

set_option maxRecDepth 4096 in
private theorem geometricMeanProjectionTable_eq (p : Fin 24) :
    geometricMeanProjectionTable p = (geometricMeanIntegerMatching p).re := by
  exact (by decide +kernel : ∀ j : Fin 24,
    geometricMeanProjectionTable j = (geometricMeanIntegerMatching j).re) p

set_option maxRecDepth 4096 in
private theorem geometricMeanIntegerMatching_injective :
    Function.Injective geometricMeanIntegerMatching := by
  decide +kernel

/-- The index order is lexicographic in the row-to-column convention.
For the real projection, index 11 attains the minimum `m`. With
`f p` equal to the projected product minus `m`, indices 17 and 22 are
3421 and 4312. The proposed signed difference is positive and strictly
larger than their geometric mean, even for regular spectra. -/
theorem exists_four_spectral_geometric_mean_counterexample :
    ∃ (a b : Fin 4 → ℂ) (m : ℝ),
      (∀ i j, a i + b j ≠ 0) ∧
      Function.Injective (matchingProduct a b) ∧
      (∀ p : Fin 24, m ≤ (matchingProduct a b (fourPerm p).symm).re) ∧
      (matchingProduct a b (fourPerm 11).symm).re = m ∧
      let f (p : Fin 24) := (matchingProduct a b (fourPerm p).symm).re - m
      let h := f 4 - f 18 - f 8 - f 17 - f 5
      f 17 = 510 ∧ f 22 = 28 ∧ h = 206 ∧ Real.sqrt (f 17 * f 22) < h := by
  let a (i : Fin 4) := GaussianInt.toComplex (geometricMeanLeft i)
  let b (i : Fin 4) := GaussianInt.toComplex (geometricMeanRight i)
  have hproj (p : Fin 24) : (matchingProduct a b (fourPerm p).symm).re =
      (geometricMeanProjectionTable p : ℝ) := by
    calc
      _ = (GaussianInt.toComplex (geometricMeanIntegerMatching p)).re :=
        congrArg Complex.re (geometricMeanMatching_map p).symm
      _ = _ := by rw [geometricMeanProjectionTable_eq p, GaussianInt.to_real_re]
  refine ⟨a, b, -2040, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    have hn : ∀ x y : Fin 4, geometricMeanLeft x + geometricMeanRight y ≠ 0 := by
      decide +kernel
    apply hn i j
    apply GaussianInt.toComplex_injective
    simpa only [map_add, map_zero, a, b] using h
  · intro σ τ h
    obtain ⟨p, hp⟩ := fourPerm_surjective σ.symm
    obtain ⟨q, hq⟩ := fourPerm_surjective τ.symm
    have hp' : (fourPerm p).symm = σ := by rw [hp, Equiv.symm_symm]
    have hq' : (fourPerm q).symm = τ := by rw [hq, Equiv.symm_symm]
    have he : geometricMeanIntegerMatching p = geometricMeanIntegerMatching q := by
      apply GaussianInt.toComplex_injective
      rw [geometricMeanMatching_map p, geometricMeanMatching_map q, hp', hq', h]
    rw [← hp', ← hq', geometricMeanIntegerMatching_injective he]
  · intro p
    rw [hproj p]
    have hl : ∀ j : Fin 24, (-2040 : ℤ) ≤ geometricMeanProjectionTable j := by
      decide +kernel
    exact_mod_cast hl p
  · rw [hproj 11]
    norm_num [geometricMeanProjectionTable, Matrix.cons_val]
  · intro f h
    have hf (p : Fin 24) : f p = (geometricMeanProjectionTable p : ℝ) + 2040 := by
      change (matchingProduct a b (fourPerm p).symm).re - (-2040) = _
      rw [hproj p, sub_neg_eq_add]
    have h17 : f 17 = 510 := by
      rw [hf]
      norm_num [geometricMeanProjectionTable, Matrix.cons_val]
    have h22 : f 22 = 28 := by
      rw [hf]
      norm_num [geometricMeanProjectionTable, Matrix.cons_val]
    have hh : h = 206 := by
      change f 4 - f 18 - f 8 - f 17 - f 5 = _
      simp only [hf]
      norm_num [geometricMeanProjectionTable, Matrix.cons_val]
    refine ⟨h17, h22, hh, ?_⟩
    rw [h17, h22, hh]
    have hs : (Real.sqrt (510 * 28 : ℝ)) ^ 2 = 510 * 28 :=
      Real.sq_sqrt (by norm_num)
    by_contra! hn
    have hsum : 0 ≤ Real.sqrt (510 * 28 : ℝ) + 206 :=
      add_nonneg (Real.sqrt_nonneg _) (by norm_num)
    nlinarith only [hs, mul_nonneg (sub_nonneg.mpr hn) hsum]

end MOC
