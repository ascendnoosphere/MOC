import MOC.ContactCrossRatios
import MOC.Support
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Integration
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! A deterministic matching triangle and the failure bound it gives for a
random ensemble. The Gaussian and Haar estimates enter at distinct steps. -/

open BigOperators Matrix MeasureTheory
open scoped ENNReal

namespace MOC

noncomputable section

/-- The nonreal cube root of unity with positive imaginary part. -/
def matchingTriangleRoot : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private theorem matchingTriangleRoot_sq : matchingTriangleRoot ^ 2 =
    (⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ : ℂ) := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp only [pow_two, matchingTriangleRoot, Complex.mul_re]
    linear_combination -hs / 4
  · simp only [pow_two, matchingTriangleRoot, Complex.mul_im]
    ring

private theorem norm_matchingTriangleRoot : ‖matchingTriangleRoot‖ = 1 := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : ‖matchingTriangleRoot‖ ^ 2 = 1 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, matchingTriangleRoot]
    linear_combination hs / 4
  exact (sq_eq_sq₀ (norm_nonneg matchingTriangleRoot) (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [one_pow] using hn)

private theorem equilateral_matching_support (u : ℂ) :
    ‖u‖ / 2 ≤ u.re ∨ ‖u‖ / 2 ≤ (u * matchingTriangleRoot).re ∨
      ‖u‖ / 2 ≤ (u * matchingTriangleRoot ^ 2).re := by
  let x : ℝ := u.re
  let y : ℝ := (u * matchingTriangleRoot).re
  let z : ℝ := (u * matchingTriangleRoot ^ 2).re
  have hsum : x + y + z = 0 := by
    simp only [x, y, z, matchingTriangleRoot_sq, matchingTriangleRoot, Complex.mul_re]
    ring
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsq : x ^ 2 + y ^ 2 + z ^ 2 = 3 * ‖u‖ ^ 2 / 2 := by
    rw [Complex.sq_norm]
    simp only [x, y, z, matchingTriangleRoot_sq, matchingTriangleRoot, Complex.mul_re,
      Complex.normSq_apply]
    linear_combination (u.im ^ 2 / 2) * hs
  change ‖u‖ / 2 ≤ x ∨ ‖u‖ / 2 ≤ y ∨ ‖u‖ / 2 ≤ z
  by_contra! h
  obtain ⟨hx, hy, hz⟩ := h
  have hp := mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)
  have hq := mul_pos (sub_pos.mpr hx) (sub_pos.mpr hz)
  have hr := mul_pos (sub_pos.mpr hy) (sub_pos.mpr hz)
  have hsumSq := congrArg (fun v : ℝ => v ^ 2) hsum
  have hsumNorm := congrArg (fun v : ℝ => ‖u‖ * v) hsum
  nlinarith only [hp, hq, hr, hsumSq, hsumNorm, hsq]

private theorem norm_matching_product_perturbation (q₁ q₂ : ℂ)
    (hq₁ : ‖q₁ - matchingTriangleRoot‖ ≤ 1 / 10)
    (hq₂ : ‖q₂ - matchingTriangleRoot‖ ≤ 1 / 10) :
    ‖q₁ * q₂ - matchingTriangleRoot ^ 2‖ ≤ 21 / 100 := by
  have hq : ‖q₂‖ ≤ 11 / 10 := by
    calc
      ‖q₂‖ = ‖(q₂ - matchingTriangleRoot) + matchingTriangleRoot‖ := by rw [sub_add_cancel]
      _ ≤ ‖q₂ - matchingTriangleRoot‖ + ‖matchingTriangleRoot‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_matchingTriangleRoot]; linarith only [hq₂]
  rw [show q₁ * q₂ - matchingTriangleRoot ^ 2 =
    (q₁ - matchingTriangleRoot) * q₂ + matchingTriangleRoot * (q₂ - matchingTriangleRoot) by ring]
  apply (norm_add_le _ _).trans
  rw [Complex.norm_mul, Complex.norm_mul, norm_matchingTriangleRoot, one_mul]
  have hprod : ‖q₁ - matchingTriangleRoot‖ * ‖q₂‖ ≤ (1 / 10 : ℝ) * (11 / 10) :=
    mul_le_mul hq₁ hq (norm_nonneg _) (by norm_num)
  nlinarith only [hprod, hq₂]

private theorem perturbed_equilateral_matching_support (u q₁ q₂ : ℂ)
    (hq₁ : ‖q₁ - matchingTriangleRoot‖ ≤ 1 / 10)
    (hq₂ : ‖q₂ - matchingTriangleRoot‖ ≤ 1 / 10) :
    ‖u‖ / 4 ≤ u.re ∨ ‖u‖ / 4 ≤ (u * q₁).re ∨ ‖u‖ / 4 ≤ (u * (q₁ * q₂)).re := by
  have step (v w : ℂ) (herr : ‖v - w‖ ≤ 21 / 100)
      (hs : ‖u‖ / 2 ≤ (u * v).re) : ‖u‖ / 4 ≤ (u * w).re := by
    have h := (Complex.re_le_norm (u * (v - w))).trans
      (by rw [Complex.norm_mul]; exact mul_le_mul_of_nonneg_left herr (norm_nonneg u))
    rw [mul_sub, Complex.sub_re] at h
    nlinarith only [h, hs, norm_nonneg u]
  rcases equilateral_matching_support u with h | h | h
  · exact Or.inl (by linarith only [h, norm_nonneg u])
  · have herr : ‖matchingTriangleRoot - q₁‖ ≤ 21 / 100 := by
      rw [norm_sub_rev]
      exact hq₁.trans (by norm_num)
    exact Or.inr (Or.inl (step _ _ herr h))
  · have herr : ‖matchingTriangleRoot ^ 2 - q₁ * q₂‖ ≤ 21 / 100 := by
      rw [norm_sub_rev]
      exact norm_matching_product_perturbation q₁ q₂ hq₁ hq₂
    exact Or.inr (Or.inr (step _ _ herr h))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ratio of the matching product for one transposition to the identity
matching product. The ratio uses just the two affected factors. -/
def matchingSwapRatio (a b : ι → ℂ) (i j : ι) : ℂ :=
  ((a j + b i) * (a i + b j)) / ((a i + b i) * (a j + b j))

private theorem matchingProduct_swap_ratio (a b : ι → ℂ)
    (hz : matchingProduct a b 1 ≠ 0) (i j : ι) (hij : i ≠ j) :
    matchingProduct a b (Equiv.swap i j) = matchingProduct a b 1 * matchingSwapRatio a b i j := by
  have hg := matchingProduct_right_swap_gap_ratio a b (1 : Equiv.Perm ι) hz i j hij
  simp only [one_mul, Equiv.Perm.one_apply] at hg
  have hne (k : ι) : a k + b k ≠ 0 := by
    simpa only [Equiv.Perm.one_apply] using Finset.prod_ne_zero_iff.mp hz k (Finset.mem_univ k)
  calc
    _ = matchingProduct a b 1 -
        matchingProduct a b 1 * (((a i - a j) * (b j - b i)) /
          ((a i + b i) * (a j + b j))) := by rw [← hg]; ring
    _ = _ := by unfold matchingSwapRatio; field_simp [hne i, hne j] <;> ring

/-- Four distinct labels supply two disjoint transpositions whose ratios
are within one tenth of the cube root used in the triangle. -/
def HasMatchingTriangleBlock (a b : ι → ℂ) : Prop :=
  ∃ labels : Fin 4 ↪ ι,
    ‖matchingSwapRatio a b (labels 0) (labels 1) - matchingTriangleRoot‖ ≤ 1 / 10 ∧
    ‖matchingSwapRatio a b (labels 2) (labels 3) - matchingTriangleRoot‖ ≤ 1 / 10

/-- A good block puts the disk of radius one quarter of the identity
matching modulus inside the full matching hull. -/
theorem matchingHull_closedBall_of_triangleBlock (a b : ι → ℂ)
    (hblock : HasMatchingTriangleBlock a b) :
    Metric.closedBall 0 (‖matchingProduct a b 1‖ / 4) ⊆
      convexHull ℝ (Set.range (matchingProduct a b)) := by
  intro d hd
  have hd' : ‖d‖ ≤ ‖matchingProduct a b 1‖ / 4 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hd
  by_cases hz : matchingProduct a b 1 = 0
  · rw [hz, norm_zero, zero_div] at hd'
    rw [norm_le_zero_iff.mp hd', ← hz]
    exact matchingProduct_mem_hull a b 1
  obtain ⟨e, h₁, h₂⟩ := hblock
  let s : Equiv.Perm ι := Equiv.swap (e 0) (e 1)
  let t : Equiv.Perm ι := Equiv.swap (e 2) (e 3)
  let q₁ := matchingSwapRatio a b (e 0) (e 1)
  let q₂ := matchingSwapRatio a b (e 2) (e 3)
  have hdist : ∀ i, s i = i ∨ t i = i := by
    intro i
    by_cases hi : i = e 0
    · subst i
      exact Or.inr (Equiv.swap_apply_of_ne_of_ne (e.injective.ne (by decide : (0 : Fin 4) ≠ 2))
        (e.injective.ne (by decide : (0 : Fin 4) ≠ 3)))
    by_cases hj : i = e 1
    · subst i
      exact Or.inr (Equiv.swap_apply_of_ne_of_ne (e.injective.ne (by decide : (1 : Fin 4) ≠ 2))
        (e.injective.ne (by decide : (1 : Fin 4) ≠ 3)))
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hi hj)
  have hs : matchingProduct a b s = matchingProduct a b 1 * q₁ :=
    matchingProduct_swap_ratio a b hz (e 0) (e 1) (e.injective.ne (by decide))
  have ht : matchingProduct a b t = matchingProduct a b 1 * q₂ :=
    matchingProduct_swap_ratio a b hz (e 2) (e 3) (e.injective.ne (by decide))
  have hst : matchingProduct a b (s * t) = matchingProduct a b 1 * (q₁ * q₂) := by
    apply mul_left_cancel₀ hz
    have h := matchingProduct_disjoint_perms_identity a b 1 s t hdist
    simp only [one_mul, hs, ht] at h
    calc
      _ = (matchingProduct a b 1 * q₁) * (matchingProduct a b 1 * q₂) := h
      _ = _ := by ring
  apply mem_hull_of_directional_bound (matchingProduct a b)
  intro u
  let v := u * matchingProduct a b 1
  have hproj : (u * d).re ≤ ‖v‖ / 4 := by
    calc
      _ ≤ ‖u * d‖ := Complex.re_le_norm _
      _ = ‖u‖ * ‖d‖ := Complex.norm_mul _ _
      _ ≤ ‖u‖ * (‖matchingProduct a b 1‖ / 4) :=
        mul_le_mul_of_nonneg_left hd' (norm_nonneg u)
      _ = ‖v‖ / 4 := by rw [show v = _ from rfl, Complex.norm_mul, mul_div_assoc]
  rcases perturbed_equilateral_matching_support v q₁ q₂ h₁ h₂ with h | h | h
  · exact ⟨1, hproj.trans h⟩
  · exact ⟨s, hproj.trans (by simpa only [v, hs, mul_assoc] using h)⟩
  · exact ⟨s * t, hproj.trans (by simpa only [v, hst, mul_assoc] using h)⟩

/-- The center of the last coordinate in each pair of Gaussian disks. -/
def matchingTriangleCenter : ℂ := ⟨-2 / 7, Real.sqrt 3 / 7⟩

private theorem matchingTriangleCenter_data :
    (2 : ℂ) * matchingTriangleCenter = matchingTriangleRoot * (1 + matchingTriangleCenter) ∧
    ‖matchingTriangleCenter‖ ≤ 1 / 2 ∧
    2 / 3 ≤ ‖1 + matchingTriangleCenter‖ ∧ ‖1 + matchingTriangleCenter‖ ≤ 1 := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have ht : ‖matchingTriangleCenter‖ ^ 2 = (1 : ℝ) / 7 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, matchingTriangleCenter]
    linear_combination hs / 49
  have h1t : ‖1 + matchingTriangleCenter‖ ^ 2 = (4 : ℝ) / 7 := by
    rw [Complex.sq_norm]
    norm_num only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, zero_add, matchingTriangleCenter]
    linear_combination hs / 49
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Complex.ext
    · norm_num only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.re_ofNat,
        Complex.im_ofNat, Complex.one_re, Complex.one_im, matchingTriangleCenter,
        matchingTriangleRoot, zero_add, zero_mul, sub_zero]
      linear_combination hs / 14
    · norm_num only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.re_ofNat,
        Complex.im_ofNat, Complex.one_re, Complex.one_im, matchingTriangleCenter,
        matchingTriangleRoot, zero_add, zero_mul, add_zero]
      ring
  · by_contra! hn
    have hpos : 0 < (‖matchingTriangleCenter‖ - 1 / 2) *
        (‖matchingTriangleCenter‖ + 1 / 2) :=
      mul_pos (sub_pos.mpr hn) (by positivity)
    nlinarith only [ht, hpos]
  · by_contra! hn
    have hpos : 0 < (2 / 3 - ‖1 + matchingTriangleCenter‖) *
        (2 / 3 + ‖1 + matchingTriangleCenter‖) :=
      mul_pos (sub_pos.mpr hn) (by positivity)
    nlinarith only [h1t, hpos]
  · by_contra! hn
    have hpos : 0 < (‖1 + matchingTriangleCenter‖ - 1) *
        (‖1 + matchingTriangleCenter‖ + 1) :=
      mul_pos (sub_pos.mpr hn) (by positivity)
    nlinarith only [h1t, hpos]

private theorem norm_pair_sum_difference (x y X Y : ℂ)
    (hx : ‖x - X‖ ≤ 1 / 200) (hy : ‖y - Y‖ ≤ 1 / 200) :
    ‖(x + y) - (X + Y)‖ ≤ 1 / 100 := by
  rw [show (x + y) - (X + Y) = (x - X) + (y - Y) by ring]
  exact (norm_add_le _ _).trans (by linarith only [hx, hy])

private theorem norm_pair_product_difference (x y X Y : ℂ) (c d : ℝ)
    (hx : ‖x - X‖ ≤ 1 / 100) (hy : ‖y - Y‖ ≤ 1 / 100)
    (hX : ‖X‖ ≤ c) (hY : ‖Y‖ ≤ d) :
    ‖x * y - X * Y‖ ≤ (c + d) / 100 + 1 / 10000 := by
  have hxy : ‖(x - X) * (y - Y)‖ ≤ (1 / 100 : ℝ) * (1 / 100) := by
    rw [Complex.norm_mul]
    exact mul_le_mul hx hy (norm_nonneg _) (by norm_num)
  have hxY : ‖(x - X) * Y‖ ≤ (1 / 100 : ℝ) * d := by
    rw [Complex.norm_mul]
    exact mul_le_mul hx hY (norm_nonneg _) (by norm_num)
  have hXy : ‖X * (y - Y)‖ ≤ c * (1 / 100 : ℝ) := by
    rw [Complex.norm_mul]
    exact mul_le_mul hX hy (norm_nonneg _) ((norm_nonneg X).trans hX)
  rw [show x * y - X * Y = ((x - X) * Y + X * (y - Y)) + (x - X) * (y - Y) by ring]
  have h := norm_add_le ((x - X) * Y + X * (y - Y)) ((x - X) * (y - Y))
  have h' := norm_add_le ((x - X) * Y) (X * (y - Y))
  linarith only [h, h', hxy, hxY, hXy]

/-- The four closed disks of radius one two-hundredth give a valid
swap ratio. In particular, the two denominator factors are nonzero. -/
theorem matchingSwapRatio_near_triangleRoot_of_disks (a₀ a₁ b₀ b₁ : ℂ)
    (ha₀ : ‖a₀‖ ≤ 1 / 200) (ha₁ : ‖a₁ - 1‖ ≤ 1 / 200)
    (hb₀ : ‖b₀ - 1‖ ≤ 1 / 200) (hb₁ : ‖b₁ - matchingTriangleCenter‖ ≤ 1 / 200) :
    (a₀ + b₀) * (a₁ + b₁) ≠ 0 ∧
      ‖((a₁ + b₀) * (a₀ + b₁)) / ((a₀ + b₀) * (a₁ + b₁)) -
        matchingTriangleRoot‖ ≤ 1 / 10 := by
  let t := matchingTriangleCenter
  let P := (a₁ + b₀) * (a₀ + b₁)
  let D := (a₀ + b₀) * (a₁ + b₁)
  obtain ⟨hroot, hsmall, hdmin, hdmax⟩ := matchingTriangleCenter_data
  have hP : ‖P - 2 * t‖ ≤ (251 : ℝ) / 10000 := by
    have hx : ‖(a₁ + b₀) - 2‖ ≤ 1 / 100 := by
      simpa only [one_add_one_eq_two] using norm_pair_sum_difference a₁ b₀ 1 1 ha₁ hb₀
    have hy : ‖(a₀ + b₁) - t‖ ≤ 1 / 100 := by
      simpa only [sub_zero, zero_add] using norm_pair_sum_difference a₀ b₁ 0 t (by simpa only
        [sub_zero] using ha₀) hb₁
    have htwo : ‖(2 : ℂ)‖ ≤ (2 : ℝ) := by
      rw [← one_add_one_eq_two]
      simpa only [norm_one, one_add_one_eq_two] using norm_add_le (1 : ℂ) 1
    have h := norm_pair_product_difference (a₁ + b₀) (a₀ + b₁) 2 t 2 (1 / 2)
      hx hy htwo hsmall
    change ‖(a₁ + b₀) * (a₀ + b₁) - 2 * t‖ ≤ _
    linarith only [h]
  have hD : ‖D - (1 + t)‖ ≤ (201 : ℝ) / 10000 := by
    have hx : ‖(a₀ + b₀) - 1‖ ≤ 1 / 100 := by
      simpa only [sub_zero, zero_add] using norm_pair_sum_difference a₀ b₀ 0 1 (by
        simpa only [sub_zero] using ha₀) hb₀
    have hy := norm_pair_sum_difference a₁ b₁ 1 t ha₁ hb₁
    have h := norm_pair_product_difference (a₀ + b₀) (a₁ + b₁) 1 (1 + t) 1 1
      hx hy (by rw [norm_one]) hdmax
    simp only [one_mul] at h
    change ‖(a₀ + b₀) * (a₁ + b₁) - (1 + t)‖ ≤ _
    linarith only [h]
  have hDlower : (2 : ℝ) / 3 - 201 / 10000 ≤ ‖D‖ := by
    have h := norm_add_le (1 + t - D) D
    rw [sub_add_cancel, norm_sub_rev (1 + t) D] at h
    linarith only [h, hD, hdmin]
  have hDpos : 0 < ‖D‖ := lt_of_lt_of_le (by norm_num) hDlower
  have hDne : D ≠ 0 := norm_pos_iff.mp hDpos
  refine ⟨hDne, ?_⟩
  change ‖P / D - matchingTriangleRoot‖ ≤ _
  have hratio : P / D - matchingTriangleRoot =
      ((P - 2 * t) + matchingTriangleRoot * (1 + t - D)) / D := by
    rw [mul_sub, ← hroot]
    field_simp [hDne] <;> ring
  rw [hratio, Complex.norm_div, div_le_iff₀ hDpos]
  have h := norm_add_le (P - 2 * t) (matchingTriangleRoot * (1 + t - D))
  rw [Complex.norm_mul, norm_matchingTriangleRoot, one_mul, norm_sub_rev (1 + t) D] at h
  linarith only [h, hP, hD, hDlower]

/-- The standard complex Gaussian density with respect to planar volume. -/
def standardComplexGaussianDensity (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(‖z‖ ^ 2)) / Real.pi)

/-- The measure with the standard complex Gaussian density. -/
def standardComplexGaussian : Measure ℂ :=
  volume.withDensity standardComplexGaussianDensity

/-- The area of a disk times a lower bound on its density gives a
lower bound on its Gaussian mass. -/
theorem standardComplexGaussian_closedBall_lower (c : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal (r ^ 2 * Real.exp (-((‖c‖ + r) ^ 2))) ≤
      standardComplexGaussian (Metric.closedBall c r) := by
  have hmeas : MeasurableSet (Metric.closedBall c r) := isClosed_closedBall.measurableSet
  rw [standardComplexGaussian, withDensity_apply _ hmeas]
  have hbound : ∀ z ∈ Metric.closedBall c r,
      ENNReal.ofReal (Real.exp (-((‖c‖ + r) ^ 2)) / Real.pi) ≤ standardComplexGaussianDensity z := by
    intro z hz
    have hdist : ‖z - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hnorm : ‖z‖ ≤ ‖c‖ + r := by
      have h := norm_add_le (z - c) c
      rw [sub_add_cancel, add_comm] at h
      exact h.trans (add_le_add_left hdist ‖c‖)
    have hsq : ‖z‖ ^ 2 ≤ (‖c‖ + r) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hnorm hnorm (norm_nonneg z)
        ((norm_nonneg z).trans hnorm)
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsq)) Real.pi_pos.le
  have hmono :
      (∫⁻ _ in Metric.closedBall c r, ENNReal.ofReal (Real.exp (-((‖c‖ + r) ^ 2)) / Real.pi)) ≤
        ∫⁻ z in Metric.closedBall c r, standardComplexGaussianDensity z :=
    lintegral_mono_ae ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hbound))
  have hfactor : ENNReal.ofReal (Real.exp (-((‖c‖ + r) ^ 2)) / Real.pi) *
      volume (Metric.closedBall c r) = ENNReal.ofReal (r ^ 2 * Real.exp (-((‖c‖ + r) ^ 2))) := by
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (sq_nonneg r),
      ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le Real.pi_pos.le)]
    congr 1
    field_simp [Real.pi_pos.ne'] <;> ring
  rw [setLIntegral_const, hfactor] at hmono
  exact hmono

/-- The three deterministic obstructions giving the union bound. The
distribution of the samples is arbitrary in this implication. -/
theorem matchingTriangle_failure_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a b : Ω → ι → ℂ) (U : Ω → Matrix ι ι ℂ) (R : ℝ) :
    μ {x | ¬ Holds (a x) (b x) (U x)} ≤
      μ {x | ¬ HasMatchingTriangleBlock (a x) (b x)} +
        μ {x | ‖matchingProduct (a x) (b x) 1‖ < R} +
        μ {x | R / 4 < ‖determinantValue (a x) (b x) (U x)‖} := by
  classical
  let B : Set Ω := {x | ¬ HasMatchingTriangleBlock (a x) (b x)}
  let Z : Set Ω := {x | ‖matchingProduct (a x) (b x) 1‖ < R}
  let D : Set Ω := {x | R / 4 < ‖determinantValue (a x) (b x) (U x)‖}
  have hsub : {x | ¬ Holds (a x) (b x) (U x)} ⊆ (B ∪ Z) ∪ D := by
    intro x hx
    change ¬ Holds (a x) (b x) (U x) at hx
    by_contra h
    change ¬ ((¬ HasMatchingTriangleBlock (a x) (b x) ∨
      ‖matchingProduct (a x) (b x) 1‖ < R) ∨
      R / 4 < ‖determinantValue (a x) (b x) (U x)‖) at h
    have hblock : HasMatchingTriangleBlock (a x) (b x) := by
      by_contra hb
      exact h (Or.inl (Or.inl hb))
    have hz : R ≤ ‖matchingProduct (a x) (b x) 1‖ :=
      le_of_not_gt fun hz => h (Or.inl (Or.inr hz))
    have hd : ‖determinantValue (a x) (b x) (U x)‖ ≤ R / 4 :=
      le_of_not_gt fun hd => h (Or.inr hd)
    apply hx
    apply matchingHull_closedBall_of_triangleBlock (a x) (b x) hblock
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hd.trans (div_le_div_of_nonneg_right hz (by norm_num))
  exact (measure_mono hsub).trans ((measure_union_le (B ∪ Z) D).trans
    (add_le_add_right (measure_union_le B Z) (μ D)))

/-- Independent bad-block events multiply. Each successful block is
enough to meet the deterministic triangle condition. -/
theorem matchingTriangle_no_block_measure_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a b : Ω → ι → ℂ) {m : ℕ} (bad : Fin m → Set Ω)
    (hind : ProbabilityTheory.iIndepSet bad μ) (q : ℝ≥0∞)
    (hmass : ∀ j, μ (bad j) ≤ q)
    (hgood : ∀ x j, x ∉ bad j → HasMatchingTriangleBlock (a x) (b x)) :
    μ {x | ¬ HasMatchingTriangleBlock (a x) (b x)} ≤ q ^ m := by
  classical
  have hsub : {x | ¬ HasMatchingTriangleBlock (a x) (b x)} ⊆ ⋂ j, bad j := by
    intro x hx
    rw [Set.mem_iInter]
    intro j
    by_contra hj
    exact hx (hgood x j hj)
  apply (measure_mono hsub).trans
  have hprod := hind.meas_biInter (Finset.univ : Finset (Fin m))
  simp only [Finset.mem_univ, Set.iInter_true] at hprod
  rw [hprod]
  calc
    _ ≤ ∏ _ : Fin m, q := Finset.prod_le_prod' fun j _ => hmass j
    _ = q ^ m := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Uniform positive lower bound on the probability of a good Gaussian block. -/
def gaussianTriangleBlockMass : ℝ := Real.exp (-5) / (200 : ℝ) ^ 16

/-- The four centers for either pair in a Gaussian block. -/
def gaussianTriangleDiskCenters : Fin 4 → ℂ :=
  ![0, 1, 1, matchingTriangleCenter]

/-- Organize the eight coordinates into two pairs. Each pair uses
the order first-spectrum, first-spectrum, second-spectrum, second-spectrum. -/
def matchingTriangleBlockCoordinates (a b : ι → ℂ) (e : Fin 4 ↪ ι)
    (j : Fin 2 × Fin 4) : ℂ :=
  let i := e (if j.1 = 0 then 0 else 2)
  let k := e (if j.1 = 0 then 1 else 3)
  ![a i, a k, b i, b k] j.2

theorem hasMatchingTriangleBlock_of_coordinate_disks (a b : ι → ℂ) (e : Fin 4 ↪ ι)
    (h : ∀ j : Fin 2 × Fin 4,
      ‖matchingTriangleBlockCoordinates a b e j - gaussianTriangleDiskCenters j.2‖ ≤ 1 / 200) :
    HasMatchingTriangleBlock a b := by
  have h₀ := matchingSwapRatio_near_triangleRoot_of_disks
    (a (e 0)) (a (e 1)) (b (e 0)) (b (e 1))
    (by simpa [matchingTriangleBlockCoordinates, gaussianTriangleDiskCenters] using h (0, 0))
    (by simpa [matchingTriangleBlockCoordinates, gaussianTriangleDiskCenters] using h (0, 1))
    (by simpa [matchingTriangleBlockCoordinates, gaussianTriangleDiskCenters] using h (0, 2))
    (by simpa [matchingTriangleBlockCoordinates, gaussianTriangleDiskCenters] using h (0, 3))
  have h₁ := matchingSwapRatio_near_triangleRoot_of_disks
    (a (e 2)) (a (e 3)) (b (e 2)) (b (e 3))
    (by simpa [matchingTriangleBlockCoordinates, gaussianTriangleDiskCenters] using h (1, 0))
    (by simpa [matchingTriangleBlockCoordinates, gaussianTriangleDiskCenters] using h (1, 1))
    (by simpa [matchingTriangleBlockCoordinates, gaussianTriangleDiskCenters] using h (1, 2))
    (by simpa [matchingTriangleBlockCoordinates, gaussianTriangleDiskCenters] using h (1, 3))
  exact ⟨e, h₀.2, h₁.2⟩

private theorem ofReal_prod_nonneg {κ : Type*} (S : Finset κ) (f : κ → ℝ)
    (hf : ∀ j, 0 ≤ f j) : ENNReal.ofReal (∏ j ∈ S, f j) =
      ∏ j ∈ S, ENNReal.ofReal (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, ENNReal.ofReal_one]
  | insert j S hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, ENNReal.ofReal_mul (hf j), ih]

/-- Eight independent variables with the standard complex Gaussian law
have the stated lower bound on the product of the eight disk masses. -/
theorem gaussianTriangleBlock_measure_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Fin 2 × Fin 4 → Ω → ℂ) (hX : ∀ j, Measurable (X j))
    (hLaw : ∀ j, μ.map (X j) = standardComplexGaussian)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    ENNReal.ofReal gaussianTriangleBlockMass ≤
      μ (⋂ j : Fin 2 × Fin 4, (X j) ⁻¹' Metric.closedBall (gaussianTriangleDiskCenters j.2) (1 / 200)) := by
  let r : ℝ := 1 / 200
  let cap : Fin 4 → ℝ := ![0, 1, 1, 1 / 2]
  let W (j : Fin 2 × Fin 4) : ℝ := r ^ 2 * Real.exp (-((cap j.2 + r) ^ 2))
  let E (j : Fin 2 × Fin 4) : Set Ω :=
    (X j) ⁻¹' Metric.closedBall (gaussianTriangleDiskCenters j.2) r
  have hcap (k : Fin 4) : ‖gaussianTriangleDiskCenters k‖ ≤ cap k := by
    have ht := matchingTriangleCenter_data.2.1
    fin_cases k
    · simp [gaussianTriangleDiskCenters, cap]
    · simp [gaussianTriangleDiskCenters, cap]
    · simp [gaussianTriangleDiskCenters, cap]
    · simpa [gaussianTriangleDiskCenters, cap] using ht
  have hW (j) : 0 ≤ W j := mul_nonneg (sq_nonneg r) (Real.exp_pos _).le
  have hmass (j : Fin 2 × Fin 4) : ENNReal.ofReal (W j) ≤ μ (E j) := by
    change ENNReal.ofReal (W j) ≤ μ ((X j) ⁻¹' Metric.closedBall (gaussianTriangleDiskCenters j.2) r)
    rw [← Measure.map_apply (hX j) isClosed_closedBall.measurableSet, hLaw j]
    apply le_trans _ (standardComplexGaussian_closedBall_lower (gaussianTriangleDiskCenters j.2) r
      (by norm_num [r]))
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have hle := add_le_add_right (hcap j.2) r
    have hnon : 0 ≤ ‖gaussianTriangleDiskCenters j.2‖ + r :=
      add_nonneg (norm_nonneg _) (by norm_num [r])
    simpa only [pow_two] using mul_le_mul hle hle hnon (hnon.trans hle)
  have hsum : (∑ j : Fin 2 × Fin 4, -((cap j.2 + r) ^ 2)) = -(22751 : ℝ) / 5000 := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four]
    norm_num [cap, r, Matrix.cons_val_zero', Matrix.cons_val_succ']
  have hrealprod : (∏ j, W j) = r ^ 16 * Real.exp (-(22751 : ℝ) / 5000) := by
    simp only [W, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
      hsum, ← pow_mul, Fintype.card_prod, Fintype.card_fin]
  change ENNReal.ofReal gaussianTriangleBlockMass ≤ μ (⋂ j, E j)
  rw [hind.meas_iInter (s := E) (fun j => ⟨_, isClosed_closedBall.measurableSet, rfl⟩)]
  refine le_trans ?_ (Finset.prod_le_prod' fun j _ => hmass j)
  rw [← ofReal_prod_nonneg Finset.univ W hW, hrealprod]
  apply ENNReal.ofReal_le_ofReal
  have hmassFormula : gaussianTriangleBlockMass = r ^ 16 * Real.exp (-5) := by
    unfold gaussianTriangleBlockMass
    rw [show r ^ 16 = ((200 : ℝ) ^ 16)⁻¹ by simp only [r, one_div, inv_pow], div_eq_mul_inv, mul_comm]
  rw [hmassFormula]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (by positivity)

/-- A sample has a good disk block when all eight coordinate tests hold. -/
def matchingTriangleDiskBlockEvent {Ω : Type*} (a b : Ω → ι → ℂ) (e : Fin 4 ↪ ι) : Set Ω :=
  ⋂ j : Fin 2 × Fin 4,
    (fun x => matchingTriangleBlockCoordinates (a x) (b x) e j) ⁻¹'
      Metric.closedBall (gaussianTriangleDiskCenters j.2) (1 / 200)

private theorem generateFrom_singleton_compl {Ω : Type*} (S : Set Ω) :
    MeasurableSpace.generateFrom {Sᶜ} = MeasurableSpace.generateFrom {S} := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro t ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    exact (MeasurableSpace.GenerateMeasurable.basic S (by simp)).compl
  · apply MeasurableSpace.generateFrom_le
    intro t ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    have hm : MeasurableSet[MeasurableSpace.generateFrom {Sᶜ}] Sᶜ :=
      MeasurableSpace.GenerateMeasurable.basic Sᶜ (by simp)
    simpa only [compl_compl] using hm.compl

private theorem matchingTriangle_diskBlock_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a b : Ω → ι → ℂ) {m : ℕ} (labels : Fin m → (Fin 4 ↪ ι))
    (hmeas : ∀ i j, Measurable (fun x =>
      matchingTriangleBlockCoordinates (a x) (b x) (labels i) j))
    (hind : ProbabilityTheory.iIndepFun (fun (p : Fin m × (Fin 2 × Fin 4)) x =>
      matchingTriangleBlockCoordinates (a x) (b x) (labels p.1) p.2) μ) :
    ProbabilityTheory.iIndepSet (fun i => (matchingTriangleDiskBlockEvent a b (labels i))ᶜ) μ := by
  classical
  let D (p : Fin m × (Fin 2 × Fin 4)) : Set Ω :=
    (fun x => matchingTriangleBlockCoordinates (a x) (b x) (labels p.1) p.2) ⁻¹'
      Metric.closedBall (gaussianTriangleDiskCenters p.2.2) (1 / 200)
  let E (i : Fin m) := matchingTriangleDiskBlockEvent a b (labels i)
  have hm (i : Fin m) : MeasurableSet (E i) :=
    MeasurableSet.iInter (fun j => hmeas i j isClosed_closedBall.measurableSet)
  have hw (i : Fin m) : ProbabilityTheory.iIndepFun (fun j x =>
      matchingTriangleBlockCoordinates (a x) (b x) (labels i) j) μ :=
    ProbabilityTheory.iIndepFun.precomp (g := fun j : Fin 2 × Fin 4 => (i, j))
      (fun j k h => congrArg Prod.snd h) hind
  have hsingle (i : Fin m) : μ (E i) = ∏ j, μ (D (i, j)) :=
    (hw i).meas_iInter (s := fun j => D (i, j))
      (fun j => ⟨Metric.closedBall (gaussianTriangleDiskCenters j.2) (1 / 200),
        isClosed_closedBall.measurableSet, rfl⟩)
  have hs : ProbabilityTheory.iIndepSet E μ := by
    apply (ProbabilityTheory.iIndepSet_iff_meas_biInter hm).mpr
    intro T
    have hset : (⋂ i ∈ T, E i) =
        ⋂ p ∈ T.product (Finset.univ : Finset (Fin 2 × Fin 4)), D p := by
      ext x
      simp only [E, matchingTriangleDiskBlockEvent, Set.mem_iInter, Finset.mem_product,
        Finset.mem_univ, and_true]
      constructor
      · intro h p hp
        exact h p.1 hp p.2
      · intro h i hi j
        exact h (i, j) hi
    rw [hset, hind.meas_biInter (S := T.product Finset.univ) (s := D)
      (fun p _ => ⟨Metric.closedBall (gaussianTriangleDiskCenters p.2.2) (1 / 200),
        isClosed_closedBall.measurableSet, rfl⟩), Finset.prod_product]
    exact Finset.prod_congr rfl (fun i _ => (hsingle i).symm)
  have hg := (ProbabilityTheory.iIndepSet_iff_iIndep E μ).mp hs
  apply (ProbabilityTheory.iIndepSet_iff_iIndep _ μ).mpr
  simpa only [E, generateFrom_singleton_compl] using hg

/-- The no-block estimate for Gaussian coordinate laws and independent
coordinates. Every block uses a separate collection of eight coordinates. -/
theorem gaussianTriangle_no_block_measure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a b : Ω → ι → ℂ)
    {m : ℕ} (labels : Fin m → (Fin 4 ↪ ι))
    (hmeas : ∀ i j, Measurable (fun x =>
      matchingTriangleBlockCoordinates (a x) (b x) (labels i) j))
    (hlaw : ∀ i j, μ.map (fun x =>
      matchingTriangleBlockCoordinates (a x) (b x) (labels i) j) = standardComplexGaussian)
    (hind : ProbabilityTheory.iIndepFun (fun (p : Fin m × (Fin 2 × Fin 4)) x =>
      matchingTriangleBlockCoordinates (a x) (b x) (labels p.1) p.2) μ) :
    μ {x | ¬ HasMatchingTriangleBlock (a x) (b x)} ≤
      ENNReal.ofReal ((1 - gaussianTriangleBlockMass) ^ m) := by
  have hp₀ : 0 ≤ gaussianTriangleBlockMass := by unfold gaussianTriangleBlockMass; positivity
  have hp₁ : gaussianTriangleBlockMass ≤ 1 := by
    unfold gaussianTriangleBlockMass
    apply (div_le_iff₀ (by positivity : 0 < (200 : ℝ) ^ 16)).mpr
    rw [one_mul]
    exact ((Real.exp_le_exp.mpr (by norm_num : (-5 : ℝ) ≤ 0)).trans_eq Real.exp_zero).trans
      (by norm_num)
  rw [ENNReal.ofReal_pow (sub_nonneg.mpr hp₁)]
  apply matchingTriangle_no_block_measure_le μ a b
    (fun i => (matchingTriangleDiskBlockEvent a b (labels i))ᶜ)
    (matchingTriangle_diskBlock_independent μ a b labels hmeas hind)
  · intro i
    have hm : MeasurableSet (matchingTriangleDiskBlockEvent a b (labels i)) :=
      MeasurableSet.iInter (fun j => hmeas i j isClosed_closedBall.measurableSet)
    have hp := gaussianTriangleBlock_measure_ge μ
      (fun j x => matchingTriangleBlockCoordinates (a x) (b x) (labels i) j)
      (hmeas i) (hlaw i)
      (ProbabilityTheory.iIndepFun.precomp (g := fun j : Fin 2 × Fin 4 => (i, j))
        (fun j k h => congrArg Prod.snd h) hind)
    rw [measure_compl hm (measure_ne_top μ _), measure_univ, ENNReal.ofReal_sub 1 hp₀,
      ENNReal.ofReal_one]
    exact tsub_le_tsub_left hp 1
  · intro x i hx
    have hi : x ∈ matchingTriangleDiskBlockEvent a b (labels i) := by
      classical
      simpa only [Set.mem_compl_iff, not_not] using hx
    apply hasMatchingTriangleBlock_of_coordinate_disks (a x) (b x) (labels i)
    intro j
    have hj := Set.mem_iInter.mp hi j
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hj

private def consecutiveGaussianBlock (n : ℕ) (i : Fin (n / 4)) : Fin 4 ↪ Fin n where
  toFun j := ⟨4 * i.val + j.val, by have hi := i.isLt; have hj := j.isLt; omega⟩
  inj' j k h := by
    apply Fin.ext
    have he : 4 * i.val + j.val = 4 * i.val + k.val := congrArg Fin.val h
    omega

private def gaussianBlockCoordinateIndex (j : Fin 2 × Fin 4) : Fin 2 × Fin 4 :=
  let l : Fin 4 := if j.1 = 0 then 0 else 2
  let r : Fin 4 := if j.1 = 0 then 1 else 3
  ![(0, l), (0, r), (1, l), (1, r)] j.2

/-- Consecutive four-index blocks are disjoint. Thus a single independent
Gaussian family on the two spectra gives the no-block estimate. -/
theorem gaussianTriangle_no_block_measure_le_of_iid_spectra {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin 2 × Fin n → Ω → ℂ) (hmeas : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = standardComplexGaussian)
    (hind : ProbabilityTheory.iIndepFun X μ) :
    μ {x | ¬ HasMatchingTriangleBlock (fun j => X (0, j) x) (fun j => X (1, j) x)} ≤
      ENNReal.ofReal ((1 - gaussianTriangleBlockMass) ^ (n / 4)) := by
  let e := consecutiveGaussianBlock n
  let code := gaussianBlockCoordinateIndex
  let g (p : Fin (n / 4) × (Fin 2 × Fin 4)) : Fin 2 × Fin n :=
    ((code p.2).1, e p.1 (code p.2).2)
  have hcode : Function.Injective code := by
    change Function.Injective gaussianBlockCoordinateIndex
    decide
  have hinj : Function.Injective g := by
    intro x y he
    have h₀ : (code x.2).1 = (code y.2).1 := congrArg Prod.fst he
    have hv : 4 * x.1.val + (code x.2).2.val = 4 * y.1.val + (code y.2).2.val :=
      congrArg (fun p : Fin 2 × Fin n => p.2.val) he
    have hi : x.1 = y.1 := by
      apply Fin.ext
      have hx := (code x.2).2.isLt
      have hy := (code y.2).2.isLt
      omega
    have hj : (code x.2).2 = (code y.2).2 := by
      apply Fin.ext
      rw [hi] at hv
      omega
    exact Prod.ext hi (hcode (Prod.ext h₀ hj))
  have hcoord (i : Fin (n / 4)) (j : Fin 2 × Fin 4) :
      (fun x => matchingTriangleBlockCoordinates (fun k => X (0, k) x)
        (fun k => X (1, k) x) (e i) j) = X (g (i, j)) := by
    obtain ⟨j, k⟩ := j
    fin_cases j <;> fin_cases k <;>
      simp [matchingTriangleBlockCoordinates, g, code, gaussianBlockCoordinateIndex]
  apply gaussianTriangle_no_block_measure_le μ _ _ e
  · intro i j
    rw [hcoord]
    exact hmeas (g (i, j))
  · intro i j
    rw [hcoord]
    exact hlaw (g (i, j))
  · have he : (fun (p : Fin (n / 4) × (Fin 2 × Fin 4)) x =>
        matchingTriangleBlockCoordinates (fun k => X (0, k) x)
          (fun k => X (1, k) x) (e p.1) p.2) = (fun p => X (g p)) :=
        funext fun p => hcoord p.1 p.2
    rw [he]
    exact ProbabilityTheory.iIndepFun.precomp hinj hind

/-- The negative moment used to estimate the lower tail of the identity
matching product. A zero sum has infinite negative moment. -/
def matchingNegativeMoment (z : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖z‖) ^ (-(1 / 10 : ℝ))

/-- A uniform bound on the negative moment of each independent summand
pair gives the exponential lower tail of the identity matching product. -/
theorem matchingProduct_lower_tail_of_independent_negative_moments {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ) (a b : Ω → Fin n → ℂ)
    (hmeas : ∀ j, Measurable (fun x => matchingNegativeMoment (a x j + b x j)))
    (hind : ProbabilityTheory.iIndepFun (fun (j : Fin n) x =>
      matchingNegativeMoment (a x j + b x j)) μ)
    (hmoment : ∀ j, (∫⁻ x, matchingNegativeMoment (a x j + b x j) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(7 / 2000 : ℝ)))) :
    μ {x | ‖matchingProduct (a x) (b x) 1‖ < Real.exp ((n : ℝ) / 100)} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 400)) := by
  let R := Real.exp ((n : ℝ) / 100)
  let T := Real.exp (-(n : ℝ) / 1000)
  let F (j : Fin n) (x : Ω) := matchingNegativeMoment (a x j + b x j)
  have hF (x : Ω) : matchingNegativeMoment (matchingProduct (a x) (b x) 1) =
      ∏ j, F j x := by
    simp only [matchingNegativeMoment, matchingProduct, Equiv.Perm.one_apply, norm_prod]
    rw [ofReal_prod_nonneg Finset.univ (fun j => ‖a x j + b x j‖) (fun _ => norm_nonneg _),
      ENNReal.prod_rpow_of_ne_top (fun _ _ => ENNReal.ofReal_ne_top)] <;> rfl
  have hthreshold : ENNReal.ofReal T = (ENNReal.ofReal R) ^ (-(1 / 10 : ℝ)) := by
    dsimp only [R, T]
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    ring
  have hsub : {x | ‖matchingProduct (a x) (b x) 1‖ < R} ⊆
      {x | ENNReal.ofReal T ≤ ∏ j, F j x} := by
    intro x hx
    change ‖matchingProduct (a x) (b x) 1‖ < R at hx
    change ENNReal.ofReal T ≤ ∏ j, F j x
    rw [hthreshold, ← hF x, matchingNegativeMoment, ENNReal.rpow_neg, ENNReal.rpow_neg,
      ENNReal.inv_le_inv]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx.le) (by norm_num)
  have hT : 0 < T := Real.exp_pos _
  have hexp : (∫⁻ x, ∏ j, F j x ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * 7 / 2000)) := by
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ F hind hmeas]
    have h := Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin n))) (fun j _ => hmoment j)
    refine h.trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 2
    ring
  have htail := (measure_mono hsub).trans (meas_ge_le_lintegral_div
    (Finset.univ.aemeasurable_prod' (fun j _ => (hmeas j).aemeasurable))
    ((ENNReal.ofReal_pos.mpr hT).ne') ENNReal.ofReal_ne_top)
  refine htail.trans ((ENNReal.div_le_div_right hexp (ENNReal.ofReal T)).trans_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos hT, show T = Real.exp (-(n : ℝ) / 1000) from rfl,
    ← Real.exp_sub, show -(n : ℝ) * 7 / 2000 - (-(n : ℝ) / 1000) = -(n : ℝ) / 400 by ring]

/-- Markov's inequality gives the determinant term from the second moment. -/
theorem determinant_second_moment_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (a b : Ω → Fin n → ℂ) (U : Ω → Matrix (Fin n) (Fin n) ℂ)
    (hmeas : AEMeasurable (fun x =>
      ENNReal.ofReal (‖determinantValue (a x) (b x) (U x)‖ ^ 2)) μ)
    (hmoment : (∫⁻ x, ENNReal.ofReal (‖determinantValue (a x) (b x) (U x)‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal (((n : ℝ) + 2) * ((n : ℝ) + 3) / 6)) :
    μ {x | Real.exp ((n : ℝ) / 100) / 4 < ‖determinantValue (a x) (b x) (U x)‖} ≤
      ENNReal.ofReal ((8 / 3) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * Real.exp (-(n : ℝ) / 50)) := by
  let T := Real.exp ((n : ℝ) / 100) / 4
  have hT : 0 < T := div_pos (Real.exp_pos _) (by norm_num)
  have hT2 : 0 < T ^ 2 := by positivity
  have hε : ENNReal.ofReal (T ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hT2).ne'
  have hsub :
      {x | T < ‖determinantValue (a x) (b x) (U x)‖} ⊆
        {x | ENNReal.ofReal (T ^ 2) ≤
          ENNReal.ofReal (‖determinantValue (a x) (b x) (U x)‖ ^ 2)} := by
    intro x hx
    change T < ‖determinantValue (a x) (b x) (U x)‖ at hx
    apply ENNReal.ofReal_le_ofReal
    simpa only [pow_two] using mul_le_mul hx.le hx.le hT.le (norm_nonneg _)
  have htail := (measure_mono hsub).trans
    (meas_ge_le_lintegral_div hmeas hε ENNReal.ofReal_ne_top)
  apply htail.trans
  refine (ENNReal.div_le_div_right hmoment (ENNReal.ofReal (T ^ 2))).trans_eq ?_
  rw [← ENNReal.ofReal_div_of_pos hT2]
  congr 1
  have hsq : T ^ 2 = Real.exp ((n : ℝ) / 50) / 16 := by
    dsimp only [T]
    rw [div_pow, pow_two (Real.exp _), ← Real.exp_add,
      show (n : ℝ) / 100 + (n : ℝ) / 100 = (n : ℝ) / 50 by ring]
    norm_num
  rw [hsq, show -(n : ℝ) / 50 = -((n : ℝ) / 50) by ring, Real.exp_neg]
  field_simp [(Real.exp_pos ((n : ℝ) / 50)).ne'] <;> ring

/-- The numerical failure bound follows from the block estimate, the
lower tail of the identity product, and the determinant second moment.
This theorem does not assume independence between those three events. -/
theorem gaussianHaar_failure_bound_of_estimates {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (a b : Ω → Fin n → ℂ) (U : Ω → Matrix (Fin n) (Fin n) ℂ)
    (hblock : μ {x | ¬ HasMatchingTriangleBlock (a x) (b x)} ≤
      ENNReal.ofReal ((1 - gaussianTriangleBlockMass) ^ (n / 4)))
    (hbaseline : μ {x | ‖matchingProduct (a x) (b x) 1‖ < Real.exp ((n : ℝ) / 100)} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 400)))
    (hmeas : AEMeasurable (fun x =>
      ENNReal.ofReal (‖determinantValue (a x) (b x) (U x)‖ ^ 2)) μ)
    (hmoment : (∫⁻ x, ENNReal.ofReal (‖determinantValue (a x) (b x) (U x)‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal (((n : ℝ) + 2) * ((n : ℝ) + 3) / 6)) :
    μ {x | ¬ Holds (a x) (b x) (U x)} ≤
      ENNReal.ofReal ((1 - gaussianTriangleBlockMass) ^ (n / 4)) +
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 400)) +
        ENNReal.ofReal ((8 / 3) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * Real.exp (-(n : ℝ) / 50)) :=
  (matchingTriangle_failure_measure_le μ a b U (Real.exp ((n : ℝ) / 100))).trans
    (add_le_add (add_le_add hblock hbaseline) (determinant_second_moment_tail μ n a b U hmeas hmoment))

end

end MOC
