import MOC.GeneralizedSpectralCircles
import MOC.ProjectiveTransport

/-! A finite spectrum on a circle or line has a real fractional-linear chart.
The choice of chart depends only on the first spectrum. -/

open scoped ComplexConjugate

namespace MOC

private theorem chart_im_zero (d z : ℂ) (s : ℝ) (hz : (d * z).re = s) :
    ((-Complex.I * d) * z + (s : ℂ) * Complex.I).im = 0 := by
  rw [show (-Complex.I * d) * z = -(Complex.I * (d * z)) by ring]
  simp [Complex.I_mul_im, Complex.mul_im, hz]

private abbrev RealChart {ι : Type*} (a : ι → ℂ) : Prop :=
  ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧ (∀ i, γ * a i + δ ≠ 0) ∧
    ∀ i, (fractionalMap α β γ δ (a i)).im = 0

set_option maxHeartbeats 1000000 in
private theorem realChart_of_circle {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (o : ℂ) (r : ℝ) (ha : ∀ i, Complex.normSq (a i - o) = r) :
    RealChart a := by
  classical
  rcases isEmpty_or_nonempty ι with he | hne
  · letI := he
    exact ⟨1, 0, 0, 1, by simp, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  by_cases hr : r = 0
  · refine ⟨1, -o, 0, 1, by simp, by simp, fun i => ?_⟩
    have h := congrArg Complex.im (Complex.normSq_eq_zero.mp ((ha i).trans hr))
    simpa [fractionalMap, sub_eq_add_neg] using h
  obtain ⟨i₀⟩ := hne
  let d := a i₀ - o
  have hd : d ≠ 0 := by
    intro h
    exact hr ((ha i₀).symm.trans (by simp [show a i₀ - o = 0 from h]))
  let ray (t : ℝ) := o + d * circleRotation t
  have hinj : Function.Injective ray := by
    intro t v h
    change o + d * circleRotation t = o + d * circleRotation v at h
    exact circleRotation_injective (mul_left_cancel₀ hd (add_left_cancel h))
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := (Set.infinite_range_of_injective hinj).exists_not_mem_finset
    (Finset.univ.image a)
  let p := ray t
  have hp (i : ι) : a i - p ≠ 0 := fun h =>
    ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, sub_eq_zero.mp h⟩)
  have hrad : Complex.normSq (p - o) = r := by
    simpa only [p, ray, add_sub_cancel_left, Complex.normSq_mul, circleRotation_normSq, mul_one]
      using ha i₀
  let u := o - p
  have hu : Complex.normSq u = r := by
    simpa only [show u = -(p - o) by dsimp [u]; ring, Complex.normSq_neg] using hrad
  have hu₀ : u ≠ 0 := fun h => hr (hu.symm.trans (by simp [h]))
  let k := -Complex.I * u
  let c : ℂ := ((1 / 2 : ℝ) : ℂ) * Complex.I
  have hk : k ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hu₀
  refine ⟨c, k - c * p, 1, -p, ?_, ?_, ?_⟩
  · rw [show c * -p - (k - c * p) * 1 = -k by ring]
    exact neg_ne_zero.mpr hk
  · intro i
    simpa only [one_mul, ← sub_eq_add_neg] using hp i
  · intro i
    have hline : (u * (a i - p)⁻¹).re = 1 / 2 := by
      apply re_mul_inv_of_circle u (a i - p) (hp i)
      rw [show a i - p - u = a i - o by dsimp [u]; ring, ha i, hu]
    have hf : fractionalMap c (k - c * p) 1 (-p) (a i) = k * (a i - p)⁻¹ + c := by
      unfold fractionalMap
      rw [one_mul, ← sub_eq_add_neg]
      field_simp [hp i] <;> ring
    rw [hf]
    exact chart_im_zero u _ _ hline

/-- Choose an invertible chart with no pole on the given spectrum. The chart sends every entry to the real line. -/
theorem exists_real_fractional_chart {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (hc : SpectrumOnGeneralizedCircle a) :
    ∃ α β γ δ : ℂ, α * δ - β * γ ≠ 0 ∧ (∀ i, γ * a i + δ ≠ 0) ∧
      ∀ i, (fractionalMap α β γ δ (a i)).im = 0 := by
  obtain ⟨q, u, v, c, hn, ha⟩ := hc
  change ∀ i, q * Complex.normSq (a i) - 2 * (u * (a i).re + v * (a i).im) + c = 0 at ha
  by_cases hq : q = 0
  · let d : ℂ := ⟨u, -v⟩
    have hd : d ≠ 0 := by
      intro h
      have hu : u = 0 := congrArg Complex.re h
      have hv : v = 0 := by simpa [d] using congrArg Complex.im h
      simp [hq, hu, hv] at hn
    refine ⟨-Complex.I * d, ((c / 2 : ℝ) : ℂ) * Complex.I, 0, 1, ?_, by simp, ?_⟩
    · simpa using mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hd
    · intro i
      simp only [fractionalMap, zero_mul, zero_add, div_one]
      apply chart_im_zero
      have h := ha i
      simp only [hq, zero_mul, zero_sub] at h
      change u * (a i).re - -v * (a i).im = c / 2
      linarith
  · let o : ℂ := ⟨u / q, v / q⟩
    apply realChart_of_circle a o (Complex.normSq o - c / q)
    intro i
    have h := ha i
    have he : Complex.normSq (a i) = (2 * (u * (a i).re + v * (a i).im) - c) / q := by
      apply (eq_div_iff hq).mpr
      linarith
    have hdot : (a i * conj o).re = (u * (a i).re + v * (a i).im) / q := by
      change (a i).re * (u / q) - (a i).im * (-(v / q)) = _
      field_simp [hq] <;> ring
    rw [Complex.normSq_sub, he, hdot]
    ring

end MOC
