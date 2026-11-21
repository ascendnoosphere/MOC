import MOC.Geometry
import MOC.SpectralStationarity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Data.Real.Sqrt

/-! The common fractional-linear change of spectra, and the constraints it
imposes when a positive determinant support gap is maximized on the spectral ball. -/

open BigOperators Matrix Filter
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Möbius transformation fixing zero. The two spectra use opposite parameters. -/
def mobiusSpectrum (t : ℂ) (a : ι → ℂ) (i : ι) : ℂ :=
  a i / (1 - t * a i)

/-- The common denominator introduced in every matching product. -/
def mobiusDenominator (a b : ι → ℂ) (t : ℂ) : ℂ :=
  (∏ i, (1 - t * a i)) * ∏ j, (1 + t * b j)

omit [DecidableEq ι] in
theorem matchingProduct_mobius (a b : ι → ℂ) (t : ℂ) (σ : Equiv.Perm ι)
    (ha : ∀ i, 1 - t * a i ≠ 0) (hb : ∀ j, 1 + t * b j ≠ 0) :
    matchingProduct (mobiusSpectrum t a) (mobiusSpectrum (-t) b) σ =
      matchingProduct a b σ / mobiusDenominator a b t := by
  have hterm (i j : ι) : mobiusSpectrum t a i + mobiusSpectrum (-t) b j =
      (a i + b j) / ((1 - t * a i) * (1 + t * b j)) := by
    simp only [mobiusSpectrum, neg_mul, sub_neg_eq_add]
    field_simp [ha i, hb j]
    ring
  unfold matchingProduct mobiusDenominator
  simp_rw [hterm, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [Equiv.prod_comp σ (fun i => 1 - t * a i)]

theorem determinantValue_mobius (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (t : ℂ) (ha : ∀ i, 1 - t * a i ≠ 0) (hb : ∀ j, 1 + t * b j ≠ 0) :
    determinantValue (mobiusSpectrum t a) (mobiusSpectrum (-t) b) U =
      determinantValue a b U / mobiusDenominator a b t := by
  rw [← signed_determinant (mobiusSpectrum t a) (mobiusSpectrum (-t) b) U hU,
    ← signed_determinant a b U hU, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  rw [matchingProduct_mobius a b t σ ha hb, mul_div_assoc]

/-- An energy-normalized positive support gap maximum minimizes the powered
spectral energy times the squared common denominator along its Möbius changes.
The support direction is allowed to rotate when the denominator changes phase. -/
theorem spectralEnergy_mobius_bound (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (η : ℂ) (hη : Complex.normSq η = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ σ : Equiv.Perm ι,
      g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hmax : ∀ (c d : ι → ℂ) (k : ℂ), spectralEnergy c d ≤ 1 → Complex.normSq k = 1 →
      ∃ σ : Equiv.Perm ι, (k * (determinantValue c d U - matchingProduct c d σ)).re ≤ g)
    (t : ℂ) (ha : ∀ i, 1 - t * a i ≠ 0) (hb : ∀ j, 1 + t * b j ≠ 0)
    (he : 0 < spectralEnergy (mobiusSpectrum t a) (mobiusSpectrum (-t) b)) :
    1 ≤ spectralEnergy (mobiusSpectrum t a) (mobiusSpectrum (-t) b) ^ Fintype.card ι *
      Complex.normSq (mobiusDenominator a b t) := by
  let c := mobiusSpectrum t a
  let d := mobiusSpectrum (-t) b
  let E := spectralEnergy c d
  let Δ := mobiusDenominator a b t
  let r := (Real.sqrt E)⁻¹
  let s := Real.sqrt (Complex.normSq Δ)
  let m := r ^ Fintype.card ι / s
  let k : ℂ := η * Δ / (s : ℂ)
  have hΔ : Δ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ha i)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hb j)
  have hΔpos := Complex.normSq_pos.mpr hΔ
  have hs : 0 < s := Real.sqrt_pos_of_pos hΔpos
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos_of_pos he)
  have hm : 0 < m := div_pos (pow_pos hr _) hs
  have hrsq : r ^ 2 = E⁻¹ := by rw [show r = (Real.sqrt E)⁻¹ by rfl, inv_pow, Real.sq_sqrt he.le]
  have hssq : s ^ 2 = Complex.normSq Δ := Real.sq_sqrt hΔpos.le
  have hk : Complex.normSq k = 1 := by
    change Complex.normSq (η * Δ / (s : ℂ)) = 1
    rw [map_div₀, Complex.normSq_mul, hη, one_mul, Complex.normSq_ofReal, ← sq, hssq,
      div_self hΔpos.ne']
  have hscale : spectralEnergy (fun i => (r : ℂ) * c i) (fun i => (r : ℂ) * d i) ≤ 1 := by
    rw [spectralEnergy_scale, hrsq, inv_mul_cancel₀ he.ne']
  obtain ⟨σ, hσ⟩ := hmax _ _ k hscale hk
  rw [determinantValue_scale, matchingProduct_scale, determinantValue_mobius a b U hU t ha hb,
    matchingProduct_mobius a b t σ ha hb] at hσ
  have hrewrite :
      k * ((r : ℂ) ^ Fintype.card ι * (determinantValue a b U / Δ) -
        (r : ℂ) ^ Fintype.card ι * (matchingProduct a b σ / Δ)) =
      (m : ℂ) * (η * (determinantValue a b U - matchingProduct a b σ)) := by
    dsimp only [k, m]
    push_cast
    field_simp [hΔ, Complex.ofReal_ne_zero.mpr hs.ne']
    ring
  rw [hrewrite, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hσ
  have hmbound : m ≤ 1 := by
    by_contra! hbad
    have h := mul_le_mul_of_nonneg_left (hgap σ) hm.le
    exact (not_lt_of_ge (h.trans hσ)) (by simpa only [one_mul] using mul_lt_mul_of_pos_right hbad hg)
  have hmsq : m ^ 2 = (E ^ Fintype.card ι * Complex.normSq Δ)⁻¹ := by
    change (r ^ Fintype.card ι / s) ^ 2 = _
    rw [div_pow, ← pow_mul, Nat.mul_comm (Fintype.card ι) 2, pow_mul, hrsq, inv_pow, hssq,
      div_eq_mul_inv, _root_.mul_inv_rev, mul_comm]
  have hp : 0 < E ^ Fintype.card ι * Complex.normSq Δ := mul_pos (pow_pos he _) hΔpos
  have hsq := pow_le_pow_left₀ hm.le hmbound 2
  rw [hmsq, one_pow] at hsq
  exact (inv_le_one₀ hp).mp hsq

private theorem hasDerivAt_complexPath (p x : ℂ) :
    HasDerivAt (fun r : ℝ => ((r : ℂ) * p) * x) (p * x) 0 := by
  have h : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 0 := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  simpa only [one_mul] using (h.mul_const p).mul_const x

private theorem hasDerivAt_normSq_path {f : ℝ → ℂ} {v : ℂ} {r : ℝ}
    (h : HasDerivAt f v r) :
    HasDerivAt (fun s => Complex.normSq (f s)) (2 * (v * star (f r)).re) r := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h
  have he : v.re * (f r).re + (f r).re * v.re +
      (v.im * (f r).im + (f r).im * v.im) = 2 * (v * star (f r)).re := by
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.normSq_apply, he] using (hre.mul hre).add (him.mul him)

private theorem hasDerivAt_mobius_line (p x : ℂ) :
    HasDerivAt (fun r : ℝ => x / (1 - ((r : ℂ) * p) * x)) (x * (p * x)) 0 := by
  have h : HasDerivAt (fun z : ℂ => 1 - (z * p) * x) (-(p * x)) 0 := by
    simpa only [one_mul] using ((((hasDerivAt_id (0 : ℂ)).mul_const p).mul_const x).const_sub 1)
  have hd : HasDerivAt (fun z : ℂ => x / (1 - (z * p) * x)) (x * (p * x))
      ((0 : ℝ) : ℂ) := by
    have hh := (hasDerivAt_const (0 : ℂ) x).div h (by simp)
    simpa only [Complex.ofReal_zero, zero_mul, sub_zero, one_pow, mul_neg, sub_neg_eq_add,
      zero_add, div_one] using hh
  exact hd.comp_ofReal

private theorem hasDerivAt_mobius_energy_side (a : ι → ℂ) (p : ℂ) :
    HasDerivAt (fun r : ℝ => ∑ i, Complex.normSq (mobiusSpectrum ((r : ℂ) * p) a i))
      (2 * (p * ∑ i, (Complex.normSq (a i) : ℂ) * a i).re) 0 := by
  have hi (i : ι) :
      HasDerivAt (fun r : ℝ => Complex.normSq (mobiusSpectrum ((r : ℂ) * p) a i))
        (2 * (p * ((Complex.normSq (a i) : ℂ) * a i)).re) 0 := by
    have hd := hasDerivAt_normSq_path (hasDerivAt_mobius_line p (a i))
    have he : (a i * (p * a i)) * star (a i) = p * ((Complex.normSq (a i) : ℂ) * a i) := by
      rw [← Complex.mul_conj (a i)]
      change (a i * (p * a i)) * star (a i) = p * ((a i * star (a i)) * a i)
      ring
    simpa only [mobiusSpectrum, Complex.ofReal_zero, zero_mul, sub_zero, div_one, he] using hd
  simpa only [Finset.mul_sum, Complex.re_sum] using HasDerivAt.sum (u := Finset.univ) (fun i _ => hi i)

private theorem hasDerivAt_mobius_energy (a b : ι → ℂ) (p : ℂ) :
    HasDerivAt (fun r : ℝ => spectralEnergy (mobiusSpectrum ((r : ℂ) * p) a)
      (mobiusSpectrum (-((r : ℂ) * p)) b))
      (2 * (p * ((∑ i, (Complex.normSq (a i) : ℂ) * a i) -
        ∑ i, (Complex.normSq (b i) : ℂ) * b i)).re) 0 := by
  have h := (hasDerivAt_mobius_energy_side a p).add (hasDerivAt_mobius_energy_side b (-p))
  have he (x y : ℂ) : 2 * (p * x).re + 2 * ((-p) * y).re = 2 * (p * (x - y)).re := by
    simp only [mul_sub, neg_mul, Complex.sub_re, Complex.neg_re]
    ring
  simpa only [spectralEnergy, mul_neg, he] using h

private theorem hasDerivAt_mobius_denominator (a b : ι → ℂ) (p : ℂ)
    (htrace : (∑ i, a i) = ∑ i, b i) :
    HasDerivAt (fun r : ℝ => mobiusDenominator a b ((r : ℂ) * p)) 0 0 := by
  have ha := HasDerivAt.finset_prod (u := Finset.univ)
    (fun i _ => (hasDerivAt_complexPath p (a i)).const_sub 1)
  have hb := HasDerivAt.finset_prod (u := Finset.univ)
    (fun i _ => (hasDerivAt_complexPath p (b i)).const_add 1)
  have he : (∑ i, -(p * a i)) + ∑ i, p * b i = 0 := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htrace, neg_add_cancel]
  simpa only [mobiusDenominator, Finset.prod_apply, Complex.ofReal_zero, zero_mul, sub_zero,
    add_zero, Finset.prod_const_one, one_smul, mul_one, one_mul, he] using ha.mul hb

/-- At a positive gap maximum on the spectral unit sphere, the two
norm-squared-weighted first moments agree. -/
theorem equal_cubic_moments_of_positive_gap_maximizer [Nonempty ι]
    (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ)
    (hη : Complex.normSq η = 1) (henergy : spectralEnergy a b = 1) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ σ : Equiv.Perm ι,
      g ≤ (η * (determinantValue a b U - matchingProduct a b σ)).re)
    (hmax : ∀ (c d : ι → ℂ) (k : ℂ), spectralEnergy c d ≤ 1 → Complex.normSq k = 1 →
      ∃ σ : Equiv.Perm ι, (k * (determinantValue c d U - matchingProduct c d σ)).re ≤ g) :
    (∑ i, (Complex.normSq (a i) : ℂ) * a i) = ∑ i, (Complex.normSq (b i) : ℂ) * b i := by
  have htrace := equal_trace_of_positive_support_gap_maximizer a b U hU η g
    henergy.le hg hgap fun c d hcd => hmax c d η hcd hη
  let s : ℂ := (∑ i, (Complex.normSq (a i) : ℂ) * a i) - ∑ i, (Complex.normSq (b i) : ℂ) * b i
  have hz (p : ℂ) : (p * s).re = 0 := by
    let E (r : ℝ) := spectralEnergy (mobiusSpectrum ((r : ℂ) * p) a)
      (mobiusSpectrum (-((r : ℂ) * p)) b)
    let D (r : ℝ) := mobiusDenominator a b ((r : ℂ) * p)
    let f (r : ℝ) := E r ^ Fintype.card ι * Complex.normSq (D r)
    have hE₀ : E 0 = 1 := by simp [E, mobiusSpectrum, henergy]
    have hD₀ : D 0 = 1 := by simp [D, mobiusDenominator]
    have hf₀ : f 0 = 1 := by simp [f, hE₀, hD₀]
    have hE : HasDerivAt E (2 * (p * s).re) 0 := hasDerivAt_mobius_energy a b p
    have hD : HasDerivAt D 0 0 := hasDerivAt_mobius_denominator a b p htrace
    have hd : HasDerivAt (fun r => Complex.normSq (D r)) 0 0 := by
      simpa only [zero_mul, Complex.zero_re, mul_zero] using hasDerivAt_normSq_path hD
    have hf : HasDerivAt f ((Fintype.card ι : ℝ) * (2 * (p * s).re)) 0 := by
      simpa only [f, hE₀, hD₀, one_pow, Complex.normSq_one, mul_one, mul_zero, add_zero] using
        (hE.pow (n := Fintype.card ι)).mul hd
    have ha : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), ∀ i, 1 - ((r : ℂ) * p) * a i ≠ 0 := by
      apply Filter.eventually_all.mpr
      intro i
      exact ((hasDerivAt_complexPath p (a i)).const_sub 1).continuousAt.eventually_ne (by simp)
    have hb : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), ∀ i, 1 + ((r : ℂ) * p) * b i ≠ 0 := by
      apply Filter.eventually_all.mpr
      intro i
      exact ((hasDerivAt_complexPath p (b i)).const_add 1).continuousAt.eventually_ne (by simp)
    have hEpos : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < E r :=
      hE.continuousAt.eventually_mem (Ioi_mem_nhds (by rw [hE₀]; exact zero_lt_one))
    have hmin : IsLocalMin f 0 := by
      filter_upwards [ha, hb, hEpos] with r hra hrb hrE
      rw [hf₀]
      exact spectralEnergy_mobius_bound a b U hU η hη hg hgap hmax ((r : ℂ) * p) hra hrb hrE
    have hzero := hmin.hasDerivAt_eq_zero hf
    have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hn)).resolve_left two_ne_zero
  apply sub_eq_zero.mp
  change s = 0
  apply Complex.ext
  · simpa using hz 1
  · simpa [Complex.mul_re] using hz Complex.I

end

end MOC
