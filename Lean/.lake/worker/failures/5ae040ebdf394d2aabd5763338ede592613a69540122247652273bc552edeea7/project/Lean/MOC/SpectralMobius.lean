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
      div_eq_mul_inv, mul_inv_rev, mul_comm]
  have hp : 0 < E ^ Fintype.card ι * Complex.normSq Δ := mul_pos (pow_pos he _) hΔpos
  have hsq := pow_le_pow_left₀ hm.le hmbound 2
  rw [hmsq, one_pow] at hsq
  exact (inv_le_one₀ hp).mp hsq

end

end MOC
