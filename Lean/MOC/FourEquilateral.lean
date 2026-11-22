import MOC.FourCoincidence
import MOC.GeneralizedSpectralCircles
import Mathlib.Tactic.LinearCombination

/-! Order-four inclusion for a pair of equilateral triples with freely chosen fourth points. -/

open Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

private def equilateralHeight : ℝ := Real.sqrt 3 / 2

private theorem equilateralHeight_mul_self : equilateralHeight * equilateralHeight = 3 / 4 := by
  calc
    equilateralHeight * equilateralHeight = Real.sqrt 3 ^ 2 / 4 := by
      unfold equilateralHeight
      ring
    _ = 3 / 4 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private def unitEquilateralSpectrum (z : ℂ) : Fin 4 → ℂ :=
  ![1, ⟨-(1 / 2), equilateralHeight⟩, ⟨-(1 / 2), -equilateralHeight⟩, z]

/-- An equilateral triple centered at `c`, with complex scale `d` and fourth point `c + d * z`. -/
def equilateralSpectrum (c d z : ℂ) (i : Fin 4) : ℂ :=
  c + d * unitEquilateralSpectrum z i

/-- The first three entries have equal squared edge lengths, positive for `d ≠ 0`. -/
theorem equilateralSpectrum_edge_lengths (c d z : ℂ) :
    let a := equilateralSpectrum c d z
    Complex.normSq (a 0 - a 1) = 3 * Complex.normSq d ∧
      Complex.normSq (a 1 - a 2) = 3 * Complex.normSq d ∧
      Complex.normSq (a 2 - a 0) = 3 * Complex.normSq d := by
  have hscale (i j : Fin 4) :
      Complex.normSq (equilateralSpectrum c d z i - equilateralSpectrum c d z j) =
        Complex.normSq d * Complex.normSq (unitEquilateralSpectrum z i - unitEquilateralSpectrum z j) := by
    simp only [equilateralSpectrum, ← Complex.normSq_mul]
    congr 1
    ring
  have h01 : Complex.normSq (unitEquilateralSpectrum z 0 - unitEquilateralSpectrum z 1) = 3 := by
    change (1 - -(1 / 2) : ℝ) * (1 - -(1 / 2)) +
      (0 - equilateralHeight) * (0 - equilateralHeight) = 3
    linear_combination equilateralHeight_mul_self
  have h12 : Complex.normSq (unitEquilateralSpectrum z 1 - unitEquilateralSpectrum z 2) = 3 := by
    change (-(1 / 2) - -(1 / 2) : ℝ) * (-(1 / 2) - -(1 / 2)) +
      (equilateralHeight - -equilateralHeight) * (equilateralHeight - -equilateralHeight) = 3
    linear_combination 4 * equilateralHeight_mul_self
  have h20 : Complex.normSq (unitEquilateralSpectrum z 2 - unitEquilateralSpectrum z 0) = 3 := by
    change (-(1 / 2) - 1 : ℝ) * (-(1 / 2) - 1) +
      (-equilateralHeight - 0) * (-equilateralHeight - 0) = 3
    linear_combination equilateralHeight_mul_self
  refine ⟨?_, ?_, ?_⟩
  · rw [hscale, h01, mul_comm]
  · rw [hscale, h12, mul_comm]
  · rw [hscale, h20, mul_comm]

private theorem unitEquilateralSpectrum_not_on_generalizedCircle (z : ℂ)
    (hz : Complex.normSq z ≠ 1) : ¬ SpectrumOnGeneralizedCircle (unitEquilateralSpectrum z) := by
  rintro ⟨q, u, v, k, hnonzero, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  change q * (1 * 1 + 0 * 0) - 2 * (u * 1 + v * 0) + k = 0 at h0
  change q * ((-(1 / 2)) * (-(1 / 2)) + equilateralHeight * equilateralHeight) -
    2 * (u * (-(1 / 2)) + v * equilateralHeight) + k = 0 at h1
  change q * ((-(1 / 2)) * (-(1 / 2)) + (-equilateralHeight) * (-equilateralHeight)) -
    2 * (u * (-(1 / 2)) + v * (-equilateralHeight)) + k = 0 at h2
  change q * Complex.normSq z - 2 * (u * z.re + v * z.im) + k = 0 at h3
  simp only [neg_mul_neg, equilateralHeight_mul_self] at h1 h2
  have hvprod : v * equilateralHeight = 0 := by linear_combination (h2 - h1) / 4
  have hh : equilateralHeight ≠ 0 :=
    (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)).ne'
  have hv : v = 0 := (mul_eq_zero.mp hvprod).resolve_right hh
  have hu : u = 0 := by
    rw [hvprod, add_zero] at h1
    linear_combination (h1 - h0) / 3
  have hk : k = -q := by
    rw [hu] at h0
    linear_combination h0
  have hqprod : q * (Complex.normSq z - 1) = 0 := by
    rw [hu, hv, hk] at h3
    linear_combination h3
  have hq : q = 0 := (mul_eq_zero.mp hqprod).resolve_right (sub_ne_zero.mpr hz)
  simp [hq, hu, hv] at hnonzero

private theorem spectrumOnGeneralizedCircle_affine_pullback {ι : Type*} (a : ι → ℂ)
    (c d : ℂ) (hd : d ≠ 0) (h : SpectrumOnGeneralizedCircle (fun i => c + d * a i)) :
    SpectrumOnGeneralizedCircle a := by
  obtain ⟨q, u, v, k, hnonzero, h⟩ := h
  let w : ℂ := (⟨u, v⟩ - (q : ℂ) * c) * conj d
  refine ⟨q * Complex.normSq d, w.re, w.im,
    q * Complex.normSq c - 2 * (u * c.re + v * c.im) + k, ?_, ?_⟩
  · by_cases hq : q = 0
    · right
      have huv : (⟨u, v⟩ : ℂ) ≠ 0 := by
        intro he
        have hu : u = 0 := congrArg Complex.re he
        have hv : v = 0 := congrArg Complex.im he
        simp [hq, hu, hv] at hnonzero
      have hconj : conj d ≠ 0 := fun he =>
        hd (by simpa only [map_zero, Complex.conj_conj] using congrArg (fun x : ℂ => conj x) he)
      have hw : w ≠ 0 := by simpa [w, hq] using mul_ne_zero huv hconj
      by_cases hRe : w.re = 0
      · exact Or.inr fun hIm => hw (Complex.ext hRe hIm)
      · exact Or.inl hRe
    · exact Or.inl (mul_ne_zero hq (mt Complex.normSq_eq_zero.mp hd))
  · intro i
    have hi := h i
    change q * Complex.normSq (c + d * a i) -
      2 * (u * (c + d * a i).re + v * (c + d * a i).im) + k = 0 at hi
    change q * Complex.normSq d * Complex.normSq (a i) -
      2 * (w.re * (a i).re + w.im * (a i).im) +
      (q * Complex.normSq c - 2 * (u * c.re + v * c.im) + k) = 0
    simp only [w, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im] at hi ⊢
    linear_combination hi

/-- A fourth entry off the circumcircle makes the four points nonconcyclic and noncollinear. -/
theorem equilateralSpectrum_not_on_generalizedCircle (c d z : ℂ) (hd : d ≠ 0)
    (hz : Complex.normSq z ≠ 1) : ¬ SpectrumOnGeneralizedCircle (equilateralSpectrum c d z) := by
  intro h
  exact unitEquilateralSpectrum_not_on_generalizedCircle z hz
    (spectrumOnGeneralizedCircle_affine_pullback (unitEquilateralSpectrum z) c d hd h)

/-- An off-circle fourth point gives four distinct entries. -/
theorem equilateralSpectrum_injective (c d z : ℂ) (hd : d ≠ 0)
    (hz : Complex.normSq z ≠ 1) : Function.Injective (equilateralSpectrum c d z) := by
  classical
  let a := equilateralSpectrum c d z
  by_contra h
  letI : Fintype (Set.range a) := Fintype.ofFinite _
  have h' : ¬ Function.Injective (Set.rangeFactorization a) :=
    fun hinj => h (fun _ _ he => hinj (Subtype.ext he))
  have hc : Nat.card (Set.range a) < 4 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      Fintype.card_lt_of_surjective_not_injective _ Set.surjective_onto_range h'
  exact equilateralSpectrum_not_on_generalizedCircle c d z hd hz
    (spectrumOnGeneralizedCircle_of_card_range_le_three a (Nat.le_of_lt_succ hc))

/-- Distinct fourth parameters give distinct ordered spectra. -/
theorem equilateralSpectrum_injective_outlier (c d : ℂ) (hd : d ≠ 0) :
    Function.Injective (equilateralSpectrum c d) := by
  intro z w h
  have he := congrFun h 3
  change c + d * z = c + d * w at he
  exact mul_left_cancel₀ hd (add_left_cancel he)

/-- Two equilateral triples with opposite first entries give order-four inclusion
for every relative unitary. Each fourth entry is free off its own circumcircle. -/
theorem holds_four_equilateral (p d e z w : ℂ) (hd : d ≠ 0) (he : e ≠ 0)
    (hz : Complex.normSq z ≠ 1) (hw : Complex.normSq w ≠ 1) :
    let a := equilateralSpectrum (p - d) d z
    let b := equilateralSpectrum (-p - e) e w
    Function.Injective a ∧ Function.Injective b ∧
      ¬ SpectrumOnGeneralizedCircle a ∧ ¬ SpectrumOnGeneralizedCircle b ∧
      ∀ (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U → Holds a b U := by
  refine ⟨equilateralSpectrum_injective _ _ _ hd hz, equilateralSpectrum_injective _ _ _ he hw,
    equilateralSpectrum_not_on_generalizedCircle _ _ _ hd hz,
    equilateralSpectrum_not_on_generalizedCircle _ _ _ he hw, fun U hU => ?_⟩
  apply holds_four_opposite_at_zero _ _ U hU
  change p - d + d * 1 + (-p - e + e * 1) = 0
  ring

end

end MOC
