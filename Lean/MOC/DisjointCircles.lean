import MOC.Geometry
import MOC.Support
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.LinearCombination

/-! A fractional-linear change sends two disjoint circles to concentric circles. -/

open Matrix

namespace MOC

private theorem normSq_fractional_of_circle (z : ℂ) (p q c R : ℝ)
    (hpq : p ≠ q) (hR : R ≠ 0)
    (hz : Complex.normSq (z - (c : ℂ)) = R) (hpqR : (p - c) * (q - c) = R) :
    z - (q : ℂ) ≠ 0 ∧
      Complex.normSq ((z - (p : ℂ)) / (z - (q : ℂ))) = (p - c) / (q - c) := by
  have hq : q - c ≠ 0 := by
    intro h
    exact hR (by simpa [h] using hpqR.symm)
  have hzq : z - (q : ℂ) ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h, ← Complex.ofReal_sub, Complex.normSq_ofReal] at hz
    have he : (p - q) * (q - c) = 0 := by
      linear_combination hpqR - hz
    exact hpq (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hq))
  refine ⟨hzq, ?_⟩
  rw [Complex.normSq_div, div_eq_div_iff (Complex.normSq_pos.mpr hzq).ne' hq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero] at hz ⊢
  linear_combination (q - p) * hz - (q - p) * hpqR

private theorem discriminant_pos_of_disjoint_radii (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (h : r + s < 1 ∨ 1 < |r - s|) : 0 < (1 + r ^ 2 - s ^ 2) ^ 2 - 4 * r ^ 2 := by
  rw [show (1 + r ^ 2 - s ^ 2) ^ 2 - 4 * r ^ 2 =
    (1 - (r + s) ^ 2) * (1 - (r - s) ^ 2) by ring]
  have hdiff : (r - s) ^ 2 < (r + s) ^ 2 := by nlinarith [mul_pos hr hs]
  rcases h with h | h
  · have hsum : (r + s) ^ 2 < 1 := by
      simpa only [one_pow] using (sq_lt_sq₀ (by positivity : 0 ≤ r + s) zero_le_one).2 h
    exact mul_pos (sub_pos.mpr hsum) (sub_pos.mpr (hdiff.trans hsum))
  · have hsq : 1 < (r - s) ^ 2 := by
      simpa only [one_pow] using (sq_lt_sq (a := 1) (b := r - s)).2
        (by simpa only [abs_one] using h)
    exact mul_pos_of_neg_of_neg (sub_neg.mpr (hsq.trans hdiff)) (sub_neg.mpr hsq)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the concentric-circle case holds, it also holds for spectra on two
disjoint circles. The signed spectra are normalized to centers `0` and `1`
by translating by `c` and dividing by the difference `d` of the centers. -/
theorem holds_of_disjoint_circles_of_concentric (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (c d : ℂ) (hd : d ≠ 0) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hdisjoint : r + s < 1 ∨ 1 < |r - s|)
    (ha : ∀ i, Complex.normSq ((a i - c) / d) = r ^ 2)
    (hb : ∀ i, Complex.normSq ((-b i - c) / d - 1) = s ^ 2)
    (hconcentric : ∀ (x y : ι → ℂ) (R S : ℝ),
      (∀ i, Complex.normSq (x i) = R) → (∀ i, Complex.normSq (y i) = S) → Holds x y U) :
    Holds a b U := by
  let x (i : ι) : ℂ := (a i - c) / d
  let y (i : ι) : ℂ := (-b i - c) / d
  let m := 1 + r ^ 2 - s ^ 2
  let D := m ^ 2 - 4 * r ^ 2
  have hD : 0 < D := discriminant_pos_of_disjoint_radii r s hr hs hdisjoint
  let e := Real.sqrt D
  let p := (m - e) / 2
  let q := (m + e) / 2
  have he : 0 < e := Real.sqrt_pos_of_pos hD
  have hesq : e ^ 2 = m ^ 2 - 4 * r ^ 2 := Real.sq_sqrt hD.le
  have hpq : p ≠ q := by dsimp only [p, q]; linarith
  have hprod : p * q = r ^ 2 := by
    calc
      _ = (m ^ 2 - e ^ 2) / 4 := by dsimp only [p, q]; ring
      _ = r ^ 2 := by rw [hesq]; ring
  have hsum : p + q = m := by dsimp only [p, q]; ring
  have hprod' : (p - 1) * (q - 1) = s ^ 2 := by
    calc
      _ = p * q - (p + q) + 1 := by ring
      _ = s ^ 2 := by rw [hprod, hsum]; dsimp only [m]; ring
  have hx (i : ι) := normSq_fractional_of_circle (x i) p q 0 (r ^ 2) hpq
    (pow_ne_zero 2 hr.ne') (by simpa [x] using ha i) (by simpa using hprod)
  have hy (i : ι) := normSq_fractional_of_circle (y i) p q 1 (s ^ 2) hpq
    (pow_ne_zero 2 hs.ne') (by simpa [y] using hb i) hprod'
  let α (i : ι) := x i - (q : ℂ)
  let β (i : ι) := y i - (q : ℂ)
  let k := (q : ℂ) - (p : ℂ)
  have hk : k ≠ 0 := sub_ne_zero.mpr (fun h => hpq ((Complex.ofReal_injective h).symm))
  have hform (z : ℂ) (hz : z - (q : ℂ) ≠ 0) :
      (z - (p : ℂ)) / (z - (q : ℂ)) = k * (z - (q : ℂ))⁻¹ + 1 := by
    dsimp only [k]
    field_simp [hz] <;> ring
  have hleft : ∀ i, Complex.normSq (k * (α i)⁻¹ + 1) = (p - 0) / (q - 0) := by
    intro i
    rw [← hform (x i) (hx i).1]
    exact (hx i).2
  have hright : ∀ i, Complex.normSq (k * -(β i)⁻¹ - 1) = (p - 1) / (q - 1) := by
    intro i
    rw [show k * -(β i)⁻¹ - 1 = -(k * (β i)⁻¹ + 1) by ring, Complex.normSq_neg,
      ← hform (y i) (hy i).1]
    exact (hy i).2
  have hscaled : Holds (fun i => k * (α i)⁻¹) (fun i => k * -(β i)⁻¹) U :=
    (holds_shift_iff _ _ hU 1).mp (hconcentric _ _ _ _ hleft hright)
  have hinv : Holds (fun i => (α i)⁻¹) (fun i => -(β i)⁻¹) U :=
    (hull_common_factor_iff (pow_ne_zero _ hk) (determinantValue_scale _ _ U k)
      (matchingProduct_scale _ _ k)).mp hscaled
  have hshift := (holds_inv_iff α β U hU (fun i => (hx i).1) (fun i => (hy i).1)).mp hinv
  have hnorm : Holds x (fun i => -y i) U := by
    apply (holds_shift_iff _ _ hU (-(q : ℂ))).mp
    have hα : (fun i => x i + -(q : ℂ)) = α := by
      funext i
      simp only [α, sub_eq_add_neg]
    have hβ : (fun i => -y i - -(q : ℂ)) = fun i => -(β i) := by
      funext i
      dsimp only [β]
      ring
    rwa [hα, hβ]
  have hdenorm : Holds (fun i => d * x i) (fun i => d * -y i) U :=
    hull_of_common_factor (determinantValue_scale _ _ U d) (matchingProduct_scale _ _ d) hnorm
  apply (holds_shift_iff _ _ hU (-c)).mp
  convert hdenorm using 1
  · funext i; dsimp only [x]; field_simp [hd] <;> ring
  · funext i; dsimp only [y]; field_simp [hd] <;> ring

end MOC
