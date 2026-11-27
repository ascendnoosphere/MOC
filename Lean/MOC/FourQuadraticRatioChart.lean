import MOC.ContactCensus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MOC.FourQuadraticRatioCapacity

/-! Reality and nonsingularity of the distinct projective chart in quadratic-ratio pattern. -/

namespace MOC

open scoped ComplexConjugate

/-- The normalized matching product for `A = (z, 0, 1, x)` and
`C = (w, v, ∞, t*v)`, with the pole factor suppressed. -/
noncomputable def fourQuadraticRatioPoleProduct (z x w v t : ℂ) (i : Fin 24) : ℂ :=
  let A : Fin 4 → ℂ := ![z, 0, 1, x]
  let σ := (fourPerm i).symm
  Neg.neg ((A (σ 0) - w) * (A (σ 1) - v) * (A (σ 3) - t * v))

private theorem quadraticRatioVectorZero {α : Type*} (a b c d : α) : ![a, b, c, d] 0 = a := rfl
private theorem quadraticRatioVectorOne {α : Type*} (a b c d : α) : ![a, b, c, d] 1 = b := rfl
private theorem quadraticRatioVectorTwo {α : Type*} (a b c d : α) : ![a, b, c, d] 2 = c := rfl
private theorem quadraticRatioVectorThree {α : Type*} (a b c d : α) : ![a, b, c, d] 3 = d := rfl

private theorem quadraticRatioContactDifferences (z x w v t : ℂ) :
    let F := fourQuadraticRatioPoleProduct z x w v t
    let D := v * (z - w)
    F 1 - F 0 = D * (1 - x) ∧ F 4 - F 0 = D * (t - x) ∧
    F 5 - F 0 = D * (x * (t - 1)) ∧ F 7 - F 1 = z * (w - v) * (1 - t * v) ∧
    F 8 - F 0 = (t * v - x) * (z * (1 + v - w) - v) := by
  have h00 : (fourPerm 0).symm 0 = 0 := by decide +kernel
  have h01 : (fourPerm 0).symm 1 = 1 := by decide +kernel
  have h03 : (fourPerm 0).symm 3 = 3 := by decide +kernel
  have h10 : (fourPerm 1).symm 0 = 0 := by decide +kernel
  have h11 : (fourPerm 1).symm 1 = 1 := by decide +kernel
  have h13 : (fourPerm 1).symm 3 = 2 := by decide +kernel
  have h40 : (fourPerm 4).symm 0 = 0 := by decide +kernel
  have h41 : (fourPerm 4).symm 1 = 2 := by decide +kernel
  have h43 : (fourPerm 4).symm 3 = 1 := by decide +kernel
  have h50 : (fourPerm 5).symm 0 = 0 := by decide +kernel
  have h51 : (fourPerm 5).symm 1 = 3 := by decide +kernel
  have h53 : (fourPerm 5).symm 3 = 1 := by decide +kernel
  have h70 : (fourPerm 7).symm 0 = 1 := by decide +kernel
  have h71 : (fourPerm 7).symm 1 = 0 := by decide +kernel
  have h73 : (fourPerm 7).symm 3 = 2 := by decide +kernel
  have h80 : (fourPerm 8).symm 0 = 2 := by decide +kernel
  have h81 : (fourPerm 8).symm 1 = 0 := by decide +kernel
  have h83 : (fourPerm 8).symm 3 = 3 := by decide +kernel
  simp only [fourQuadraticRatioPoleProduct, h00, h01, h03, h10, h11, h13, h40, h41, h43,
    h50, h51, h53, h70, h71, h73, h80, h81, h83,
    quadraticRatioVectorZero, quadraticRatioVectorOne, quadraticRatioVectorTwo, quadraticRatioVectorThree]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

private theorem imaginary_ratio_real {p q : ℂ} (hp : p.re = 0) (hp₀ : p ≠ 0)
    (hq : (p * q).re = 0) : q.im = 0 := by
  have hpi : p.im ≠ 0 := fun h => hp₀ (Complex.ext (by simpa using hp) (by simpa using h))
  have him : -(p.im * q.im) = 0 := by simpa only [Complex.mul_re, hp, zero_mul, zero_sub] using hq
  exact (mul_eq_zero.mp (neg_eq_zero.mp him)).resolve_left hpi

/-- The six quadratic-ratio pattern contacts force real projective parameters `x,t,r,u`.
The formulas for `z` and `w` have nonzero denominators on this chart. -/
theorem fourQuadraticRatio_normalized_chart (z x w v t η : ℂ) (H : ℝ)
    (hz : z ≠ 0) (hzv : z ≠ v) (hzw : z ≠ w) (hv : v ≠ 0) (hwv : w ≠ v)
    (htv : t * v ≠ 1) (htx : t * v ≠ x) (ht : t ≠ 1) (hx : x ≠ 1) (hη : η ≠ 0)
    (hc : ∀ i ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 24)),
      (η * fourQuadraticRatioPoleProduct z x w v t i).re = H) :
    t.im = 0 ∧ x.im = 0 ∧ (η * (v * (z - w))).re = 0 ∧
      ∃ r u : ℝ, (r : ℂ) ≠ 0 ∧
        ((r : ℂ) * (v * (z - w)) = z * (w - v) * (1 - t * v)) ∧
        ((u : ℂ) * (v * (z - w)) = (t * v - x) * (z * (1 + v - w) - v)) ∧
        let f := t * v - x
        let Wden := -(r : ℂ) * f + (u : ℂ) * (t * v - 1)
        let Zden := f * (t * v - 1) - v * Wden
        Wden ≠ 0 ∧ Zden ≠ 0 ∧
          w = -f * ((r : ℂ) + 1 - t * v) / Wden ∧ z = (r : ℂ) * v * f / Zden := by
  let F := fourQuadraticRatioPoleProduct z x w v t
  let D := v * (z - w)
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hηD : η * D ≠ 0 := mul_ne_zero hη hD
  obtain ⟨h1, h4, h5, h7, h8⟩ := quadraticRatioContactDifferences z x w v t
  change F 1 - F 0 = D * (1 - x) at h1
  change F 4 - F 0 = D * (t - x) at h4
  change F 5 - F 0 = D * (x * (t - 1)) at h5
  have hline {i j : Fin 24} (hi : i ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 24)))
      (hj : j ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 24))) : (η * (F i - F j)).re = 0 := by
    change (η * (fourQuadraticRatioPoleProduct z x w v t i - fourQuadraticRatioPoleProduct z x w v t j)).re = 0
    rw [mul_sub, Complex.sub_re, hc i hi, hc j hj, sub_self]
  have htline : (η * (F 1 - F 0) * t).re = 0 := by
    have h := hline (i := 5) (j := 4) (by decide) (by decide)
    have hid : η * (F 1 - F 0) * t = -(η * (F 5 - F 4)) := by
      linear_combination η * t * h1 + η * h5 - η * h4
    simp only [hid, Complex.neg_re, h, neg_zero]
  have ht_re : t.im = 0 := imaginary_ratio_real (hline (i := 1) (j := 0) (by decide) (by decide))
    (by rw [h1]; exact mul_ne_zero hη (mul_ne_zero hD (sub_ne_zero.mpr hx.symm))) htline
  have htD : (η * D).re = 0 := by
    have h := hline (i := 4) (j := 1) (by decide) (by decide)
    have hid : η * (F 4 - F 1) = (η * D) * (t - 1) := by linear_combination η * (h4 - h1)
    rw [hid, Complex.mul_re] at h
    have htre : t.re - 1 ≠ 0 := fun hu => ht (Complex.ext (by simpa using sub_eq_zero.mp hu)
      (by simpa only [Complex.one_im] using ht_re))
    simpa only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, ht_re, sub_self,
      mul_zero, sub_zero, mul_eq_zero, htre, or_false] using h
  have hx_re : x.im = 0 := by
    have h := hline (i := 1) (j := 0) (by decide) (by decide)
    rw [h1, ← mul_assoc] at h
    have h' := imaginary_ratio_real htD hηD h
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_eq_zero] using h'
  let r := (F 7 - F 1) / D
  let u := (F 8 - F 0) / D
  have hrD : r * D = F 7 - F 1 := div_mul_cancel₀ _ hD
  have huD : u * D = F 8 - F 0 := div_mul_cancel₀ _ hD
  have hr_re : r.im = 0 := imaginary_ratio_real htD hηD (by
    rw [show (η * D) * r = η * (r * D) by ring, hrD]
    exact hline (i := 7) (j := 1) (by decide) (by decide))
  have hu_re : u.im = 0 := imaginary_ratio_real htD hηD (by
    rw [show (η * D) * u = η * (u * D) by ring, huD]
    exact hline (i := 8) (j := 0) (by decide) (by decide))
  have hr : (r.re : ℂ) = r := Complex.ext (by simp) (by simpa using hr_re.symm)
  have hu : (u.re : ℂ) = u := Complex.ext (by simp) (by simpa using hu_re.symm)
  have hR : r * D = z * (w - v) * (1 - t * v) := hrD.trans h7
  have hU : u * D = (t * v - x) * (z * (1 + v - w) - v) := huD.trans h8
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, zero_mul] at hR
    exact mul_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr hwv)) (sub_ne_zero.mpr htv.symm) hR.symm
  refine ⟨ht_re, hx_re, htD, r.re, u.re, ?_⟩
  rw [hr, hu]
  refine ⟨hr₀, hR, hU, ?_⟩
  let f := t * v - x
  let Wden := -r * f + u * (t * v - 1)
  let Zden := f * (t * v - 1) - v * Wden
  have hf : f ≠ 0 := sub_ne_zero.mpr htx
  change r * (v * (z - w)) = _ at hR
  change u * (v * (z - w)) = _ at hU
  have hzid : z * Zden = r * v * f := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hzw)
    dsimp only [Zden, Wden, f]
    linear_combination z * (1 - t * v) * hU - (t * v - x) * (1 - z) * hR
  have hwid : w * Wden = -f * (r + 1 - t * v) := by
    apply mul_left_cancel₀ (mul_ne_zero hz hv)
    dsimp only [Wden, f]
    have hzid' := hzid
    dsimp only [Zden, Wden, f] at hzid'
    linear_combination (t * v - x) * hR - w * hzid'
  have hZ : Zden ≠ 0 := by
    intro h
    rw [h, mul_zero] at hzid
    exact (mul_ne_zero (mul_ne_zero hr₀ hv) hf) hzid.symm
  have hW : Wden ≠ 0 := by
    intro h
    have hR0 : r + 1 - t * v = 0 := by
      rw [h, mul_zero] at hwid
      exact (mul_eq_zero.mp hwid.symm).resolve_left (neg_ne_zero.mpr hf)
    have hrtv : t * v - 1 = r := by linear_combination -hR0
    have hZ₁ : Zden = f * r := by simp [Zden, h, hrtv]
    rw [hZ₁] at hzid
    apply hzv
    apply mul_right_cancel₀ (mul_ne_zero hf hr₀)
    convert hzid using 1 <;> ring
  exact ⟨hW, hZ, (eq_div_iff hW).mpr hwid, (eq_div_iff hZ).mpr hzid⟩

end MOC

/-! The exact matching-ratio identities used in the positive quadratic-ratio pattern capacity
argument. All denominators are controlled by the distinct pole chart. -/

namespace MOC

private def quadraticRatioRatioIndices : Fin 9 → Fin 24 := ![0, 2, 6, 9, 10, 13, 14, 16, 19]

private theorem quadraticRatioRatioProductValues (z x w v t : ℂ) (i : Fin 9) :
    fourQuadraticRatioPoleProduct z x w v t (quadraticRatioRatioIndices i) =
      (![v * (z - w) * (x - t * v), (v - 1) * (z - w) * (x - t * v),
        w * (z - v) * (x - t * v), (z - v) * (x - w) * (t * v - 1),
        t * v * (z - v) * (1 - w), -w * (x - v) * (t * v - 1),
        v * (t * v - x) * (w - 1), t * v * (x - v) * (1 - w),
        w * (x - v) * (z - t * v)] : Fin 9 → ℂ) i := by
  have h : ∀ k : Fin 9,
      let σ := (fourPerm (quadraticRatioRatioIndices k)).symm
      σ 0 = (![0, 0, 1, 3, 2, 1, 2, 2, 1] : Fin 9 → Fin 4) k ∧
      σ 1 = (![1, 2, 0, 0, 0, 3, 1, 3, 3] : Fin 9 → Fin 4) k ∧
      σ 3 = (![3, 3, 3, 2, 1, 2, 3, 1, 0] : Fin 9 → Fin 4) k := by
    decide +kernel
  obtain ⟨h₀, h₁, h₃⟩ := h i
  dsimp only [fourQuadraticRatioPoleProduct]
  rw [h₀, h₁, h₃]
  fin_cases i <;> simp [Matrix.cons_val] <;> ring_nf <;> simp

set_option maxHeartbeats 1500000 in
/-- The algebraic quadratic-ratio pattern source equations and the quadratic ratios at indices
19 and `2 - 13` are exact identities of the original projective products. -/
theorem fourQuadraticRatio_exact_pole_ratios (x t r u : ℝ) (z w v : ℂ)
    (hv : v ≠ 0) (hzw : z ≠ w) (ht : t ≠ 0) :
    let F := fourQuadraticRatioPoleProduct z x w v t
    let D := v * (z - w)
    let R (i : Fin 24) := (F i - F 0) / D
    let y := x - 1
    let h := 1 - t
    let H := h + u
    let E := H * (1 - t * x) - h * r * y
    let J := H * (1 - t * x) + h * y
    let f := (t : ℂ) * v - x
    let T := (t : ℂ) * v - 1
    let W := -(r : ℂ) * f + (u : ℂ) * T
    let Z := f * T - v * W
    f ≠ 0 → T ≠ 0 → W ≠ 0 → Z ≠ 0 →
    z = (r : ℂ) * v * f / Z → w = -f * ((r : ℂ) + 1 - t * v) / W →
    let Q := quadraticRatioQuadraticEval (quadraticRatioShiftedDen x t r u) f
    Q ≠ 0 ∧ R 2 = f / v ∧ R 6 = (r : ℂ) * f / T ∧
      R 10 = (t : ℂ) * v * u / f - x ∧
      R 9 = (y : ℂ) * R 10 + ((y ^ 2 - r * y + u : ℝ) : ℂ) ∧
      R 2 - R 13 = quadraticRatioQuadraticEval (quadraticRatioShiftedNumD x t r u) f / Q ∧
      R 19 = quadraticRatioQuadraticEval (quadraticRatioShiftedNumB x t r u) f / Q ∧
      R 16 - (h : ℂ) * R 10 + (t : ℂ) * (R 19 + (R 2 - R 13)) =
        ((t * (t + u - 1) : ℝ) : ℂ) ∧
      (E : ℂ) * R 14 - ((t * y * H : ℝ) : ℂ) * R 19 + (J : ℂ) * (R 2 - R 13) =
        (((h * x - y) * u ^ 2 + h ^ 2 * x * (u + y) - r * h * x * H : ℝ) : ℂ) := by
  intro F D R y h H E J f T W Z hf hT hW hZ hz hw Q
  let k := (r : ℂ) + 1 - t * v
  let Q₀ := v * W + k * f
  have hZW : z - w = f * T * Q₀ / (Z * W) := by
    rw [hz, hw]
    field_simp [hZ, hW]
    dsimp only [Z, Q₀, k, T]
    ring
  have hQ₀ : Q₀ ≠ 0 := by
    intro hzero
    apply sub_ne_zero.mpr hzw
    rw [hZW, hzero, mul_zero, zero_div]
  have hQ : Q = (t : ℂ) * Q₀ := by
    dsimp only [Q, Q₀, quadraticRatioQuadraticEval, quadraticRatioShiftedDen, W, k, T, f]
    push_cast
    ring
  have hQnz : Q ≠ 0 := by rw [hQ]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) hQ₀
  have hF₀ : F 0 = -f * D := by
    have hh : F 0 = v * (z - w) * (x - (t : ℂ) * v) := quadraticRatioRatioProductValues z x w v t 0
    rw [hh]
    dsimp only [f, D]
    ring
  have hF₂ : F 2 = (v - 1) * (z - w) * (x - (t : ℂ) * v) := quadraticRatioRatioProductValues z x w v t 1
  have hF₆ : F 6 = w * (z - v) * (x - (t : ℂ) * v) := quadraticRatioRatioProductValues z x w v t 2
  have hF₉ : F 9 = (z - v) * (x - w) * ((t : ℂ) * v - 1) := quadraticRatioRatioProductValues z x w v t 3
  have hF₁₀ : F 10 = (t : ℂ) * v * (z - v) * (1 - w) := quadraticRatioRatioProductValues z x w v t 4
  have hF₁₃ : F 13 = -w * (x - v) * ((t : ℂ) * v - 1) := quadraticRatioRatioProductValues z x w v t 5
  have hF₁₄ : F 14 = v * ((t : ℂ) * v - x) * (w - 1) := quadraticRatioRatioProductValues z x w v t 6
  have hF₁₆ : F 16 = (t : ℂ) * v * (x - v) * (1 - w) := quadraticRatioRatioProductValues z x w v t 7
  have hF₁₉ : F 19 = w * (x - v) * (z - (t : ℂ) * v) := quadraticRatioRatioProductValues z x w v t 8
  let Dn := v * f * T * Q₀
  have hDn : Dn ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hv hf) hT) hQ₀
  have hD : D = Dn / (Z * W) := by
    change v * (z - w) = _
    rw [hZW]
    dsimp only [Dn]
    ring
  have hDne : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hz' : z = (r : ℂ) * v * f / Z := hz
  have hw' : w = -f * k / W := hw
  have hR (i : Fin 24) : R i = F i / D + f := by
    dsimp only [R]
    rw [hF₀, neg_mul, sub_neg_eq_add, add_div, mul_div_cancel_right₀ _ hDne]
  have hRnorm (i : Fin 24) (a b : ℂ) (hb : b ≠ 0)
      (hnum : F i * (Z * W) * b = a * Dn) : R i = a / b + f := by
    rw [hR, hD, div_div_eq_mul_div, (div_eq_div_iff hDn hb).mpr hnum]
  have hzv : z - v = v * Q₀ / Z := by
    rw [hz']
    field_simp [hZ]
    dsimp only [Q₀, Z, k, T]
    ring
  have hxw : (x : ℂ) - w = ((x : ℂ) * W + f * k) / W := by
    rw [hw']
    field_simp [hW] <;> ring
  have hw₁ : w - 1 = (f - u) * T / W := by
    rw [hw']
    field_simp [hW]
    dsimp only [W, k, T]
    ring
  have h₁w : 1 - w = (u - f) * T / W := by
    have heq : 1 - w = -(w - 1) := by ring
    rw [heq, hw₁]
    field_simp [hW]
    ring
  have hztv : z - (t : ℂ) * v = v * T * ((t : ℂ) * v * u - ((r : ℂ) + t) * f) / Z := by
    rw [hz']
    field_simp [hZ]
    dsimp only [Z, W, T]
    ring
  have hR₂ : R 2 = f / v := by
    dsimp only [R]
    rw [hF₂, hF₀]
    change ((v - 1) * (z - w) * (x - (t : ℂ) * v) - -f * (v * (z - w))) /
      (v * (z - w)) = _
    field_simp [hv, sub_ne_zero.mpr hzw]
    dsimp only [f]
    ring
  have hR₆ : R 6 = (r : ℂ) * f / T := by
    rw [hRnorm 6 (f * k) T hT (by
      rw [hF₆, hzv, hw', show (x : ℂ) - (t : ℂ) * v = -f by dsimp only [f]; ring]
      field_simp [hZ, hW] <;> dsimp only [Dn] <;> ring)]
    field_simp [hT]
    dsimp only [k, T]
    ring
  have hR₁₀ : R 10 = (t : ℂ) * v * u / f - x := by
    rw [hRnorm 10 ((t : ℂ) * v * (u - f)) f hf (by
      rw [hF₁₀, hzv, h₁w]
      field_simp [hZ, hW] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf]
    dsimp only [f]
    ring
  have hR₉ : R 9 = (y : ℂ) * R 10 + ((y ^ 2 - r * y + u : ℝ) : ℂ) := by
    rw [hR₁₀, hRnorm 9 ((x : ℂ) * W + f * k) f hf (by
      rw [hF₉, hzv, hxw]
      change (v * Q₀ / Z * (((x : ℂ) * W + f * k) / W) * T) * (Z * W) * f = _
      field_simp [hZ, hW] <;> dsimp only [Dn] <;> ring)]
    field_simp [hf]
    dsimp only [W, k, T, f, y]
    push_cast
    ring
  have hR₁₄ : R 14 = (f - u) * Z / Q₀ + f := by
    apply hRnorm 14 _ _ hQ₀
    rw [hF₁₄, hw₁]
    change (v * f * ((f - u) * T / W)) * (Z * W) * Q₀ = _
    field_simp [hW] <;> dsimp only [Dn] <;> ring
  have hR₁₆ : R 16 = (t : ℂ) * (x - v) * (u - f) * Z / (f * Q₀) + f := by
    apply hRnorm 16 _ _ (mul_ne_zero hf hQ₀)
    rw [hF₁₆, h₁w]
    field_simp [hW] <;> dsimp only [Dn] <;> ring
  let N := W * ((r : ℂ) * x + ((h : ℂ) * y - r) * v) + k * f * (h : ℂ) * y
  let M := k * (x - v) * (((r : ℂ) + t) * f - (t : ℂ) * v * u) + f * Q₀
  have hRD : R 2 - R 13 = N / Q₀ := by
    have h13 : R 13 = k * (x - v) * Z / (v * Q₀) + f := by
      apply hRnorm 13 _ _ (mul_ne_zero hv hQ₀)
      rw [hF₁₃, hw']
      change (-(-f * k / W) * (x - v) * T) * (Z * W) * (v * Q₀) = _
      field_simp [hW] <;> dsimp only [Dn] <;> ring
    rw [hR₂, h13]
    field_simp [hv, hQ₀]
    dsimp only [N, Q₀, Z, k, T, f, h, y]
    push_cast
    ring
  have hRB : R 19 = M / Q₀ := by
    rw [hRnorm 19 (k * (x - v) * (((r : ℂ) + t) * f - (t : ℂ) * v * u)) Q₀ hQ₀ (by
      rw [hF₁₉, hztv, hw']
      field_simp [hZ, hW] <;> dsimp only [Dn] <;> ring)]
    dsimp only [M]
    field_simp [hQ₀]
  have hN : quadraticRatioQuadraticEval (quadraticRatioShiftedNumD x t r u) f = (t : ℂ) * N := by
    dsimp only [N, quadraticRatioQuadraticEval, quadraticRatioShiftedNumD, Q₀, Z, W, k, T, f, h, y]
    push_cast
    ring
  have hM : quadraticRatioQuadraticEval (quadraticRatioShiftedNumB x t r u) f = (t : ℂ) * M := by
    dsimp only [M, quadraticRatioQuadraticEval, quadraticRatioShiftedNumB, quadraticRatioShiftedDen, Q₀, Z, W, k, T, f, h, y]
    push_cast
    ring
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine ⟨hQnz, hR₂, hR₆, hR₁₀, hR₉, ?_, ?_, ?_, ?_⟩
  · rw [hRD, hN, hQ]
    field_simp [ht', hQ₀] <;> ring
  · rw [hRB, hM, hQ]
    field_simp [ht', hQ₀] <;> ring
  · rw [hR₁₆, hR₁₀, hRD, hRB]
    field_simp [hf, hQ₀]
    dsimp only [N, M, Q₀, Z, W, k, T, f, h, y]
    push_cast
    ring
  · rw [hR₁₄, hRD, hRB]
    field_simp [hQ₀]
    dsimp only [N, M, Q₀, Z, W, k, T, f, E, J, H, h, y]
    push_cast
    ring

end MOC
