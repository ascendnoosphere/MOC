import MOC.ContactCensus
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Reality and nonsingularity of the distinct projective chart in T4. -/

namespace MOC

open scoped ComplexConjugate

/-- The normalized matching product for `A = (z, 0, 1, x)` and
`C = (w, v, ∞, t*v)`, with the pole factor suppressed. -/
noncomputable def fourT4PoleProduct (z x w v t : ℂ) (i : Fin 24) : ℂ :=
  let A : Fin 4 → ℂ := ![z, 0, 1, x]
  let σ := (fourPerm i).symm
  Neg.neg ((A (σ 0) - w) * (A (σ 1) - v) * (A (σ 3) - t * v))

private theorem t4VectorZero {α : Type*} (a b c d : α) : ![a, b, c, d] 0 = a := rfl
private theorem t4VectorOne {α : Type*} (a b c d : α) : ![a, b, c, d] 1 = b := rfl
private theorem t4VectorTwo {α : Type*} (a b c d : α) : ![a, b, c, d] 2 = c := rfl
private theorem t4VectorThree {α : Type*} (a b c d : α) : ![a, b, c, d] 3 = d := rfl

private theorem t4ContactDifferences (z x w v t : ℂ) :
    let F := fourT4PoleProduct z x w v t
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
  simp only [fourT4PoleProduct, h00, h01, h03, h10, h11, h13, h40, h41, h43,
    h50, h51, h53, h70, h71, h73, h80, h81, h83,
    t4VectorZero, t4VectorOne, t4VectorTwo, t4VectorThree]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

private theorem imaginary_ratio_real {p q : ℂ} (hp : p.re = 0) (hp₀ : p ≠ 0)
    (hq : (p * q).re = 0) : q.im = 0 := by
  have hpi : p.im ≠ 0 := fun h => hp₀ (Complex.ext (by simpa using hp) (by simpa using h))
  have him : -(p.im * q.im) = 0 := by simpa only [Complex.mul_re, hp, zero_mul, zero_sub] using hq
  exact (mul_eq_zero.mp (neg_eq_zero.mp him)).resolve_left hpi

/-- The six T4 contacts force real projective parameters `x,t,r,u`.
The formulas for `z` and `w` have nonzero denominators on this chart. -/
theorem fourT4_normalized_chart (z x w v t η : ℂ) (H : ℝ)
    (hz : z ≠ 0) (hzv : z ≠ v) (hzw : z ≠ w) (hv : v ≠ 0) (hwv : w ≠ v)
    (htv : t * v ≠ 1) (htx : t * v ≠ x) (ht : t ≠ 1) (hx : x ≠ 1) (hη : η ≠ 0)
    (hc : ∀ i ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 24)),
      (η * fourT4PoleProduct z x w v t i).re = H) :
    t.im = 0 ∧ x.im = 0 ∧ (η * (v * (z - w))).re = 0 ∧
      ∃ r u : ℝ, (r : ℂ) ≠ 0 ∧
        ((r : ℂ) * (v * (z - w)) = z * (w - v) * (1 - t * v)) ∧
        ((u : ℂ) * (v * (z - w)) = (t * v - x) * (z * (1 + v - w) - v)) ∧
        let f := t * v - x
        let Wden := -(r : ℂ) * f + (u : ℂ) * (t * v - 1)
        let Zden := f * (t * v - 1) - v * Wden
        Wden ≠ 0 ∧ Zden ≠ 0 ∧
          w = -f * ((r : ℂ) + 1 - t * v) / Wden ∧ z = (r : ℂ) * v * f / Zden := by
  let F := fourT4PoleProduct z x w v t
  let D := v * (z - w)
  have hD : D ≠ 0 := mul_ne_zero hv (sub_ne_zero.mpr hzw)
  have hηD : η * D ≠ 0 := mul_ne_zero hη hD
  obtain ⟨h1, h4, h5, h7, h8⟩ := t4ContactDifferences z x w v t
  change F 1 - F 0 = D * (1 - x) at h1
  change F 4 - F 0 = D * (t - x) at h4
  change F 5 - F 0 = D * (x * (t - 1)) at h5
  have hline {i j : Fin 24} (hi : i ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 24)))
      (hj : j ∈ ({0, 1, 4, 5, 7, 8} : Finset (Fin 24))) : (η * (F i - F j)).re = 0 := by
    change (η * (fourT4PoleProduct z x w v t i - fourT4PoleProduct z x w v t j)).re = 0
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
