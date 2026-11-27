import MOC.ContactCensus
import MOC.FourT7Minor
import Mathlib.Tactic.FieldSimp

/-! The projective normalization of actual spectral vectors in case T7. -/

namespace MOC

open BigOperators

noncomputable section

/-- Matching products after the first three left labels are sent to infinity,
zero and one. The row at infinity supplies the constant factor one. -/
def fourT7ProjectiveProduct (z : ℂ) (C : Fin 4 → ℂ) (i : Fin 24) : ℂ :=
  -(C (fourPerm i 1)) * (1 - C (fourPerm i 2)) * (z - C (fourPerm i 3))

/-- The projective chart exhausts regular order-four spectral vectors. It
preserves all matching products up to one common nonzero factor. -/
theorem exists_fourT7_projective_products (a b : Fin 4 → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hn : ∀ i j, a i + b j ≠ 0) :
    ∃ K z : ℂ, ∃ C : Fin 4 → ℂ, K ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 ∧ Function.Injective C ∧
      (∀ j, C j ≠ 0 ∧ C j ≠ 1 ∧ C j ≠ z) ∧
      ∀ i, matchingProduct a b (fourPerm i).symm = K * fourT7ProjectiveProduct z C i := by
  let d := (a 2 - a 0) / (a 2 - a 1)
  let L := d * (a 1 - a 0)
  let f (x : ℂ) := d * (x - a 1) / (x - a 0)
  let D (j : Fin 4) := -b j - a 0
  let C (j : Fin 4) := f (-b j)
  let z := f (a 3)
  let K := -((a 1 - a 0) / L) * ((a 2 - a 0) / L) * ((a 3 - a 0) / L) * ∏ j, D j
  have hD (j : Fin 4) : D j ≠ 0 := by
    dsimp only [D]
    intro h
    exact hn 0 j (by linear_combination -h)
  have hsub (i : Fin 4) (hi : i ≠ 0) : a i - a 0 ≠ 0 := sub_ne_zero.mpr (ha.ne hi)
  have hd : d ≠ 0 := div_ne_zero (hsub 2 (by decide))
    (sub_ne_zero.mpr (ha.ne (by decide : (2 : Fin 4) ≠ 1)))
  have hL : L ≠ 0 := mul_ne_zero hd (hsub 1 (by decide))
  have hf1 : f (a 1) = 0 := by simp [f]
  have hf2 : f (a 2) = 1 := by
    dsimp only [f, d]
    field_simp [hsub 2 (by decide), sub_ne_zero.mpr (ha.ne (by decide : (2 : Fin 4) ≠ 1))]
    <;> ring
  have hfd {x y : ℂ} (hx : x - a 0 ≠ 0) (hy : y - a 0 ≠ 0) :
      f x - f y = L * (x - y) / ((x - a 0) * (y - a 0)) := by
    dsimp only [f, L]
    field_simp [hx, hy] <;> ring
  have hfinj {x y : ℂ} (hx : x - a 0 ≠ 0) (hy : y - a 0 ≠ 0) (h : f x = f y) : x = y := by
    have he := hfd hx hy
    rw [h, sub_self] at he
    have hz := (div_eq_zero_iff.mp he.symm).resolve_right (mul_ne_zero hx hy)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hL)
  have hC1 (j : Fin 4) : C j ≠ 0 := by
    rw [← hf1]
    exact fun h => (hn 1 j) (by rw [← hfinj (hD j) (hsub 1 (by decide)) h, neg_add_cancel])
  have hC2 (j : Fin 4) : C j ≠ 1 := by
    rw [← hf2]
    exact fun h => (hn 2 j) (by rw [← hfinj (hD j) (hsub 2 (by decide)) h, neg_add_cancel])
  have hC3 (j : Fin 4) : C j ≠ z := by
    exact fun h => (hn 3 j) (by rw [← hfinj (hD j) (hsub 3 (by decide)) h, neg_add_cancel])
  have hfactor (i j : Fin 4) (hi : i ≠ 0) :
      a i + b j = ((a i - a 0) / L) * D j * (f (a i) - C j) := by
    dsimp only [C]
    rw [hfd (hsub i hi) (hD j)]
    change a i + b j = ((a i - a 0) / L) * D j * (L * (a i - -b j) / ((a i - a 0) * D j))
    field_simp [hsub i hi, hD j, hL] <;> ring
  have hzero (j : Fin 4) : a 0 + b j = -D j := by dsimp [D]; ring
  refine ⟨K, z, C, ?_, ?_, ?_, ?_, fun j => ⟨hC1 j, hC2 j, hC3 j⟩, ?_⟩
  · exact mul_ne_zero (mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (hsub 1 (by decide)) hL))
        (div_ne_zero (hsub 2 (by decide)) hL)) (div_ne_zero (hsub 3 (by decide)) hL))
      (Finset.prod_ne_zero_iff.mpr fun j _ => hD j)
  · rw [← hf1]
    exact fun h => (ha.ne (by decide : (3 : Fin 4) ≠ 1)) (hfinj (hsub 3 (by decide)) (hsub 1 (by decide)) h)
  · rw [← hf2]
    exact fun h => (ha.ne (by decide : (3 : Fin 4) ≠ 2)) (hfinj (hsub 3 (by decide)) (hsub 2 (by decide)) h)
  · intro i j hij
    exact hb (neg_injective (hfinj (hD i) (hD j) hij))
  · intro i
    let σ := fourPerm i
    have hDprod : D (σ 0) * D (σ 1) * D (σ 2) * D (σ 3) = ∏ j, D j := by
      simpa only [Fin.prod_univ_four] using Equiv.prod_comp σ D
    change matchingProduct a b σ.symm = K * (-(C (σ 1)) * (1 - C (σ 2)) * (z - C (σ 3)))
    rw [matchingProduct_inverse, Fin.prod_univ_four, hzero, hfactor 1 _ (by decide),
      hfactor 2 _ (by decide), hfactor 3 _ (by decide), hf1, hf2, zero_sub]
    dsimp only [K]
    rw [← hDprod]
    change _ = _
    ring

private theorem t7_chord_ratios_real {κ x y : ℂ} (hκ : κ ≠ 0)
    (hx : (κ * x).re = 0) (hy : (κ * y).re = 0) :
    (x / y).im = 0 := by
  rw [← mul_div_mul_left x y hκ]
  simp [Complex.div_im, hx, hy]

private theorem t7_chart_chords (z w v r c : ℂ) :
    let F := fourT7ProjectiveProduct z ![w, v, r, c]
    F 0 - F 1 = v * (r - c) * (z - 1) ∧
    F 2 - F 4 = z * (r - c) * (v - 1) ∧
    F 0 - F 2 = (z - c) * (r - v) ∧
    F 7 - F 1 = (1 - c) * (z - r) * (v - w) ∧
    F 8 - F 2 = r * (z - c) * (w - v) := by
  dsimp only
  have h0 : fourT7ProjectiveProduct z ![w, v, r, c] 0 =
      -v * (1 - r) * (z - c) := rfl
  have h1 : fourT7ProjectiveProduct z ![w, v, r, c] 1 =
      -v * (1 - c) * (z - r) := rfl
  have h2 : fourT7ProjectiveProduct z ![w, v, r, c] 2 =
      -r * (1 - v) * (z - c) := rfl
  have h4 : fourT7ProjectiveProduct z ![w, v, r, c] 4 =
      -c * (1 - v) * (z - r) := rfl
  have h7 : fourT7ProjectiveProduct z ![w, v, r, c] 7 =
      -w * (1 - c) * (z - r) := rfl
  have h8 : fourT7ProjectiveProduct z ![w, v, r, c] 8 =
      -r * (1 - w) * (z - c) := rfl
  rw [h0, h1, h2, h4, h7, h8]
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

/-- In the T7 chart the contact equations make four rational parameters real.
The equation for the third column is denominator-free, including its zero
parameter branch. -/
theorem fourT7_chart_real_parameters (z w v r c κ : ℂ) (H : ℝ) (hκ : κ ≠ 0)
    (hz : z ≠ 0) (hz1 : z ≠ 1)
    (hinj : Function.Injective (![w, v, r, c] : Fin 4 → ℂ))
    (hsep : ∀ j, (![w, v, r, c] : Fin 4 → ℂ) j ≠ 0 ∧
      (![w, v, r, c] : Fin 4 → ℂ) j ≠ 1 ∧ (![w, v, r, c] : Fin 4 → ℂ) j ≠ z)
    (hc : ∀ i ∈ fourT7ContactIndices,
      (κ * fourT7ProjectiveProduct z ![w, v, r, c] i).re = H) :
    ∃ h t k l s : ℂ, h.im = 0 ∧ t.im = 0 ∧ k.im = 0 ∧ l.im = 0 ∧ s.im = 0 ∧
      h ≠ 0 ∧ h ≠ 1 ∧ t ≠ 0 ∧ t ≠ 1 ∧ k = 1 + t * (h - 1) ∧ s ≠ 0 ∧
      z = h * v / (1 + (h - 1) * v) ∧
      c = (z * (v - r) - t * r * (v - z)) / (v - r - t * (v - z)) ∧
      (1 + l * v) * r = k * v ∧ w = v + s * (v - r) / r ∧
      (κ * ((z - c) * (v - r))).re = 0 ∧
      v - z = (h - 1) * v * (z - 1) ∧
      (z - c) * (v - r) = t * (c - r) * (z - v) ∧
      (1 - c) * (z - r) / (r * (z - c)) = l / (k - 1) - 1 := by
  let F := fourT7ProjectiveProduct z ![w, v, r, c]
  have hreal (i j : Fin 24) (hi : i ∈ fourT7ContactIndices) (hj : j ∈ fourT7ContactIndices) :
      (κ * (F i - F j)).re = 0 := by
    simp only [F, mul_sub, Complex.sub_re, hc i hi, hc j hj, sub_self]
  obtain ⟨h01, h24, h02, h71, h82⟩ := t7_chart_chords z w v r c
  change F 0 - F 1 = _ at h01
  change F 2 - F 4 = _ at h24
  change F 0 - F 2 = _ at h02
  change F 7 - F 1 = _ at h71
  change F 8 - F 2 = _ at h82
  have hv : v ≠ 0 := (hsep 1).1
  have hv1 : v ≠ 1 := (hsep 1).2.1
  have hvz : v ≠ z := (hsep 1).2.2
  have hr : r ≠ 0 := (hsep 2).1
  have hzr : z ≠ r := (hsep 2).2.2.symm
  have hzc : z ≠ c := (hsep 3).2.2.symm
  have hrc : r ≠ c := hinj.ne (by decide : (2 : Fin 4) ≠ 3)
  have hvc : v ≠ c := hinj.ne (by decide : (1 : Fin 4) ≠ 3)
  have hvr : v ≠ r := hinj.ne (by decide : (1 : Fin 4) ≠ 2)
  have hwv : w ≠ v := hinj.ne (by decide : (0 : Fin 4) ≠ 1)
  let h := z * (v - 1) / (v * (z - 1))
  let t := (c - z) * (v - r) / ((c - r) * (v - z))
  let k := 1 + t * (h - 1)
  let l := k / r - 1 / v
  let s := r * (w - v) / (v - r)
  let e := (1 - c) * (z - r) / (r * (z - c))
  have hh0 : h ≠ 0 := div_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr hv1))
    (mul_ne_zero hv (sub_ne_zero.mpr hz1))
  have hh1' : h - 1 = (v - z) / (v * (z - 1)) := by
    dsimp only [h]
    field_simp [hv, sub_ne_zero.mpr hz1] <;> ring
  have hh1 : h ≠ 1 := by
    apply sub_ne_zero.mp
    rw [hh1']
    exact div_ne_zero (sub_ne_zero.mpr hvz) (mul_ne_zero hv (sub_ne_zero.mpr hz1))
  have ht0 : t ≠ 0 := div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hzc.symm) (sub_ne_zero.mpr hvr))
    (mul_ne_zero (sub_ne_zero.mpr hrc.symm) (sub_ne_zero.mpr hvz))
  have ht1 : t ≠ 1 := by
    intro he
    have hp := (div_eq_iff (mul_ne_zero (sub_ne_zero.mpr hrc.symm) (sub_ne_zero.mpr hvz))).mp he
    have hzero : (z - r) * (c - v) = 0 := by linear_combination hp
    exact mul_ne_zero (sub_ne_zero.mpr hzr) (sub_ne_zero.mpr hvc.symm) hzero
  have him : h.im = 0 := by
    have heq : h = (F 2 - F 4) / (F 0 - F 1) := by
      rw [h24, h01]
      dsimp only [h]
      field_simp [hv, sub_ne_zero.mpr hrc, sub_ne_zero.mpr hz1] <;> ring
    rw [heq]
    exact t7_chord_ratios_real hκ (hreal 2 4 (by decide) (by decide))
      (hreal 0 1 (by decide) (by decide))
  have ht_im : t.im = 0 := by
    have heq : t = (-((F 0 - F 2) / (F 0 - F 1))) / (h - 1) := by
      rw [h02, h01, hh1']
      dsimp only [t]
      field_simp [hv, sub_ne_zero.mpr hrc, sub_ne_zero.mpr hrc.symm,
        sub_ne_zero.mpr hvz, sub_ne_zero.mpr hz1] <;> ring
    rw [heq]
    have hd := t7_chord_ratios_real hκ (hreal 0 2 (by decide) (by decide))
      (hreal 0 1 (by decide) (by decide))
    simp [Complex.div_im, Complex.sub_im, him, hd]
  have hk_im : k.im = 0 := by simp [k, Complex.add_im, Complex.mul_im, Complex.sub_im, him, ht_im]
  have he_im : e.im = 0 := by
    have heq : e = -((F 7 - F 1) / (F 8 - F 2)) := by
      rw [h71, h82]
      dsimp only [e]
      field_simp [hr, sub_ne_zero.mpr hzc, sub_ne_zero.mpr hwv] <;> ring
    rw [heq]
    have h := t7_chord_ratios_real hκ (hreal 7 1 (by decide) (by decide))
      (hreal 8 2 (by decide) (by decide))
    simp [h]
  have hL : l = (k - 1) * (e + 1) := by
    dsimp only [l, k, e]
    rw [hh1']
    dsimp only [t]
    field_simp (disch := simp [hr, hv, sub_ne_zero.mpr hzc, sub_ne_zero.mpr hrc.symm,
      sub_ne_zero.mpr hvz, sub_ne_zero.mpr hz1])
    ring
  have hl_im : l.im = 0 := by
    rw [hL]
    simp [Complex.mul_im, Complex.sub_im, Complex.add_im, hk_im, he_im]
  have hs_im : s.im = 0 := by
    have heq : s = -((F 8 - F 2) / (F 0 - F 2)) := by
      rw [h82, h02]
      dsimp only [s]
      field_simp [sub_ne_zero.mpr hzc, sub_ne_zero.mpr hvr, sub_ne_zero.mpr hvr.symm] <;> ring
    rw [heq]
    have h := t7_chord_ratios_real hκ (hreal 8 2 (by decide) (by decide))
      (hreal 0 2 (by decide) (by decide))
    simp [h]
  have hsz : s ≠ 0 := div_ne_zero (mul_ne_zero hr (sub_ne_zero.mpr hwv)) (sub_ne_zero.mpr hvr)
  refine ⟨h, t, k, l, s, him, ht_im, hk_im, hl_im, hs_im, hh0, hh1, ht0, ht1, rfl,
    hsz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx : 1 + (h - 1) * v = (v - 1) / (z - 1) := by
      rw [hh1']
      field_simp [hv, sub_ne_zero.mpr hz1] <;> ring
    rw [hx]
    dsimp only [h]
    field_simp (disch := simp [hv, sub_ne_zero.mpr hv1, sub_ne_zero.mpr hz1])
    ring
  · have hden : v - r - t * (v - z) = (v - r) * (z - r) / (c - r) := by
      dsimp only [t]
      field_simp [sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hvz] <;> ring
    have hden_ne : v - r - t * (v - z) ≠ 0 := by
      rw [hden]
      exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hvr) (sub_ne_zero.mpr hzr))
        (sub_ne_zero.mpr hrc.symm)
    apply (eq_div_iff hden_ne).mpr
    dsimp only [t]
    field_simp [sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hvz] <;> ring
  · dsimp only [l]
    field_simp [hv, hr] <;> ring
  · dsimp only [s]
    field_simp [hr, sub_ne_zero.mpr hvr] <;> ring
  · have h := hreal 0 2 (by decide) (by decide)
    rw [h02, show r - v = -(v - r) by ring, mul_neg, mul_neg, Complex.neg_re, neg_eq_zero] at h
    exact h
  · calc
      v - z = (h - 1) * (v * (z - 1)) :=
        ((eq_div_iff (mul_ne_zero hv (sub_ne_zero.mpr hz1))).mp hh1').symm
      _ = _ := by ring
  · dsimp only [t]
    field_simp [sub_ne_zero.mpr hrc.symm, sub_ne_zero.mpr hvz] <;> ring
  · change e = _
    have hk1 : k - 1 ≠ 0 := by
      change 1 + t * (h - 1) - 1 ≠ 0
      rw [show 1 + t * (h - 1) - 1 = t * (h - 1) by ring]
      exact mul_ne_zero ht0 (sub_ne_zero.mpr hh1)
    rw [hL]
    field_simp [hk1] <;> ring

end

end MOC
