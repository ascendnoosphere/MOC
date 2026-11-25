import MOC.ContactRectangle
import MOC.FourT18Ratios
import MOC.FourT18Spectral
import MOC.FourT18T20Minor
import MOC.FourCoincidence
import MOC.ProjectivePole
import MOC.TwoExceptions
import Mathlib.Tactic.Lift

/-! The matching contacts in case T18 imply both spectral inequalities. -/

namespace MOC

noncomputable section

private theorem t18_projective_products (a b : Fin 4 → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hn : ∀ i j, a i + b j ≠ 0) :
    ∃ (K : ℂ) (X Y : Fin 4 → ℂ), K ≠ 0 ∧ X 1 = 1 ∧ Y 1 = 0 ∧ Function.Injective X ∧
      (∀ {i j}, i ≠ 0 → j ≠ 0 → Y i = Y j → i = j) ∧
      (∀ i j, j ≠ 0 → X i ≠ Y j) ∧
      ∀ i, matchingProduct a b (fourPerm i).symm =
        K * fourT18PoleProduct (X 0) (X 2) (X 3) (Y 2) (Y 3) i := by
  obtain ⟨c, A, C, hc, _, _, hA, hC, hsep, hp⟩ :=
    exists_projective_pole_chart a b 0 1 0 (by decide) ha hb hn
  let d := A 1 - C 1
  let X (i : Fin 4) := (A i - C 1) / d
  let Y (i : Fin 4) := (C i - C 1) / d
  have hd : d ≠ 0 := sub_ne_zero.mpr (hsep 1 1 (by decide))
  have hX : X 1 = 1 := div_self hd
  have hY : Y 1 = 0 := by simp [Y]
  have hinj {x y : ℂ} (h : (x - C 1) / d = (y - C 1) / d) : x = y := by
    have he := (div_left_inj' hd).mp h
    linear_combination he
  have hvec : X = ![X 0, 1, X 2, X 3] := by
    funext i
    fin_cases i
    · rfl
    · exact hX
    · rfl
    · rfl
  have hprod (σ : Equiv.Perm (Fin 4)) :
      (∏ j ∈ Finset.univ.erase (0 : Fin 4), (A (σ j) - C j)) =
        (A (σ 1) - C 1) * (A (σ 2) - C 2) * (A (σ 3) - C 3) := by
    rw [show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide,
      Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
      Finset.prod_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
      Finset.prod_singleton, mul_assoc]
  refine ⟨c * d ^ 3, X, Y, mul_ne_zero hc (pow_ne_zero _ hd), hX, hY, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hA (hinj hij)
  · intro i j hi hj hij
    exact hC hi hj (hinj hij)
  · intro i j hj hij
    exact hsep i j hj (hinj hij)
  · intro i
    let σ := (fourPerm i).symm
    rw [hp, hprod]
    have hF : fourT18PoleProduct (X 0) (X 2) (X 3) (Y 2) (Y 3) i =
        (X (σ 1) - Y 1) * (X (σ 2) - Y 2) * (X (σ 3) - Y 3) := by
      simp only [fourT18PoleProduct, hY, sub_zero]
      rw [← hvec]
    rw [hF]
    dsimp only [X, Y]
    field_simp [hd] <;> ring

private theorem t18_ratio_real {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) :
    (z / w).im = 0 := by simp [Complex.div_im, hz, hw]

set_option maxHeartbeats 2500000 in
private theorem t18_projected_inequalities (x b z v w : ℂ) (μ : ℝ)
    (hμ : μ ≠ 0) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hb1 : b ≠ 1) (hbz : b ≠ z) (hbv : b ≠ v) (hbw : b ≠ w)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzv : z ≠ v) (hzw : z ≠ w)
    (hv : v ≠ 0) (hv1 : v ≠ 1) (hvw : v ≠ w)
    (hc : ∀ i ∈ fourT18ContactIndices,
      (fourT18PoleProduct x b z v w i / fourT18PoleProduct x b z v w 0).im = 0)
    (hn : ∀ i, 0 ≤ -μ * (fourT18PoleProduct x b z v w i /
      fourT18PoleProduct x b z v w 0).im) :
    let g (i : Fin 24) := -μ * (fourT18PoleProduct x b z v w i /
      fourT18PoleProduct x b z v w 0).im
    0 ≤ g 18 - g 2 ∧ 0 ≤ g 2 - g 4 + g 10 - g 12 + g 13 + g 18 := by
  let F := fourT18PoleProduct x b z v w
  let R (i : Fin 24) := F i / F 0
  let g (i : Fin 24) := -μ * (R i).im
  change 0 ≤ g 18 - g 2 ∧ 0 ≤ g 2 - g 4 + g 10 - g 12 + g 13 + g 18
  change ∀ i, 0 ≤ g i at hn
  change ∀ i ∈ fourT18ContactIndices, (R i).im = 0 at hc
  have h0 : F 0 = (b - v) * (z - w) := by change 1 * (b - v) * (z - w) = _; ring
  have hF1 : F 1 = 1 * (z - v) * (b - w) := rfl
  have hF3 : F 3 = z * (1 - v) * (b - w) := rfl
  have hF6 : F 6 = x * (b - v) * (z - w) := rfl
  have hF8 : F 8 = x * (1 - v) * (z - w) := rfl
  have hF0n : F 0 ≠ 0 := by rw [h0]; exact mul_ne_zero (sub_ne_zero.mpr hbv) (sub_ne_zero.mpr hzw)
  let h := z * (1 - v) / (z - v)
  let k := (b - 1) / (v - 1)
  let l := R 1
  have hh : h ≠ 0 := div_ne_zero (mul_ne_zero hz0 (sub_ne_zero.mpr hv1.symm)) (sub_ne_zero.mpr hzv)
  have hk : k ≠ 0 := div_ne_zero (sub_ne_zero.mpr hb1) (sub_ne_zero.mpr hv1)
  have hl : l ≠ 0 := by
    change F 1 / F 0 ≠ 0
    rw [hF1, one_mul]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hzv) (sub_ne_zero.mpr hbw)) hF0n
  have hh1 : h ≠ 1 := by
    intro he
    change z * (1 - v) / (z - v) = 1 at he
    have he' := (div_eq_iff (sub_ne_zero.mpr hzv)).mp he
    have hz : v * (1 - z) = 0 := by linear_combination he'
    exact mul_ne_zero hv (sub_ne_zero.mpr hz1.symm) hz
  have hk1 : k ≠ 1 := by
    intro he
    change (b - 1) / (v - 1) = 1 at he
    have he' := (div_eq_iff (sub_ne_zero.mpr hv1)).mp he
    have hz : b = v := by linear_combination he'
    exact hbv hz
  have hl1 : l ≠ 1 := by
    intro he
    change F 1 / F 0 = 1 at he
    have he' := (div_eq_iff hF0n).mp he
    rw [h0, hF1] at he'
    have hz : (b - z) * (w - v) = 0 := by linear_combination he'
    exact mul_ne_zero (sub_ne_zero.mpr hbz) (sub_ne_zero.mpr hvw.symm) hz
  have hR6 : R 6 = x := by
    dsimp only [R]
    rw [hF6, h0]
    field_simp [sub_ne_zero.mpr hbv, sub_ne_zero.mpr hzw] <;> ring
  have hR8 : R 8 = x * (1 - v) / (b - v) := by
    dsimp only [R]
    rw [hF8, h0]
    field_simp [sub_ne_zero.mpr hbv, sub_ne_zero.mpr hzw] <;> ring
  have hhR : h = R 3 / l := by
    dsimp only [h, l, R]
    rw [hF3, hF1, h0, one_mul]
    field_simp [sub_ne_zero.mpr hzv, sub_ne_zero.mpr hbw, sub_ne_zero.mpr hbv,
      sub_ne_zero.mpr hzw] <;> ring
  have hkR : k = 1 - x / R 8 := by
    dsimp only [k]
    rw [hR8]
    field_simp [hx0, sub_ne_zero.mpr hv1, sub_ne_zero.mpr hv1.symm, sub_ne_zero.mpr hbv] <;> ring
  have hxim : x.im = 0 := by rw [← hR6]; exact hc 6 (by decide)
  have hlim : l.im = 0 := hc 1 (by decide)
  have hhim : h.im = 0 := by rw [hhR]; exact t18_ratio_real (hc 3 (by decide)) hlim
  have hkim : k.im = 0 := by
    rw [hkR, Complex.sub_im, Complex.one_im, t18_ratio_real hxim (hc 8 (by decide)), sub_self]
  have hb : b = 1 + k * (v - 1) := by
    dsimp only [k]
    field_simp [sub_ne_zero.mpr hv1] <;> ring
  have hz : z * (v + h - 1) = h * v := by
    have hi : h * (z - v) = z * (1 - v) := div_mul_cancel₀ _ (sub_ne_zero.mpr hzv)
    linear_combination hi
  have ht : v + h - 1 ≠ 0 := by
    intro he
    rw [he, mul_zero] at hz
    exact mul_ne_zero hh hv hz.symm
  have hD : b + h * (k - 1) ≠ 0 := by
    intro he
    have hi : (b - z) * (v + h - 1) = (v - 1) * (b + h * (k - 1)) := by
      rw [hb]
      linear_combination -hz
    rw [he, mul_zero] at hi
    exact mul_ne_zero (sub_ne_zero.mpr hbz) ht hi
  have hld : l = (b - w) * (z - v) / ((b - v) * (z - w)) := by
    dsimp only [l, R]
    rw [hF1, h0, one_mul, mul_comm (z - v)]
  have hW : (z - v) / (z - w) = (l * (k - 1) * (v + h - 1) + v) / (b + h * (k - 1)) := by
    have hL : l * ((b - v) * (z - w)) = (b - w) * (z - v) :=
      (eq_div_iff (mul_ne_zero (sub_ne_zero.mpr hbv) (sub_ne_zero.mpr hzw))).mp hld
    have hB : (b - z) * (v + h - 1) = (v - 1) * (b + h * (k - 1)) := by
      rw [hb]
      linear_combination -hz
    have hV : (z - v) * (v + h - 1) = v * (1 - v) := by linear_combination hz
    have hq : b - v = (k - 1) * (v - 1) := by rw [hb]; ring
    apply (div_eq_div_iff (sub_ne_zero.mpr hzw) hD).mpr
    apply (mul_right_cancel₀ (sub_ne_zero.mpr hv1))
    have hL' : (z - v) * (b - z) = l * ((b - v) * (z - w)) - (z - v) * (z - w) := by
      linear_combination -hL
    calc
      _ = ((z - v) * (b - z)) * (v + h - 1) := by
        rw [mul_assoc (z - v), mul_comm (b + h * (k - 1)) (v - 1), ← hB]
        ring
      _ = _ := by
        rw [hL', hq]
        linear_combination -(z - w) * hV
  have hq : k - 1 ≠ 0 := sub_ne_zero.mpr hk1
  obtain ⟨r2, r5, r9, r10, r13, r14, rA, rB, rEA, rEB⟩ :=
    fourT18_exact_pole_ratios x b z v w h k l hb hz hW hld hh hv hv1 hq ht hD hbv hzv hzw
  change R 2 = _ at r2
  change R 5 = _ at r5
  change R 9 = _ at r9
  change R 10 = _ * R 5 at r10
  change R 13 = _ * R 14 at r13
  change R 14 = _ at r14
  change R 18 - R 2 = _ at rA
  change R 2 - R 4 + R 10 - R 12 + R 13 + R 18 = _ at rB
  change (1 + h * (k - 1)) * (R 18 - R 2) = _ at rEA
  change (1 + h * (k - 1)) * (R 2 - R 4 + R 10 - R 12 + R 13 + R 18) = _ at rEB
  have hbim : b.im = k.re * v.im := by
    rw [hb]
    simp [Complex.add_im, Complex.mul_im, Complex.sub_im, hkim]
  have hDim : (b + h * (k - 1)).im = k.re * v.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.sub_im, hhim, hkim, hbim]
  by_cases hvim : v.im = 0
  · have hbim0 : b.im = 0 := by simp [hbim, hvim]
    have hR14i : (R 14).im = 0 := by
      rw [r14]
      simp [Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.add_im, hxim, hkim, hvim]
    have hR13i : (R 13).im = 0 := by
      rw [r13]
      simp [Complex.mul_im, Complex.sub_im, hR14i, hhim, hlim, hkim]
    have hAi : (R 18 - R 2).im = 0 := by
      rw [rA]
      simp [Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.add_im,
        hDim, hbim0, hxim, hkim, hhim, hlim, hvim]
    have hBi : (R 2 - R 4 + R 10 - R 12 + R 13 + R 18).im = 0 := by
      rw [rB]
      simp [Complex.div_im, Complex.mul_im, Complex.sub_im, Complex.add_im,
        hDim, hbim0, hR13i, hxim, hkim, hhim, hlim, hvim]
    simp only [Complex.sub_im] at hAi
    simp only [Complex.sub_im, Complex.add_im] at hBi
    dsimp only [g]
    exact ⟨le_of_eq (by linear_combination μ * hAi), le_of_eq (by linear_combination μ * hBi)⟩
  lift x to ℝ using hxim
  lift h to ℝ using hhim with hReal hCast
  lift k to ℝ using hkim with kReal kCast
  lift l to ℝ using hlim with lReal lCast
  let D := b + (hReal : ℂ) * ((kReal : ℂ) - 1)
  let ρ := μ * v.im
  let q := kReal - 1
  have hqR : q ≠ 0 := by exact_mod_cast hq
  have hqC : (kReal : ℂ) - 1 = (q : ℂ) := by simp [q]
  have hqCn : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqR
  have hk0 : kReal ≠ 0 := by exact_mod_cast hk
  have hDiff : D.im = kReal * v.im := by simpa only [D, Complex.ofReal_re] using hDim
  have hNormD : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD
  have hNormV : 0 < Complex.normSq v := Complex.normSq_pos.mpr hv
  have hNorm1 : 0 < Complex.normSq (v - 1) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hv1)
  have hi1 : (v - 1).im = v.im := by simp
  have h2 : g 2 = ρ * kReal / q := by
    dsimp only [g, ρ]
    rw [r2, hqC, Complex.sub_im, Complex.one_im, Complex.div_ofReal_im, Complex.im_ofReal_mul]
    ring
  have h5 : g 5 * Complex.normSq D = ρ * hReal * (hReal - 1) * q * (lReal - 1) * kReal := by
    have hr : R 5 = (hReal : ℂ) + ((hReal * (hReal - 1) * q * (lReal - 1) : ℝ) : ℂ) / D := by
      dsimp only [D, q]
      push_cast
      exact r5
    dsimp only [g, ρ]
    rw [hr, Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, zero_div, zero_sub, hDiff]
    field_simp [hNormD.ne'] <;> ring
  have h9 : g 9 * Complex.normSq v = ρ * lReal * x * (hReal - 1) := by
    have hr : R 9 = ((lReal * x : ℝ) : ℂ) + ((lReal * x * (hReal - 1) : ℝ) : ℂ) / v := by
      push_cast
      exact r9
    dsimp only [g, ρ]
    rw [hr, Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, zero_div, zero_sub]
    field_simp [hNormV.ne'] <;> ring
  have h14 : g 14 * Complex.normSq (v - 1) = ρ * (x - 1) / q := by
    have hr : R 14 = ((-1 / q : ℝ) : ℂ) + (((x - 1) / q : ℝ) : ℂ) / (v - 1) := by
      rw [r14, hqC]
      push_cast
      field_simp [hqCn, sub_ne_zero.mpr hv1] <;> ring
    dsimp only [g, ρ]
    rw [hr, Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, zero_div, zero_sub, hi1]
    field_simp [hNorm1.ne'] <;> ring
  have h10 : g 10 = (-x / (hReal * q)) * g 5 := by
    have hr : R 10 = ((-x / (hReal * q) : ℝ) : ℂ) * R 5 := by
      dsimp only [q]
      push_cast
      exact r10
    dsimp only [g]
    rw [hr, Complex.im_ofReal_mul]
    ring
  have h13 : g 13 = (-hReal * lReal * q) * g 14 := by
    have hr : R 13 = ((-hReal * lReal * q : ℝ) : ℂ) * R 14 := by
      dsimp only [q]
      push_cast
      exact r13
    dsimp only [g]
    rw [hr, Complex.im_ofReal_mul]
    ring
  let e := 1 + hReal * q
  let L := 1 + hReal * lReal * q
  let P := x + hReal * q
  have hA : e * (g 18 - g 2) = P * g 5 + L * g 14 := by
    have hr : (e : ℂ) * (R 18 - R 2) = (P : ℂ) * R 5 + (L : ℂ) * R 14 +
        ((lReal * x * e + x / q - hReal * q * (1 + hReal * lReal) - 1 : ℝ) : ℂ) := by
      dsimp only [e, L, P, q]
      push_cast
      exact rEA
    have hi := congrArg Complex.im hr
    simp only [Complex.im_ofReal_mul, Complex.add_im, Complex.sub_im, Complex.ofReal_im, add_zero] at hi
    dsimp only [g]
    linear_combination -μ * hi
  have hB : e * (g 2 - g 4 + g 10 - g 12 + g 13 + g 18) =
      -P / (hReal * q) * g 5 - hReal * q * L * g 14 := by
    have hr : (e : ℂ) * (R 2 - R 4 + R 10 - R 12 + R 13 + R 18) =
        ((-P / (hReal * q) : ℝ) : ℂ) * R 5 - ((hReal * q * L : ℝ) : ℂ) * R 14 +
          (((x - 1) * (e * (lReal - 1) - hReal) + hReal * (lReal - 1) : ℝ) : ℂ) := by
      dsimp only [e, L, P, q]
      push_cast
      exact rEB
    have hi := congrArg Complex.im hr
    simp only [Complex.im_ofReal_mul, Complex.add_im, Complex.sub_im, Complex.ofReal_im, add_zero] at hi
    dsimp only [g]
    linear_combination -μ * hi
  have hg2 : 0 < g 2 := by
    apply lt_of_le_of_ne (hn 2)
    rw [h2]
    exact (div_ne_zero (mul_ne_zero (mul_ne_zero hμ hvim) hk0) hqR).symm
  apply fourT18_inequalities_of_projected_kernels x hReal kReal lReal _ _ _ g
    (by exact_mod_cast hx0) (by exact_mod_cast hx1) (by exact_mod_cast hh) (by exact_mod_cast hh1)
    hk0 (by exact_mod_cast hk1) (by exact_mod_cast hl) (by exact_mod_cast hl1)
    hNormD hNormV hNorm1 hg2 hn _ _ h10 h13 _ hA hB
  · rw [h5, h2]
    change _ = hReal * (hReal - 1) * q ^ 2 * (lReal - 1) * (ρ * kReal / q)
    field_simp [hqR] <;> ring
  · rw [h9, h2]
    change _ = lReal * x * ((hReal - 1) * q / kReal) * (ρ * kReal / q)
    field_simp [hqR, hk0] <;> ring
  · rw [h14, h2]
    field_simp [hqR, hk0] <;> ring


set_option maxHeartbeats 1800000 in
/-- For simple spectra with no opposite entries, the prescribed T18
contacts imply both spectral inequalities of the minor certificate. -/
theorem fourT18_spectral_inequalities (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i + b j ≠ 0) (hη : η ≠ 0)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT18ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H) :
    let g (i : Fin 24) := (η * matchingProduct a b (fourPerm i).symm).re - H
    0 ≤ g 18 - g 2 ∧ 0 ≤ g 2 - g 4 + g 10 - g 12 + g 13 + g 18 := by
  have hp0 : (fourPerm 0).symm = 1 := by decide
  have hp1 : (fourPerm 1).symm = Equiv.swap 2 3 := by decide
  have hp6 : (fourPerm 6).symm = Equiv.swap 0 1 := by decide
  have hp7 : (fourPerm 7).symm = Equiv.swap 0 1 * Equiv.swap 2 3 := by decide
  have hH := matchingProduct_swap_rectangle_height_zero ha hb hη
    (by simpa only [hp0] using hc 0 (by decide))
    (by simpa only [hp6] using hc 6 (by decide))
    (by simpa only [hp1] using hc 1 (by decide))
    (by simpa only [hp7] using hc 7 (by decide))
  subst H
  obtain ⟨K, X, Y, hK, hX1, hY1, hX, hY, hXY, hprod⟩ := t18_projective_products a b ha hb hab
  let x := X 0
  let p := X 2
  let z := X 3
  let v := Y 2
  let w := Y 3
  let F := fourT18PoleProduct x p z v w
  let R (i : Fin 24) := F i / F 0
  let P := η * K * F 0
  have hx0 : x ≠ 0 := by rw [← hY1]; exact hXY 0 1 (by decide)
  have hx1 : x ≠ 1 := by rw [← hX1]; exact hX.ne (by decide : (0 : Fin 4) ≠ 1)
  have hp1 : p ≠ 1 := by rw [← hX1]; exact hX.ne (by decide : (2 : Fin 4) ≠ 1)
  have hpz : p ≠ z := hX.ne (by decide : (2 : Fin 4) ≠ 3)
  have hpv : p ≠ v := hXY 2 2 (by decide)
  have hpw : p ≠ w := hXY 2 3 (by decide)
  have hz0 : z ≠ 0 := by rw [← hY1]; exact hXY 3 1 (by decide)
  have hz1 : z ≠ 1 := by rw [← hX1]; exact hX.ne (by decide : (3 : Fin 4) ≠ 1)
  have hzv : z ≠ v := hXY 3 2 (by decide)
  have hzw : z ≠ w := hXY 3 3 (by decide)
  have hv0 : v ≠ 0 := by
    rw [← hY1]
    exact fun he => (by decide : (2 : Fin 4) ≠ 1) (hY (by decide) (by decide) he)
  have hv1 : v ≠ 1 := by
    rw [← hX1]
    exact (hXY 1 2 (by decide)).symm
  have hvw : v ≠ w :=
    fun he => (by decide : (2 : Fin 4) ≠ 3) (hY (by decide) (by decide) he)
  have hF0 : F 0 ≠ 0 := by
    change 1 * (p - v) * (z - w) ≠ 0
    rw [one_mul]
    exact mul_ne_zero (sub_ne_zero.mpr hpv) (sub_ne_zero.mpr hzw)
  have hP0 : P ≠ 0 := mul_ne_zero (mul_ne_zero hη hK) hF0
  have hP : P.re = 0 := by
    have h := hc 0 (by decide)
    rw [hprod] at h
    simpa only [P, F, mul_assoc] using h
  have hμ : P.im ≠ 0 := by
    intro hi
    exact hP0 (Complex.ext (by simpa using hP) (by simpa using hi))
  have hg (i : Fin 24) : (η * matchingProduct a b (fourPerm i).symm).re = -P.im * (R i).im := by
    have he : η * matchingProduct a b (fourPerm i).symm = P * R i := by
      rw [hprod]
      dsimp only [P, R]
      change η * (K * F i) = (η * K * F 0) * (F i / F 0)
      field_simp [hF0] <;> ring
    rw [he, Complex.mul_re, hP, zero_mul, zero_sub, neg_mul]
  have hRc (i : Fin 24) (hi : i ∈ fourT18ContactIndices) : (R i).im = 0 := by
    have hh := hc i hi
    rw [hg] at hh
    exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr hμ)
  have hRn (i : Fin 24) : 0 ≤ -P.im * (R i).im := by rw [← hg]; exact hn i
  have h := t18_projected_inequalities x p z v w P.im hμ hx0 hx1 hp1 hpz hpv hpw hz0 hz1
    hzv hzw hv0 hv1 hvw hRc hRn
  simpa only [sub_zero, hg] using h

/-- The T18 lower support bound holds at the prescribed six contacts,
including configurations with more contacts or spectral collisions. -/
theorem fourT18_support (a b : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct a b (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT18ContactIndices, (η * matchingProduct a b (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    H ≤ (η * determinantValue a b U).re := by
  by_cases hna : ¬ Function.Injective a
  · exact four_lower_support_of_holds a b η H U
      (holds_four_of_repeated_spectrum a b U hU (Or.inl hna)) hn
  by_cases hnb : ¬ Function.Injective b
  · exact four_lower_support_of_holds a b η H U
      (holds_four_of_repeated_spectrum a b U hU (Or.inr hnb)) hn
  by_cases hzero : ∃ i j, a i + b j = 0
  · obtain ⟨i, j, hij⟩ := hzero
    exact four_lower_support_of_holds a b η H U (holds_four_of_opposite_entries a b U hU hij) hn
  by_cases hη : η = 0
  · simpa [hη] using hn 0
  have hab (i j : Fin 4) : a i + b j ≠ 0 := fun h => hzero ⟨i, j, h⟩
  obtain ⟨hA, hB⟩ := fourT18_spectral_inequalities a b η H (not_not.mp hna) (not_not.mp hnb) hab hη hn hc
  exact fourT18_support_of_two_inequalities a b η H hn hc U hU hA hB

end

end MOC
