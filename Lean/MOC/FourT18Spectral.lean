import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The sign calculation for the T18 spectral inequalities. -/

namespace MOC

noncomputable section

private theorem t18_sign_region (x h k l : ℝ) (hk : k ≠ 0) (hk1 : k ≠ 1)
    (hxk : 0 < (x - 1) / k) (hxh : 0 < -x / (h * (k - 1)))
    (hlh : 0 < -h * l * (k - 1)) (hkh : 0 < (h - 1) * (k - 1) / k)
    (hl1 : 0 < h * (h - 1) * (l - 1)) :
    (0 < h ∧ h < 1 ∧ 0 < k ∧ k < 1 ∧ 0 < l ∧ l < 1 ∧ 1 < x) ∨
    (1 < h ∧ k < 0 ∧ 1 < l ∧ 0 < x ∧ x < 1) := by
  have hxl : 0 < x * l := by
    have hprod := mul_pos hxh hlh
    have heq : (-x / (h * (k - 1))) * (-h * l * (k - 1)) = x * l := by
      have hd : h * (k - 1) ≠ 0 := (div_pos_iff.mp hxh).elim
        (fun a => a.2.ne') (fun a => a.2.ne)
      obtain ⟨hh0, hq0⟩ := mul_ne_zero_iff.mp hd
      field_simp [hh0, hq0] <;> ring
    rwa [heq] at hprod
  rcases lt_or_gt_of_ne hk with hkneg | hkpos
  · have hx1 : x < 1 := by
      rcases div_pos_iff.mp hxk with a | a
      · exact (not_lt_of_ge hkneg.le a.2).elim
      · exact sub_neg.mp a.1
    have hk1n : k - 1 < 0 := sub_neg.mpr (hkneg.trans zero_lt_one)
    have h1 : 1 < h := by
      rcases div_pos_iff.mp hkh with a | a
      · exact (not_lt_of_ge hkneg.le a.2).elim
      · by_contra! hn
        exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hn) hk1n.le)) a.1
    have hh : 0 < h := zero_lt_one.trans h1
    have hx : 0 < x := by
      rcases div_pos_iff.mp hxh with a | a
      · exact (not_lt_of_ge (mul_neg_of_pos_of_neg hh hk1n).le a.2).elim
      · exact neg_lt_zero.mp a.1
    have hl : 1 < l := sub_pos.mp
      (pos_of_mul_pos_right hl1 ((mul_pos hh (sub_pos.mpr h1)).le))
    exact Or.inr ⟨h1, hkneg, hl, hx, hx1⟩
  · have hx : 1 < x := sub_pos.mp ((div_pos_iff_of_pos_right hkpos).mp hxk)
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hl : 0 < l := pos_of_mul_pos_right hxl hx0.le
    have hqim : 0 < (h - 1) * (k - 1) := (div_pos_iff_of_pos_right hkpos).mp hkh
    have hklt : k < 1 := by
      by_contra! hkle
      have hkg : 0 < k - 1 := sub_pos.mpr (lt_of_le_of_ne hkle hk1.symm)
      have hhg : 1 < h := sub_pos.mp (pos_of_mul_pos_left hqim hkg.le)
      have hden : 0 < h * (k - 1) := mul_pos (zero_lt_one.trans hhg) hkg
      have hneg : 0 < -x := (div_pos_iff_of_pos_right hden).mp hxh
      exact (not_lt_of_ge (neg_nonpos.mpr hx0.le)) hneg
    have hk1n : k - 1 < 0 := sub_neg.mpr hklt
    have hh1 : h < 1 := by
      by_contra! hn
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn) hk1n.le)) hqim
    have hh : 0 < h := by
      rcases div_pos_iff.mp hxh with a | a
      · exact (not_lt_of_ge (neg_nonpos.mpr hx0.le) a.1).elim
      · by_contra! hn
        exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hn hk1n.le)) a.2
    have hl1' : l < 1 := by
      by_contra! hn
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
        (mul_neg_of_pos_of_neg hh (sub_neg.mpr hh1)).le (sub_nonneg.mpr hn))) hl1
    exact Or.inl ⟨hh, hh1, hkpos, hklt, hl, hl1', hx⟩

private theorem t18_interpolation_signs (x h k l : ℝ)
    (hr : (0 < h ∧ h < 1 ∧ 0 < k ∧ k < 1 ∧ 0 < l ∧ l < 1 ∧ 1 < x) ∨
      (1 < h ∧ k < 0 ∧ 1 < l ∧ 0 < x ∧ x < 1)) :
    h * (k - 1) < 0 ∧ 1 + h * (k - 1) ≠ 0 ∧
      0 < (x + h * (k - 1)) / (1 + h * (k - 1)) ∧
      0 < (1 + h * l * (k - 1)) / (1 + h * (k - 1)) := by
  rcases hr with ⟨hh, hh1, hk, hk1, hl, hl1, hx⟩ | ⟨hh, hk, hl, hx, hx1⟩
  · have hq : k - 1 < 0 := sub_neg.mpr hk1
    have ht := mul_neg_of_pos_of_neg hh hq
    have he : 0 < 1 + h * (k - 1) := by
      nlinarith only [hh1, mul_pos hh hk]
    have hp : 0 < x + h * (k - 1) := by linarith only [hx, he]
    have hL : 0 < 1 + h * l * (k - 1) := by
      have hlp := mul_pos (neg_pos.mpr ht) (sub_pos.mpr hl1)
      nlinarith only [he, hlp]
    exact ⟨ht, he.ne', div_pos hp he, div_pos hL he⟩
  · have ht := mul_neg_of_pos_of_neg (zero_lt_one.trans hh)
      (sub_neg.mpr (hk.trans zero_lt_one))
    have he : 1 + h * (k - 1) < 0 := by
      nlinarith only [hh, mul_neg_of_pos_of_neg (zero_lt_one.trans hh) hk]
    have hp : x + h * (k - 1) < 0 := by linarith only [hx1, he]
    have hL : 1 + h * l * (k - 1) < 0 := by
      have hlp := mul_pos (neg_pos.mpr ht) (sub_pos.mpr hl)
      nlinarith only [he, hlp]
    exact ⟨ht, he.ne, div_pos_of_neg_of_neg hp he, div_pos_of_neg_of_neg hL he⟩

/-- The exact T18 kernel identities imply the two minor inequalities.
The three positive factors are the squared norms of the original chart denominators. -/
theorem fourT18_inequalities_of_projected_kernels (x h k l d u v : ℝ) (g : Fin 24 → ℝ)
    (hx : x ≠ 0) (hx1 : x ≠ 1) (hh : h ≠ 0) (hh1 : h ≠ 1)
    (hk : k ≠ 0) (hk1 : k ≠ 1) (hl : l ≠ 0) (hl1 : l ≠ 1)
    (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) (hg2 : 0 < g 2)
    (hn : ∀ i, 0 ≤ g i)
    (hg5 : g 5 * d = h * (h - 1) * (k - 1)^2 * (l - 1) * g 2)
    (hg9 : g 9 * u = l * x * ((h - 1) * (k - 1) / k) * g 2)
    (hg10 : g 10 = (-x / (h * (k - 1))) * g 5)
    (hg13 : g 13 = (-h * l * (k - 1)) * g 14)
    (hg14 : g 14 * v = ((x - 1) / k) * g 2)
    (hA : (1 + h * (k - 1)) * (g 18 - g 2) =
      (x + h * (k - 1)) * g 5 + (1 + h * l * (k - 1)) * g 14)
    (hB : (1 + h * (k - 1)) * (g 2 - g 4 + g 10 - g 12 + g 13 + g 18) =
      (-(x + h * (k - 1)) / (h * (k - 1))) * g 5 -
        (h * (k - 1) * (1 + h * l * (k - 1))) * g 14) :
    0 ≤ g 18 - g 2 ∧ 0 ≤ g 2 - g 4 + g 10 - g 12 + g 13 + g 18 := by
  have hq := sub_ne_zero.mpr hk1
  have hg5p : 0 < g 5 := by
    refine lt_of_le_of_ne (hn 5) (Ne.symm ?_)
    intro hz
    rw [hz, zero_mul] at hg5
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hh (sub_ne_zero.mpr hh1))
      (pow_ne_zero _ hq)) (sub_ne_zero.mpr hl1)) hg2.ne') hg5.symm
  have hg14p : 0 < g 14 := by
    refine lt_of_le_of_ne (hn 14) (Ne.symm ?_)
    intro hz
    rw [hz, zero_mul] at hg14
    exact (mul_ne_zero (div_ne_zero (sub_ne_zero.mpr hx1) hk) hg2.ne') hg14.symm
  have hg10p : 0 < g 10 := by
    refine lt_of_le_of_ne (hn 10) (Ne.symm ?_)
    rw [hg10]
    exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr hx) (mul_ne_zero hh hq)) hg5p.ne'
  have hg13p : 0 < g 13 := by
    refine lt_of_le_of_ne (hn 13) (Ne.symm ?_)
    rw [hg13]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hh) hl) hq) hg14p.ne'
  have hg9p : 0 < g 9 := by
    refine lt_of_le_of_ne (hn 9) (Ne.symm ?_)
    intro hz
    rw [hz, zero_mul] at hg9
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hl hx)
      (div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hh1) hq) hk)) hg2.ne') hg9.symm
  have hxk : 0 < (x - 1) / k :=
    pos_of_mul_pos_left (hg14 ▸ mul_pos hg14p hv) hg2.le
  have hxh : 0 < -x / (h * (k - 1)) := pos_of_mul_pos_left (hg10 ▸ hg10p) hg5p.le
  have hlh : 0 < -h * l * (k - 1) := pos_of_mul_pos_left (hg13 ▸ hg13p) hg14p.le
  have hxl : 0 < l * x := by
    have hprod := mul_pos hxh hlh
    have he : (-x / (h * (k - 1))) * (-h * l * (k - 1)) = l * x := by
      field_simp [hh, hq] <;> ring
    rwa [he] at hprod
  have hkh : 0 < (h - 1) * (k - 1) / k :=
    pos_of_mul_pos_right (pos_of_mul_pos_left (hg9 ▸ mul_pos hg9p hu) hg2.le) hxl.le
  have hl1p : 0 < h * (h - 1) * (l - 1) := by
    have he : h * (h - 1) * (k - 1)^2 * (l - 1) * g 2 =
        (h * (h - 1) * (l - 1)) * ((k - 1)^2 * g 2) := by ring
    rw [he] at hg5
    exact pos_of_mul_pos_left (hg5 ▸ mul_pos hg5p hd)
      (mul_nonneg (sq_nonneg _) hg2.le)
  obtain ⟨ht, he, hp, hL⟩ := t18_interpolation_signs x h k l
    (t18_sign_region x h k l hk hk1 hxk hxh hlh hkh hl1p)
  have hPA : g 18 - g 2 =
      ((x + h * (k - 1)) / (1 + h * (k - 1))) * g 5 +
        ((1 + h * l * (k - 1)) / (1 + h * (k - 1))) * g 14 := by
    apply (mul_left_cancel₀ he)
    rw [hA]
    field_simp [he] <;> ring
  have hPB : g 2 - g 4 + g 10 - g 12 + g 13 + g 18 =
      ((x + h * (k - 1)) / (1 + h * (k - 1))) * ((-1 / (h * (k - 1))) * g 5) +
        ((1 + h * l * (k - 1)) / (1 + h * (k - 1))) * (-(h * (k - 1)) * g 14) := by
    apply (mul_left_cancel₀ he)
    rw [hB]
    field_simp [he, hh, hq] <;> ring
  have hneg : 0 < -(h * (k - 1)) := neg_pos.mpr ht
  have hinv : 0 < -1 / (h * (k - 1)) := div_pos_of_neg_of_neg (by norm_num) ht
  constructor
  · rw [hPA]
    exact (add_pos (mul_pos hp hg5p) (mul_pos hL hg14p)).le
  · rw [hPB]
    exact (add_pos (mul_pos hp (mul_pos hinv hg5p)) (mul_pos hL (mul_pos hneg hg14p))).le

end

end MOC
