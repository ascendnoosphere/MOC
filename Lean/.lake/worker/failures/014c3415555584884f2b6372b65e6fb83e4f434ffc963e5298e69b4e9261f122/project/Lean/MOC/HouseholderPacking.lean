import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Fractional triangle packing for a four-coordinate Householder reflection. -/

open BigOperators

namespace MOC

private theorem exists_packing_coordinates (d lx ly lz ux uy uz : ℝ)
    (hlx : 0 ≤ lx) (hly : 0 ≤ ly) (hlz : 0 ≤ lz)
    (hx : lx ≤ ux) (hy : ly ≤ uy) (hz : lz ≤ uz)
    (hux : ux ≤ d) (huy : uy ≤ d) (huz : uz ≤ d)
    (hs : d ≤ ux + uy + uz) (hxy : lx + ly - d ≤ uz)
    (hxz : lx + lz - d ≤ uy) (hyz : ly + lz - d ≤ ux) :
    ∃ x y z : ℝ, (lx ≤ x ∧ x ≤ ux) ∧ (ly ≤ y ∧ y ≤ uy) ∧ (lz ≤ z ∧ z ≤ uz) ∧
      d ≤ x + y + z ∧ x + y - z ≤ d ∧ x + z - y ≤ d ∧ y + z - x ≤ d := by
  by_cases hlow : d ≤ lx + ly + lz
  · -- Raising the subtracted coordinate repairs a violated triangle inequality.
    by_cases h₁ : lx + ly - lz ≤ d
    · by_cases h₂ : lx + lz - ly ≤ d
      · by_cases h₃ : ly + lz - lx ≤ d
        · exact ⟨lx, ly, lz, ⟨le_rfl, hx⟩, ⟨le_rfl, hy⟩, ⟨le_rfl, hz⟩, hlow, h₁, h₂, h₃⟩
        · exact ⟨ly + lz - d, ly, lz, ⟨by linarith, hyz⟩, ⟨le_rfl, hy⟩,
            ⟨le_rfl, hz⟩, by linarith, by linarith, by linarith, by linarith⟩
      · exact ⟨lx, lx + lz - d, lz, ⟨le_rfl, hx⟩, ⟨by linarith, hxz⟩,
          ⟨le_rfl, hz⟩, by linarith, by linarith, by linarith, by linarith⟩
    · exact ⟨lx, ly, lx + ly - d, ⟨le_rfl, hx⟩, ⟨le_rfl, hy⟩,
        ⟨by linarith, hxy⟩, by linarith, by linarith, by linarith, by linarith⟩
  · -- Interpolate to the slice x + y + z = d.
    let width := ux + uy + uz - (lx + ly + lz)
    let s := (d - (lx + ly + lz)) / width
    have hwidth : 0 < width := by dsimp [width]; linarith
    have hs₀ : 0 ≤ s := div_nonneg (by linarith) hwidth.le
    have hs₁ : s ≤ 1 := by
      dsimp only [s]
      apply (div_le_iff₀ hwidth).2
      dsimp [width]
      linarith
    have hsMul : s * width = d - (lx + ly + lz) := div_mul_cancel₀ _ hwidth.ne'
    have within (l u : ℝ) (hlu : l ≤ u) : l ≤ l + s * (u - l) ∧ l + s * (u - l) ≤ u := by
      have h₀ := mul_nonneg hs₀ (sub_nonneg.mpr hlu)
      have h₁ := mul_le_mul_of_nonneg_right hs₁ (sub_nonneg.mpr hlu)
      rw [one_mul] at h₁
      exact ⟨by linarith, by linarith⟩
    let x := lx + s * (ux - lx)
    let y := ly + s * (uy - ly)
    let z := lz + s * (uz - lz)
    have htotal : x + y + z = d := calc
      _ = lx + ly + lz + s * width := by dsimp only [x, y, z, width]; ring
      _ = d := by rw [hsMul]; ring
    have hx₀ : 0 ≤ x := hlx.trans (within lx ux hx).1
    have hy₀ : 0 ≤ y := hly.trans (within ly uy hy).1
    have hz₀ : 0 ≤ z := hlz.trans (within lz uz hz).1
    exact ⟨x, y, z, within lx ux hx, within ly uy hy, within lz uz hz,
      htotal.ge, by linarith, by linarith, by linarith⟩

private theorem packing_upper_sum {d a b c : ℝ} (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : d ≤ a + b + c) :
    d ≤ min d a + min d b + min d c := by
  by_cases hda : d ≤ a
  · rw [min_eq_left hda]
    linarith [le_min hd hb, le_min hd hc]
  by_cases hdb : d ≤ b
  · rw [min_eq_left hdb]
    linarith [le_min hd ha, le_min hd hc]
  by_cases hdc : d ≤ c
  · rw [min_eq_left hdc]
    linarith [le_min hd ha, le_min hd hb]
  rwa [min_eq_right (le_of_not_ge hda), min_eq_right (le_of_not_ge hdb),
    min_eq_right (le_of_not_ge hdc)]

private theorem packing_triangle_bound {d a b c : ℝ} (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : d ≤ a + b + c) :
    max 0 (d - b) + max 0 (d - c) - d ≤ min d a := by
  have hl (e : ℝ) (he : 0 ≤ e) : max 0 (d - e) ≤ d :=
    max_le hd (by linarith)
  have hu : 0 ≤ min d a := le_min hd ha
  by_cases hdb : d ≤ b
  · rw [max_eq_left (sub_nonpos.mpr hdb)]
    linarith [hl c hc]
  by_cases hdc : d ≤ c
  · rw [max_eq_left (sub_nonpos.mpr hdc)]
    linarith [hl b hb]
  rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hdb)),
    max_eq_right (sub_nonneg.mpr (le_of_not_ge hdc))]
  exact le_min (by linarith) (by linarith)

private theorem exists_four_capacity_packing
    (d e01 e02 e03 e12 e13 e23 : ℝ)
    (hd : 0 ≤ d) (hn01 : 0 ≤ e01) (hn02 : 0 ≤ e02) (hn03 : 0 ≤ e03)
    (hn12 : 0 ≤ e12) (hn13 : 0 ≤ e13) (hn23 : 0 ≤ e23)
    (hm₁ : d ≤ e01 + e23) (hm₂ : d ≤ e02 + e13) (hm₃ : d ≤ e03 + e12)
    (hs₀ : d ≤ e01 + e02 + e03) (hs₁ : d ≤ e01 + e12 + e13)
    (hs₂ : d ≤ e02 + e12 + e23) (hs₃ : d ≤ e03 + e13 + e23) :
    ∃ t : Fin 4 → ℝ, (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = d ∧
      t 0 + t 1 ≤ e01 ∧ t 0 + t 2 ≤ e02 ∧ t 0 + t 3 ≤ e03 ∧
      t 1 + t 2 ≤ e12 ∧ t 1 + t 3 ≤ e13 ∧ t 2 + t 3 ≤ e23 := by
  have hl (e : ℝ) : 0 ≤ max 0 (d - e) := le_max_left 0 (d - e)
  have hbound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : d ≤ a + b) :
      max 0 (d - b) ≤ min d a := max_le (le_min hd ha) (le_min (by linarith) (by linarith))
  obtain ⟨x, y, z, ⟨hlx, hux⟩, ⟨hly, huy⟩, ⟨hlz, huz⟩, ht, hxy, hxz, hyz⟩ :=
    exists_packing_coordinates d (max 0 (d - e23)) (max 0 (d - e13)) (max 0 (d - e12))
      (min d e01) (min d e02) (min d e03)
      (hl e23) (hl e13) (hl e12)
      (hbound hn01 hn23 hm₁) (hbound hn02 hn13 hm₂) (hbound hn03 hn12 hm₃)
      (min_le_left ..) (min_le_left ..) (min_le_left ..)
      (packing_upper_sum hd hn01 hn02 hn03 hs₀)
      (packing_triangle_bound hd hn03 hn23 hn13 (by linarith))
      (packing_triangle_bound hd hn02 hn23 hn12 (by linarith))
      (packing_triangle_bound hd hn01 hn13 hn12 (by linarith))
  have hx₀ := hux.trans (min_le_right d e01)
  have hy₀ := huy.trans (min_le_right d e02)
  have hz₀ := huz.trans (min_le_right d e03)
  have hx₁ := (le_max_right 0 (d - e23)).trans hlx
  have hy₁ := (le_max_right 0 (d - e13)).trans hly
  have hz₁ := (le_max_right 0 (d - e12)).trans hlz
  let t : Fin 4 → ℝ := ![(x + y + z - d) / 2, (d + x - y - z) / 2,
    (d + y - x - z) / 2, (d + z - x - y) / 2]
  have htn (i : Fin 4) : 0 ≤ t i := by
    fin_cases i <;> simp [t] <;> linarith
  have hts : (∑ i, t i) = d := by
    simp [Fin.sum_univ_four, t] <;> ring
  refine ⟨t, htn, hts, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [t] <;> linarith

private theorem householder_matching_capacity (a b c d : ℝ) (h : a + b + c + d = 1) :
    1 - 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ 4 * c * d + 4 * a * b := by
  nlinarith only [sq_nonneg (a + b - c - d), congrArg (fun x : ℝ => x ^ 2) h]

private theorem householder_star_capacity (a b c d : ℝ) (h : a + b + c + d = 1) :
    1 - 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ 4 * c * d + 4 * b * d + 4 * b * c := by
  nlinarith only [sq_nonneg (a - b - c - d), congrArg (fun x : ℝ => x ^ 2) h]

/-- The Householder packing inequalities indexed by their two omitted labels. -/
theorem exists_householder_triangle_packing_edges (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ t : Fin 4 → ℝ, (∀ i, 0 ≤ t i) ∧
      (∑ i, t i) = max 0 (1 - 2 * ∑ i, p i ^ 2) ∧
      t 0 + t 1 ≤ 4 * p 2 * p 3 ∧ t 0 + t 2 ≤ 4 * p 1 * p 3 ∧
      t 0 + t 3 ≤ 4 * p 1 * p 2 ∧ t 1 + t 2 ≤ 4 * p 0 * p 3 ∧
      t 1 + t 3 ≤ 4 * p 0 * p 2 ∧ t 2 + t 3 ≤ 4 * p 0 * p 1 := by
  let a := p 0
  let b := p 1
  let c := p 2
  let d := p 3
  let D := max 0 (1 - 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2))
  have ha : 0 ≤ a := hp 0
  have hb : 0 ≤ b := hp 1
  have hc : 0 ≤ c := hp 2
  have hd : 0 ≤ d := hp 3
  have h : a + b + c + d = 1 := by simpa only [Fin.sum_univ_four] using hsum
  have cap (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ 4 * x * y :=
    mul_nonneg (mul_nonneg (by norm_num) hx) hy
  have h01 := cap c d hc hd
  have h02 := cap b d hb hd
  have h03 := cap b c hb hc
  have h12 := cap a d ha hd
  have h13 := cap a c ha hc
  have h23 := cap a b ha hb
  have bound {s : ℝ} (hs : 0 ≤ s) (hu : 1 - 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ s) :
      D ≤ s := max_le hs hu
  obtain ⟨t, hn, hs, ht01, ht02, ht03, ht12, ht13, ht23⟩ :=
    exists_four_capacity_packing D _ _ _ _ _ _ (le_max_left ..)
      h01 h02 h03 h12 h13 h23
      (bound (by linarith) (householder_matching_capacity a b c d h))
      (bound (by linarith) (by linarith [householder_matching_capacity a c b d (by linarith)]))
      (bound (by linarith) (by linarith [householder_matching_capacity a d b c (by linarith)]))
      (bound (by linarith) (householder_star_capacity a b c d h))
      (bound (by linarith) (by linarith [householder_star_capacity b a c d (by linarith)]))
      (bound (by linarith) (by linarith [householder_star_capacity c a b d (by linarith)]))
      (bound (by linarith) (by linarith [householder_star_capacity d a b c (by linarith)]))
  exact ⟨t, hn, by simpa only [Fin.sum_univ_four] using hs, ht01, ht02, ht03, ht12, ht13, ht23⟩

/-- For four coordinate masses, the triangle omitting index `i` can receive a
nonnegative weight `t i` so that each edge stays within its Householder capacity. -/
theorem exists_householder_triangle_packing (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ t : Fin 4 → ℝ, (∀ i, 0 ≤ t i) ∧
      (∑ i, t i) = max 0 (1 - 2 * ∑ i, p i ^ 2) ∧
      ∀ i j, i ≠ j → t i + t j ≤ 4 * (∏ k ∈ (Finset.univ.erase i).erase j, p k) := by
  obtain ⟨t, hn, hs, ht01, ht02, ht03, ht12, ht13, ht23⟩ :=
    exists_householder_triangle_packing_edges p hp hsum
  refine ⟨t, hn, hs, ?_⟩
  have hC01 : ((Finset.univ : Finset (Fin 4)).erase 0).erase 1 = {2, 3} := by decide
  have hC02 : ((Finset.univ : Finset (Fin 4)).erase 0).erase 2 = {1, 3} := by decide
  have hC03 : ((Finset.univ : Finset (Fin 4)).erase 0).erase 3 = {1, 2} := by decide
  have hC12 : ((Finset.univ : Finset (Fin 4)).erase 1).erase 2 = {0, 3} := by decide
  have hC13 : ((Finset.univ : Finset (Fin 4)).erase 1).erase 3 = {0, 2} := by decide
  have hC23 : ((Finset.univ : Finset (Fin 4)).erase 2).erase 3 = {0, 1} := by decide
  have hcProd (i j : Fin 4) :
      ((Finset.univ : Finset (Fin 4)).erase i).erase j = (Finset.univ.erase j).erase i := by
    ext k
    simp only [Finset.mem_erase]
    constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact ⟨h₂, h₁, h₃⟩
  have hlt (i j : Fin 4) (hij : i < j) :
      t i + t j ≤ 4 * (∏ k ∈ (Finset.univ.erase i).erase j, p k) := by
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
    all_goals
      first
      | rw [hC01, Finset.prod_pair (by decide : (2 : Fin 4) ≠ 3)]
        simpa only [mul_assoc] using ht01
      | rw [hC02, Finset.prod_pair (by decide : (1 : Fin 4) ≠ 3)]
        simpa only [mul_assoc] using ht02
      | rw [hC03, Finset.prod_pair (by decide : (1 : Fin 4) ≠ 2)]
        simpa only [mul_assoc] using ht03
      | rw [hC12, Finset.prod_pair (by decide : (0 : Fin 4) ≠ 3)]
        simpa only [mul_assoc] using ht12
      | rw [hC13, Finset.prod_pair (by decide : (0 : Fin 4) ≠ 2)]
        simpa only [mul_assoc] using ht13
      | rw [hC23, Finset.prod_pair (by decide : (0 : Fin 4) ≠ 1)]
        simpa only [mul_assoc] using ht23
  intro i j hij
  rcases lt_or_gt_of_ne hij with h₁ | h₂
  · exact hlt i j h₁
  · rw [hcProd i j, add_comm]
    exact hlt j i h₂

end MOC
