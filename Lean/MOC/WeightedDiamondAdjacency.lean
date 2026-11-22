import MOC.WeightedDiamondClip
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Data.Nat.Find
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! The common-zero test suffices to prune nonadjacent crossings in a
finite coordinate cone. -/

open BigOperators
open scoped Classical

namespace MOC

noncomputable section

variable {ι κ : Type*} [DecidableEq ι] [Fintype κ]

private def positiveCoordinates (s : Finset ι) (v : ι → ℝ) : Finset ι :=
  s.filter fun i => 0 < v i

private theorem positiveCoordinates_ssubset_of_supported_sub
    (s : Finset ι) (x y : ι → ℝ) (a : ℝ)
    (hs : ∀ i ∈ s, x i = 0 → y i = 0)
    (hx : ∀ i ∈ s, 0 ≤ x i)
    (hnew : ∃ k ∈ s, 0 < x k ∧ x k - a * y k = 0) :
    positiveCoordinates s (x - a • y) ⊂ positiveCoordinates s x := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨his, ?_⟩
    by_contra! hn
    have hz := le_antisymm hn (hx i his)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hz, hs i his hz, mul_zero,
      sub_zero, lt_irrefl] at hip
  · obtain ⟨i, his, hip, hiz⟩ := hnew
    intro h
    have hi : i ∈ positiveCoordinates s x := Finset.mem_filter.mpr ⟨his, hip⟩
    have hi' : i ∈ positiveCoordinates s (x - a • y) := h.symm ▸ hi
    have h' := (Finset.mem_filter.mp hi').2
    change 0 < x i - a * y i at h'
    exact (ne_of_gt h') hiz

private theorem exists_coordinate_subtraction (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i)
    (hs : ∀ i ∈ s, x i = 0 → y i = 0)
    (hp : (positiveCoordinates s y).Nonempty) :
    ∃ a : ℝ, 0 < a ∧ (∀ i ∈ s, 0 ≤ x i - a * y i) ∧
      positiveCoordinates s (x - a • y) ⊂ positiveCoordinates s x := by
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image (positiveCoordinates s y) (fun i => x i / y i) hp
  obtain ⟨hks, hky⟩ := Finset.mem_filter.mp hk
  have hkx : 0 < x k := lt_of_le_of_ne (hx k hks) (fun h => hky.ne' (hs k hks h.symm))
  let a := x k / y k
  refine ⟨a, div_pos hkx hky, ?_, positiveCoordinates_ssubset_of_supported_sub s x y a hs hx ?_⟩
  · intro i hi
    by_cases hz : y i = 0
    · simpa only [hz, mul_zero, sub_zero] using hx i hi
    · have hiy := lt_of_le_of_ne (hy i hi) (Ne.symm hz)
      exact sub_nonneg.mpr ((le_div_iff₀ hiy).mp (hmin i (Finset.mem_filter.mpr ⟨hi, hiy⟩)))
  · exact ⟨k, hks, hkx, sub_eq_zero.mpr (div_mul_cancel₀ _ hky.ne').symm⟩

private theorem proportional_of_minimal_negative_support (W : Submodule ℝ (ι → ℝ))
    (s : Finset ι) (L : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hzero : ∀ v ∈ W, (∀ i ∈ s, v i = 0) → v = 0)
    (x y : ι → ℝ) (hxW : x ∈ W) (hyW : y ∈ W)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) (hxL : L x < 0)
    (hmin : ∀ v ∈ W, (∀ i ∈ s, 0 ≤ v i) → L v < 0 →
      (positiveCoordinates s x).card ≤ (positiveCoordinates s v).card)
    (hs : ∀ i ∈ s, x i = 0 → y i = 0) : ∃ b : ℝ, 0 ≤ b ∧ y = b • x := by
  by_cases hyz : y = 0
  · exact ⟨0, le_rfl, by simp [hyz]⟩
  have hpy : (positiveCoordinates s y).Nonempty := by
    by_contra h
    apply hyz (hzero y hyW fun i hi => ?_)
    exact le_antisymm (le_of_not_gt fun hp => h ⟨i, Finset.mem_filter.mpr ⟨hi, hp⟩⟩) (hy i hi)
  have hsub : positiveCoordinates s y ⊆ positiveCoordinates s x := by
    intro i hi
    obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨his, lt_of_le_of_ne (hx i his) (fun h => hip.ne' (hs i his h.symm))⟩
  obtain ⟨a, ha, hA, hAc⟩ := exists_coordinate_subtraction s x y hx hy hs hpy
  have hzL : 0 ≤ L (x - a • y) := by
    by_contra! hn
    exact (not_le_of_gt (Finset.card_lt_card hAc))
      (hmin _ (W.sub_mem hxW (W.smul_mem a hyW)) hA hn)
  have hyL : L y < 0 := by
    by_contra! h
    rw [map_sub, map_smul, smul_eq_mul] at hzL
    linarith only [hxL, hzL, mul_nonneg ha.le h]
  have hsame : positiveCoordinates s y = positiveCoordinates s x :=
    Finset.eq_of_subset_of_card_le hsub (hmin y hyW hy hyL)
  have hs' (i : ι) (hi : i ∈ s) (hz : y i = 0) : x i = 0 := by
    apply le_antisymm _ (hx i hi)
    apply le_of_not_gt
    intro hp
    have hpos : i ∈ positiveCoordinates s x := Finset.mem_filter.mpr ⟨hi, hp⟩
    rw [← hsame] at hpos
    exact (ne_of_gt (Finset.mem_filter.mp hpos).2) hz
  have hpx : (positiveCoordinates s x).Nonempty := hpy.mono hsub
  obtain ⟨b, hb, hB, hBc⟩ := exists_coordinate_subtraction s y x hy hx hs' hpx
  have hwL : 0 ≤ L (y - b • x) := by
    by_contra! hn
    have hc := Finset.card_lt_card hBc
    rw [hsame] at hc
    exact (not_le_of_gt hc) (hmin _ (W.sub_mem hyW (W.smul_mem b hxW)) hB hn)
  have hprodL : 0 ≤ (1 - a * b) * L x := by
    have he : (1 - a * b) * L x = L (x - a • y) + a * L (y - b • x) := by
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    rw [he]
    exact add_nonneg hzL (mul_nonneg ha.le hwL)
  have hcoeff : 1 - a * b ≤ 0 := le_of_not_gt fun hp =>
    (mul_neg_of_pos_of_neg hp hxL).not_le hprodL
  obtain ⟨k, hk⟩ := hpx
  obtain ⟨hks, hkx⟩ := Finset.mem_filter.mp hk
  have hcoord (i : ι) : (1 - a * b) * x i = (x i - a * y i) + a * (y i - b * x i) := by ring
  have hcoeff' : 1 - a * b = 0 := by
    apply le_antisymm hcoeff
    have he : 0 ≤ (1 - a * b) * x k := by
      rw [hcoord]
      exact add_nonneg (hA k hks) (mul_nonneg ha.le (hB k hks))
    exact nonneg_of_mul_nonneg_left he hkx
  have he : y - b • x = 0 := by
    apply hzero _ (W.sub_mem hyW (W.smul_mem b hxW))
    intro i hi
    change y i - b * x i = 0
    have hz := hcoord i
    rw [hcoeff', zero_mul] at hz
    by_contra hne
    have hp := lt_of_le_of_ne (hB i hi) (Ne.symm hne)
    exact (add_pos_of_nonneg_of_pos (hA i hi) (mul_pos ha hp)).ne' hz.symm
  exact ⟨b, hb.le, sub_eq_zero.mp he⟩

private def coordinateCross (r : κ → ι → ℝ) (j : ι) (p n : κ) : ι → ℝ :=
  r p j • r n - r n j • r p

/-- In a coordinate cone generated by rays with an antichain of positive
supports, the clipping support test needs only kept rays and crossings
whose common zero coordinates contain no third ray. -/
theorem adjacent_halfspace_support_nonneg (W : Submodule ℝ (ι → ℝ))
    (s : Finset ι) (j : ι) (r : κ → ι → ℝ)
    (hzero : ∀ v ∈ W, (∀ i ∈ s, v i = 0) → v = 0)
    (hrW : ∀ k, r k ∈ W) (hr : ∀ k i, i ∈ s → 0 ≤ r k i)
    (hsep : ∀ k l, k ≠ l → ∃ i ∈ s, 0 < r k i ∧ r l i = 0)
    (hgen : ∀ v ∈ W, (∀ i ∈ s, 0 ≤ v i) →
      ∃ w : κ → ℝ, (∀ k, 0 ≤ w k) ∧ v = ∑ k, w k • r k)
    (L : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hkeep : ∀ k, 0 ≤ r k j → 0 ≤ L (r k))
    (hcross : ∀ p n, 0 < r p j → r n j < 0 →
      (∀ k, k ≠ p → k ≠ n → ∃ i ∈ s, r p i = 0 ∧ r n i = 0 ∧ 0 < r k i) →
      0 ≤ L (r p j • r n - r n j • r p))
    (v : ι → ℝ) (hvW : v ∈ W) (hv : ∀ i ∈ s, 0 ≤ v i) (hvj : 0 ≤ v j) : 0 ≤ L v := by
  classical
  by_contra! hvL
  let s' := insert j s
  let bad (m : ℕ) : Prop := ∃ x ∈ W, (∀ i ∈ s', 0 ≤ x i) ∧ L x < 0 ∧
    (positiveCoordinates s' x).card = m
  have hv' (i : ι) (hi : i ∈ s') : 0 ≤ v i := by
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hvj
    · exact hv i hi
  have hex : ∃ m, bad m := ⟨_, v, hvW, hv', hvL, rfl⟩
  obtain ⟨x, hxW, hx, hxL, hcard⟩ := Nat.find_spec hex
  have hmin (y : ι → ℝ) (hyW : y ∈ W) (hy : ∀ i ∈ s', 0 ≤ y i) (hyL : L y < 0) :
      (positiveCoordinates s' x).card ≤ (positiveCoordinates s' y).card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨y, hyW, hy, hyL, rfl⟩
  have hs (i : ι) (hi : i ∈ s) : i ∈ s' := Finset.mem_insert_of_mem hi
  have hj : j ∈ s' := Finset.mem_insert_self j s
  have hprop (y : ι → ℝ) (hyW : y ∈ W) (hy : ∀ i ∈ s', 0 ≤ y i)
      (hy0 : ∀ i ∈ s', x i = 0 → y i = 0) : ∃ b : ℝ, 0 ≤ b ∧ y = b • x :=
    proportional_of_minimal_negative_support W s' L
      (fun u hu hz => hzero u hu (fun i hi => hz i (hs i hi))) x y hxW hyW hx hy hxL hmin hy0
  obtain ⟨w, hw, hwx⟩ := hgen x hxW (fun i hi => hx i (hs i hi))
  have oldZero (k : κ) (hk : w k ≠ 0) (i : ι) (hi : i ∈ s) (hxi : x i = 0) : r k i = 0 := by
    have hsum : (∑ l, w l * r l i) = x i := by
      rw [hwx]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have he := Finset.single_le_sum (f := fun l => w l * r l i)
      (fun l _ => mul_nonneg (hw l) (hr l i hi)) (Finset.mem_univ k)
    rw [hsum, hxi] at he
    exact (mul_eq_zero.mp (le_antisymm he (mul_nonneg (hw k) (hr k i hi)))).resolve_left hk
  have hnegativeCross : ∃ p n, w p ≠ 0 ∧ w n ≠ 0 ∧ 0 < r p j ∧ r n j < 0 ∧
      L (coordinateCross r j p n) < 0 := by
    by_contra hn
    let r' (k : κ) := if w k = 0 then 0 else r k
    let A : (ι → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
    have hwx' : (∑ k, w k • r' k) = x := by
      rw [hwx]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : w k = 0 <;> simp [r', h]
    have hk' (k : κ) (h : 0 ≤ A (r' k)) : 0 ≤ L (r' k) := by
      by_cases he : w k = 0
      · simp [r', he]
      · simp only [r', if_neg he] at h ⊢
        exact hkeep k h
    have hc' (p n : κ) (hp : 0 < A (r' p)) (hn' : A (r' n) < 0) :
        0 ≤ L (A (r' p) • r' n - A (r' n) • r' p) := by
      have hwp : w p ≠ 0 := fun e => by simp [r', e] at hp
      have hwn : w n ≠ 0 := fun e => by simp [r', e] at hn'
      simp only [r', if_neg hwp, if_neg hwn, A, LinearMap.proj_apply] at hp hn' ⊢
      exact le_of_not_gt (fun hz => hn ⟨p, n, hwp, hwn, hp, hn', hz⟩)
    have hA : 0 ≤ A (∑ k, w k • r' k) := by rw [hwx']; exact hx j hj
    have he := halfspace_clip_support_nonneg r' A L hk' hc' w hw hA
    rw [hwx'] at he
    exact hxL.not_le he
  obtain ⟨p, n, hwp, hwn, hp, hn, hLz⟩ := hnegativeCross
  let z := coordinateCross r j p n
  have hzW : z ∈ W := W.sub_mem (W.smul_mem _ (hrW n)) (W.smul_mem _ (hrW p))
  have hzj : z j = 0 := by
    change r p j * r n j - r n j * r p j = 0
    ring
  have hzn (i : ι) (hi : i ∈ s') : 0 ≤ z i := by
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hzj]
    · change 0 ≤ r p j * r n i - r n j * r p i
      exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hn.le (hr p i hi)).trans
        (mul_nonneg hp.le (hr n i hi)))
  have hzs (i : ι) (hi : i ∈ s') (hxi : x i = 0) : z i = 0 := by
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hzj
    · simp [z, coordinateCross, oldZero p hwp i hi hxi, oldZero n hwn i hi hxi]
  obtain ⟨a, ha, haz⟩ := hprop z hzW hzn hzs
  have ha' : 0 < a := lt_of_le_of_ne ha (fun he => by
    have h : z = 0 := by rw [haz, ← he, zero_smul]
    exact hLz.ne (show L z = 0 by rw [h, map_zero]))
  have hpn : p ≠ n := fun h => (not_le_of_gt hn) (h ▸ hp.le)
  have hadj (k : κ) (hkp : k ≠ p) (hkn : k ≠ n) :
      ∃ i ∈ s, r p i = 0 ∧ r n i = 0 ∧ 0 < r k i := by
    by_contra hno
    have hthird (i : ι) (hi : i ∈ s) (hip : r p i = 0) (hin : r n i = 0) : r k i = 0 :=
      le_antisymm (le_of_not_gt fun hik => hno ⟨i, hi, hip, hin, hik⟩) (hr k i hi)
    have hcancel : ∃ b c : ℝ, 0 ≤ b ∧ 0 ≤ c ∧ r k j + b * r p j + c * r n j = 0 := by
      rcases lt_trichotomy (r k j) 0 with hk | hk | hk
      · refine ⟨-r k j / r p j, 0, div_nonneg (neg_nonneg.mpr hk.le) hp.le, le_rfl, ?_⟩
        rw [div_mul_cancel₀ _ hp.ne', add_neg_cancel, zero_mul, add_zero]
      · exact ⟨0, 0, le_rfl, le_rfl, by simp [hk]⟩
      · refine ⟨0, -r k j / r n j, le_rfl, div_nonneg_of_nonpos
          (neg_nonpos.mpr hk.le) hn.le, ?_⟩
        rw [div_mul_cancel₀ _ hn.ne, zero_mul, add_zero, add_neg_cancel]
    obtain ⟨b, c, hb, hc, huj⟩ := hcancel
    let u := r k + b • r p + c • r n
    have huW : u ∈ W := W.add_mem (W.add_mem (hrW k) (W.smul_mem b (hrW p))) (W.smul_mem c (hrW n))
    have hun (i : ι) (hi : i ∈ s') : 0 ≤ u i := by
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact le_of_eq huj.symm
      · exact add_nonneg (add_nonneg (hr k i hi) (mul_nonneg hb (hr p i hi))) (mul_nonneg hc (hr n i hi))
    have hus (i : ι) (hi : i ∈ s') (hxi : x i = 0) : u i = 0 := by
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact huj
      · have hip := oldZero p hwp i hi hxi
        have hin := oldZero n hwn i hi hxi
        simp [u, hip, hin, hthird i hi hip hin]
    obtain ⟨d, _, hud⟩ := hprop u huW hun hus
    let θ := d / a
    have hθ : u = θ • z := by
      change u = (d / a) • z
      rw [hud, haz, smul_smul, div_mul_cancel₀ _ ha'.ne']
    let A := -θ * r n j - b
    let B := θ * r p j - c
    have hcoeff (i : ι) : r k i = A * r p i + B * r n i := by
      have he := congrFun hθ i
      change r k i + b * r p i + c * r n i = θ * (r p j * r n i - r n j * r p i) at he
      dsimp only [A, B]
      linear_combination he
    have hA : 0 ≤ A := by
      obtain ⟨i, hi, hip, hin⟩ := hsep p n hpn
      have he := hcoeff i
      rw [hin, mul_zero, add_zero] at he
      exact nonneg_of_mul_nonneg_left (he ▸ hr k i hi) hip
    have hB : 0 ≤ B := by
      obtain ⟨i, hi, hin, hip⟩ := hsep n p hpn.symm
      have he := hcoeff i
      rw [hip, mul_zero, zero_add] at he
      exact nonneg_of_mul_nonneg_left (he ▸ hr k i hi) hin
    have hAz : A = 0 := le_antisymm (le_of_not_gt fun hA' => by
      obtain ⟨i, hi, hip, hik⟩ := hsep p k hkp.symm
      have he := hcoeff i
      rw [hik] at he
      exact (add_pos_of_pos_of_nonneg (mul_pos hA' hip) (mul_nonneg hB (hr n i hi))).ne' he.symm) hA
    have hBz : B = 0 := le_antisymm (le_of_not_gt fun hB' => by
      obtain ⟨i, hi, hin, hik⟩ := hsep n k hkn.symm
      have he := hcoeff i
      rw [hik] at he
      exact (add_pos_of_nonneg_of_pos (mul_nonneg hA (hr p i hi)) (mul_pos hB' hin)).ne' he.symm) hB
    obtain ⟨i, _, hik, _⟩ := hsep k p hkp
    exact hik.ne' (by simpa only [hAz, hBz, zero_mul, add_zero] using (hcoeff i))
  exact hLz.not_le (hcross p n hp hn hadj)

/-- For rays positive under a common normalizer, all linear support tests
characterize membership in their nonnegative span. -/
theorem exists_conic_weights_of_linear_tests {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : κ → E) (A : E →ₗ[ℝ] ℝ) (x : E)
    (hA : ∀ k, 0 < A (b k)) (hAx : 0 < A x)
    (h : ∀ L : E →ₗ[ℝ] ℝ, (∀ k, 0 ≤ L (b k)) → 0 ≤ L x) :
    ∃ w : κ → ℝ, (∀ k, 0 ≤ w k) ∧ x = ∑ k, w k • b k := by
  classical
  let b' (k : κ) := (A (b k))⁻¹ • b k
  let x' := (A x)⁻¹ • x
  have hx' : x' ∈ convexHull ℝ (Set.range b') := by
    by_contra hn
    have hclosed : IsClosed (convexHull ℝ (Set.range b')) :=
      (Set.finite_range b').isClosed_convexHull
    obtain ⟨L, c, hc, hx⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hn
    let M : E →ₗ[ℝ] ℝ := c • A - L.toLinearMap
    have hM (k : κ) : 0 ≤ M (b k) := by
      have he := hc _ (subset_convexHull ℝ _ (Set.mem_range_self k))
      simp only [b', map_smul, smul_eq_mul, inv_mul_eq_div] at he
      change 0 ≤ c * A (b k) - L (b k)
      exact sub_nonneg.mpr ((div_lt_iff₀ (hA k)).mp he).le
    have hxM := h M hM
    change 0 ≤ c * A x - L x at hxM
    simp only [x', map_smul, smul_eq_mul, inv_mul_eq_div] at hx
    exact (not_le_of_gt ((lt_div_iff₀ hAx).mp hx)) (sub_nonneg.mp hxM)
  obtain ⟨γ, inst, p, y, hp, _, hy, hyx⟩ := mem_convexHull_iff_exists_fintype.mp hx'
  letI : Fintype γ := inst
  have hy' (i : γ) : ∃ k, b' k = y i := hy i
  choose f hf using hy'
  let v (k : κ) : ℝ := ∑ i : γ, if f i = k then p i else 0
  have hv (k : κ) : 0 ≤ v k := Finset.sum_nonneg fun i _ => by split_ifs <;> simp [hp]
  have he : x' = ∑ k, v k • b' k := by
    rw [← hyx]
    simp only [← hf, v, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hax : A x • x' = x := by simp only [x', smul_smul, mul_inv_cancel₀ hAx.ne', one_smul]
  refine ⟨fun k => A x * (v k * (A (b k))⁻¹), fun k =>
    mul_nonneg hAx.le (mul_nonneg (hv k) (inv_nonneg.mpr (hA k).le)), ?_⟩
  calc
    x = A x • x' := hax.symm
    _ = A x • (∑ k, v k • b' k) := congrArg (fun y : E => A x • y) he
    _ = _ := by simp only [Finset.smul_sum, b', smul_smul]

end

end MOC
