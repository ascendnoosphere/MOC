import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Support reduction for finite conic combinations. -/

open BigOperators

namespace MOC

/-- A finite nonnegative combination in a real vector space has an equivalent
combination with at most `finrank ℝ V` nonzero weights, drawn from its original support. -/
theorem exists_conic_support_le_finrank {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (v : ι → V) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i • v i) = ∑ i, p i • v i ∧
      (Finset.univ.filter fun i => q i ≠ 0).card ≤ Module.finrank ℝ V ∧
      ∀ i, p i = 0 → q i = 0 := by
  classical
  let support (w : ι → ℝ) := Finset.univ.filter fun i => w i ≠ 0
  let P (n : ℕ) := ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i • v i) = ∑ i, p i • v i ∧
    (∀ i, p i = 0 → q i = 0) ∧ (support q).card = n
  have hex : ∃ n, P n := ⟨(support p).card, p, hp, rfl, fun _ h => h, rfl⟩
  obtain ⟨q, hq, hsum, hz, hcard⟩ := Nat.find_spec hex
  refine ⟨q, hq, hsum, ?_, hz⟩
  let S := support q
  change S.card ≤ Module.finrank ℝ V
  by_contra hlarge
  have hdep : ¬ LinearIndependent ℝ (fun i : S => v i) := by
    intro h
    exact hlarge (by simpa only [Fintype.card_coe] using h.fintype_card_le_finrank)
  obtain ⟨g, hg, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let d (i : ι) := if h : i ∈ S then (g k)⁻¹ * g ⟨i, h⟩ else 0
  have hdz (i : ι) (hi : i ∉ S) : d i = 0 := dif_neg hi
  have hdk : d k = 1 := by
    rw [show d (k : ι) = (g k)⁻¹ * g k from dif_pos k.property, inv_mul_cancel₀ hk]
  have hdS : (∑ i, d i • v i) = 0 := calc
    _ = ∑ i ∈ S, d i • v i :=
      (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by rw [hdz i hi, zero_smul])).symm
    _ = ∑ i : S, d i • v i := (Finset.sum_coe_sort S (fun i => d i • v i)).symm
    _ = ∑ i : S, ((g k)⁻¹ * g i) • v i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show d (i : ι) = (g k)⁻¹ * g i from dif_pos i.property]
    _ = (g k)⁻¹ • ∑ i : S, g i • v i := by simp only [mul_smul, Finset.smul_sum]
    _ = 0 := by rw [hg, smul_zero]
  let D := Finset.univ.filter fun i => 0 < d i
  have hD : D.Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdk.symm ▸ zero_lt_one⟩⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image D (fun i => q i / d i) hD
  have hjd : 0 < d j := (Finset.mem_filter.mp hj).2
  have hjS : j ∈ S := by
    by_contra h
    exact hjd.ne' (hdz j h)
  let t := q j / d j
  have ht : 0 ≤ t := div_nonneg (hq j) hjd.le
  let r (i : ι) := q i - t * d i
  have hr (i : ι) : 0 ≤ r i := by
    by_cases hi : 0 < d i
    · have hti : t ≤ q i / d i := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ hi).mp hti)
    · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hi)).trans (hq i))
  have hrj : r j = 0 := by
    dsimp only [r, t]
    rw [div_mul_cancel₀ _ hjd.ne', sub_self]
  have hrzero (i : ι) (hi : q i = 0) : r i = 0 := by
    have hni : i ∉ S := by simp [S, support, hi]
    simp only [r, hi, hdz i hni, mul_zero, sub_zero]
  have hsub : support r ⊆ S.erase j := by
    intro i hi
    have hri : r i ≠ 0 := (Finset.mem_filter.mp hi).2
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · rintro rfl
      exact hri hrj
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun he => hri (hrzero i he)⟩
  have hrlt : (support r).card < S.card :=
    (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hjS)
  have hrsum : (∑ i, r i • v i) = ∑ i, q i • v i := by
    simp only [r, sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdS,
      smul_zero, sub_zero]
  have hmincard : Nat.find hex ≤ (support r).card :=
    Nat.find_min' hex ⟨r, hr, hrsum.trans hsum, fun i hi => hrzero i (hz i hi), rfl⟩
  have hlt : (support r).card < Nat.find hex := hrlt.trans_eq hcard
  exact (not_lt_of_ge hmincard) hlt

end MOC
