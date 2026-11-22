import MOC.Support
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Lattice

/-! A finite envelope of real parts of affine functions admits exact contact
steps along directions fixing its current maximizing functions. -/

namespace MOC

noncomputable section

open Filter
open scoped Topology

variable {J : Type*} [Fintype J]

private theorem affine_along_ray (s x v : ℂ) (b t : ℝ) :
    (s * (x + (t : ℂ) * v)).re + b = ((s * x).re + b) + t * (s * v).re := by
  rw [mul_add, mul_left_comm s, Complex.add_re, Complex.re_ofReal_mul]
  ring

/-- Move along a direction on which every active affine function is constant.
If one inactive slope is positive, the first overtaking time adds a contact
at the same height and preserves all old contacts. -/
theorem exists_affine_contact_of_flat_direction
    (s : J → ℂ) (b : J → ℝ) (x v : ℂ) (H : ℝ)
    (hupper : ∀ j, (s j * x).re + b j ≤ H)
    (hflat : ∀ j, (s j * x).re + b j = H → (s j * v).re = 0)
    (hgrowing : ∃ j, 0 < (s j * v).re) :
    ∃ t : ℝ, 0 < t ∧
      (∀ j, (s j * (x + (t : ℂ) * v)).re + b j ≤ H) ∧
      (∀ j, (s j * x).re + b j = H → (s j * (x + (t : ℂ) * v)).re + b j = H) ∧
      ∃ j, (s j * x).re + b j < H ∧ (s j * (x + (t : ℂ) * v)).re + b j = H := by
  classical
  let D := Finset.univ.filter (fun j => 0 < (s j * v).re)
  let time (j : J) : ℝ := (H - ((s j * x).re + b j)) / (s j * v).re
  obtain ⟨j, hj⟩ := hgrowing
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image D time
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hrpos : 0 < (s r * v).re := (Finset.mem_filter.mp hr).2
  have hrlt : (s r * x).re + b r < H :=
    lt_of_le_of_ne (hupper r) (fun he => (ne_of_gt hrpos) (hflat r he))
  have ht : 0 < time r := div_pos (sub_pos.mpr hrlt) hrpos
  refine ⟨time r, ht, ?_, ?_, r, hrlt, ?_⟩
  · intro i
    rw [affine_along_ray]
    by_cases hi : 0 < (s i * v).re
    · have h := (le_div_iff₀ hi).mp
        (hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
      dsimp only [time] at h
      linarith only [h]
    · have h := mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hi)
      linarith only [h, hupper i]
  · intro i h
    rw [affine_along_ray, h, hflat i h, mul_zero, add_zero]
  · rw [affine_along_ray]
    have h := div_mul_cancel₀ (H - ((s r * x).re + b r)) (ne_of_gt hrpos)
    change time r * (s r * v).re = _ at h
    linarith only [h]

/-- A uniform positive support margin for the slopes makes the affine envelope
coercive. In particular it has a minimum even on the entire complex plane. -/
theorem exists_affine_envelope_minimizer [Nonempty J]
    (s : J → ℂ) (b : J → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ x : ℂ, ∃ j, δ * ‖x‖ ≤ (s j * x).re) :
    ∃ (x : ℂ) (H : ℝ), (∀ j, (s j * x).re + b j ≤ H) ∧
      ∀ y : ℂ, ∃ j, H ≤ (s j * y).re + b j := by
  classical
  let F (x : ℂ) : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty (fun j => (s j * x).re + b j)
  have hle (x : ℂ) (j : J) : (s j * x).re + b j ≤ F x :=
    Finset.le_sup' (fun i => (s i * x).re + b i) (Finset.mem_univ j)
  obtain ⟨j₀, _, hb⟩ :=
    Finset.exists_min_image Finset.univ b (Finset.univ_nonempty : (Finset.univ : Finset J).Nonempty)
  have hlower (x : ℂ) : δ * ‖x‖ + b j₀ ≤ F x := by
    obtain ⟨j, hj⟩ := hmargin x
    exact (add_le_add hj (hb j (Finset.mem_univ j))).trans (hle x j)
  have h₀ : b j₀ ≤ F 0 := by simpa only [norm_zero, mul_zero, zero_add] using hlower 0
  let R := (F 0 - b j₀) / δ
  have hR : 0 ≤ R := div_nonneg (sub_nonneg.mpr h₀) hδ.le
  have houtside (x : ℂ) (hx : x ∉ Metric.closedBall (0 : ℂ) R) : F 0 ≤ F x := by
    have hnorm : R < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have h : F 0 - b j₀ ≤ ‖x‖ * δ := (div_le_iff₀ hδ).mp hnorm.le
    linarith only [h, hlower x, mul_comm δ ‖x‖]
  have hF : Continuous F := by
    apply Continuous.finset_sup'_apply
    intro j _
    fun_prop
  have hin : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := Metric.mem_closedBall_self hR
  obtain ⟨x, _, hx⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMinOn ⟨0, hin⟩ hF.continuousOn
  refine ⟨x, F x, hle x, fun y => ?_⟩
  have hy : F x ≤ F y := by
    by_cases h : y ∈ Metric.closedBall (0 : ℂ) R
    · exact hx h
    · exact (hx hin).trans (houtside y h)
  obtain ⟨j, _, hj⟩ := (Finset.le_sup'_iff Finset.univ_nonempty).mp hy
  exact ⟨j, hj⟩

private theorem exists_nondecreasing_active_slope
    (s : J → ℂ) (b : J → ℝ) (x v : ℂ) (H : ℝ)
    (hupper : ∀ j, (s j * x).re + b j ≤ H)
    (hmin : ∀ y : ℂ, ∃ j, H ≤ (s j * y).re + b j) :
    ∃ j, (s j * x).re + b j = H ∧ 0 ≤ (s j * v).re := by
  by_contra! h
  have hnear (j : J) : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (s j * (x + (t : ℂ) * v)).re + b j < H := by
    by_cases hj : (s j * x).re + b j = H
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      rw [affine_along_ray, hj]
      exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg ht (h j hj))
    · have hcont : ContinuousAt (fun t : ℝ => (s j * (x + (t : ℂ) * v)).re + b j) 0 := by
        fun_prop
      have hstart : (s j * (x + ((0 : ℝ) : ℂ) * v)).re + b j ∈ Set.Iio H := by
        simpa using lt_of_le_of_ne (hupper j) hj
      exact (hcont.eventually_mem (Iio_mem_nhds hstart)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht⟩ := (Filter.eventually_all.mpr hnear).exists
  obtain ⟨j, hj⟩ := hmin (x + (t : ℂ) * v)
  exact (not_lt_of_ge hj) (ht j)

private theorem re_mul_perpendicular (z : ℂ) : (z * (Complex.I * star z)).re = 0 := by
  rw [mul_left_comm z, Complex.star_def, Complex.mul_conj]
  simp [Complex.mul_re]

/-- At a minimum of a coercive affine envelope, one or two active labels can
be extended by a new active label. The minimal height is preserved. -/
theorem exists_more_affine_contacts_at_minimum
    (s : J → ℂ) (b : J → ℝ) (x : ℂ) (H δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ v : ℂ, ∃ j, δ * ‖v‖ ≤ (s j * v).re)
    (hupper : ∀ j, (s j * x).re + b j ≤ H)
    (hmin : ∀ y : ℂ, ∃ j, H ≤ (s j * y).re + b j)
    (r q : J) (hactive : ∀ j, (s j * x).re + b j = H → j = r ∨ j = q) :
    ∃ y : ℂ, (∀ j, (s j * y).re + b j ≤ H) ∧
      (∀ j, (s j * x).re + b j = H → (s j * y).re + b j = H) ∧
      ∃ j, (s j * x).re + b j < H ∧ (s j * y).re + b j = H := by
  let d := s r - s q
  obtain ⟨v, hv, heq⟩ : ∃ v : ℂ, v ≠ 0 ∧ (s r * v).re = (s q * v).re := by
    by_cases hd : d = 0
    · exact ⟨1, one_ne_zero, by rw [sub_eq_zero.mp hd]⟩
    · refine ⟨Complex.I * star d, mul_ne_zero Complex.I_ne_zero (star_ne_zero.mpr hd), ?_⟩
      have he := re_mul_perpendicular d
      change ((s r - s q) * (Complex.I * star d)).re = 0 at he
      exact sub_eq_zero.mp (by simpa only [sub_mul, Complex.sub_re] using he)
  have hsame (i : J) (hi : (s i * x).re + b i = H) :
      (s i * v).re = (s r * v).re := by
    rcases hactive i hi with h | h
    · rw [h]
    · rw [h, heq]
  obtain ⟨i, hi, hpos⟩ := exists_nondecreasing_active_slope s b x v H hupper hmin
  obtain ⟨k, hk, hneg⟩ := exists_nondecreasing_active_slope s b x (-v) H hupper hmin
  rw [hsame i hi] at hpos
  rw [mul_neg, Complex.neg_re, hsame k hk] at hneg
  have hz : (s r * v).re = 0 := by linarith only [hpos, hneg]
  obtain ⟨j, hj⟩ := hmargin v
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨t, _, ht, hpreserve, hnew⟩ :=
    exists_affine_contact_of_flat_direction s b x v H hupper
      (fun i hi => (hsame i hi).trans hz) ⟨j, (mul_pos hδ hnorm).trans_le hj⟩
  exact ⟨x + (t : ℂ) * v, ht, hpreserve, hnew⟩

end

end MOC
