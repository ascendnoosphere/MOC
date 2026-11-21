import MOC.Support
import MOC.Wielandt

/-! The matching products certify a quantitative margin for zero in a support disk. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If zero is attained, at least one matching product has squared modulus at
most the difference between the squared radius of the support disk and the
squared distance of its center from zero. -/
theorem exists_matching_normSq_le_disk_margin_of_singular (a b : ι → ℂ)
    {W : Matrix ι ι ℂ} (hW : IsUnitary W) (hzero : determinantValue a b W = 0)
    (z ξ : ℂ)
    (hdisk : ∀ σ : Equiv.Perm ι, (ξ * (matchingProduct a b σ - z)).re ≤
      -Complex.normSq (matchingProduct a b σ - z) / 2) :
    ∃ σ : Equiv.Perm ι,
      Complex.normSq (matchingProduct a b σ) ≤ 2 * (ξ * z).re - Complex.normSq z := by
  obtain ⟨σ, hσ⟩ := (holds_iff_directional a b W).mp
    (holds_of_singular a b hW hzero) (ξ - conj z)
  rw [hzero, mul_zero, Complex.zero_re, sub_mul, Complex.sub_re, mul_comm (conj z)] at hσ
  have h := hdisk σ
  rw [mul_sub, Complex.sub_re, Complex.normSq_sub] at h
  exact ⟨σ, by linarith only [h, hσ]⟩

/-- A support disk with margin below every squared matching modulus requires
strict circle-or-line separation of the signed spectra. -/
theorem strictlySeparatedByCircleOrLine_of_matching_disk_margin (a b : ι → ℂ) (z ξ : ℂ)
    (hdisk : ∀ σ : Equiv.Perm ι, (ξ * (matchingProduct a b σ - z)).re ≤
      -Complex.normSq (matchingProduct a b σ - z) / 2)
    (hmargin : ∀ σ : Equiv.Perm ι,
      2 * (ξ * z).re - Complex.normSq z < Complex.normSq (matchingProduct a b σ)) :
    StrictlySeparatedByCircleOrLine a (fun i => -b i) := by
  apply (not_exists_singular_iff_circle_or_line a b).mp
  rintro ⟨W, hW, hzero⟩
  obtain ⟨σ, hσ⟩ := exists_matching_normSq_le_disk_margin_of_singular a b hW hzero z ξ hdisk
  exact (not_lt_of_ge hσ) (hmargin σ)

/-- When no pair sums to zero, it suffices that zero lie on or outside a
support disk containing the matching products. -/
theorem strictlySeparatedByCircleOrLine_of_disk_boundary (a b : ι → ℂ) (z ξ : ℂ)
    (hregular : ∀ i j, a i + b j ≠ 0)
    (hdisk : ∀ σ : Equiv.Perm ι, (ξ * (matchingProduct a b σ - z)).re ≤
      -Complex.normSq (matchingProduct a b σ - z) / 2)
    (hprojected : (ξ * z).re ≤ Complex.normSq z / 2) :
    StrictlySeparatedByCircleOrLine a (fun i => -b i) := by
  refine strictlySeparatedByCircleOrLine_of_matching_disk_margin a b z ξ hdisk ?_
  intro σ
  have hnonzero : matchingProduct a b σ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hregular (σ j) j
  exact lt_of_le_of_lt (by linarith only [hprojected]) (Complex.normSq_pos.mpr hnonzero)

/-- Two transverse vertices with weights at least `ε` in a convex
representation of zero give a uniform lower bound for the support function.
The displayed form avoids division when the vertices vanish. -/
theorem exists_projection_ge_of_weighted_zero {κ : Type*} [Fintype κ]
    (p : κ → ℂ) (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hmass : ∑ k, w k = 1)
    (hzero : ∑ k, (w k : ℂ) * p k = 0)
    (i j : κ) (ε : ℝ) (hε : 0 ≤ ε) (hi : ε ≤ w i) (hj : ε ≤ w j)
    (η : ℂ) (hη : ‖η‖ = 1) :
    ∃ k : κ, ε * |(p i * conj (p j)).im| ≤ (‖p i‖ + ‖p j‖) * (η * p k).re := by
  classical
  let q (k : κ) := (η * p k).re
  obtain ⟨k, _, hmax⟩ := Finset.exists_max_image Finset.univ q ⟨i, Finset.mem_univ i⟩
  let H := q k
  have hle (l : κ) : q l ≤ H := hmax l (Finset.mem_univ l)
  have hmean : ∑ l, w l * q l = 0 := by
    have he := congrArg (fun z : ℂ => (η * z).re) hzero
    change (η * ∑ l, (w l : ℂ) * p l).re = (η * 0).re at he
    rw [Finset.mul_sum, Complex.re_sum, mul_zero, Complex.zero_re] at he
    calc
      _ = ∑ l, (η * ((w l : ℂ) * p l)).re := by
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_left_comm, Complex.re_ofReal_mul]
      _ = 0 := he
  have htotal : ∑ l, w l * (H - q l) = H := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul, hmean, sub_zero]
  have hnonneg (l : κ) : 0 ≤ w l * (H - q l) :=
    mul_nonneg (hw l) (sub_nonneg.mpr (hle l))
  have hH : 0 ≤ H := htotal ▸ Finset.sum_nonneg (fun l _ => hnonneg l)
  have habs (l : κ) (hεl : ε ≤ w l) : ε * |q l| ≤ H := by
    by_cases hs : 0 ≤ q l
    · have hwle : w l ≤ 1 := by
        rw [← hmass]
        exact Finset.single_le_sum (fun m _ => hw m) (Finset.mem_univ l)
      rw [abs_of_nonneg hs]
      exact (mul_le_mul_of_nonneg_right (hεl.trans hwle) hs).trans (by simpa using hle l)
    · have hs' : q l < 0 := lt_of_not_ge hs
      rw [abs_of_neg hs']
      calc
        _ ≤ w l * (-q l) := mul_le_mul_of_nonneg_right hεl (neg_nonneg.mpr hs'.le)
        _ ≤ w l * (H - q l) := mul_le_mul_of_nonneg_left (by linarith only [hH]) (hw l)
        _ ≤ ∑ m, w m * (H - q m) :=
          Finset.single_le_sum (fun m _ => hnonneg m) (Finset.mem_univ l)
        _ = H := htotal
  let u := η * p i
  let v := η * p j
  have hηc : η * conj η = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hη, one_pow, Complex.ofReal_one]
  have hrotate : u * conj v = p i * conj (p j) := by
    dsimp only [u, v]
    rw [map_mul, show η * p i * (conj η * conj (p j)) =
      (η * conj η) * (p i * conj (p j)) by ring, hηc, one_mul]
  have him : (p i * conj (p j)).im = u.im * v.re - u.re * v.im := by
    rw [← hrotate, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hu : |u.im| ≤ ‖p i‖ := by
    simpa only [u, Complex.norm_mul, hη, one_mul] using Complex.abs_im_le_norm u
  have hv : |v.im| ≤ ‖p j‖ := by
    simpa only [v, Complex.norm_mul, hη, one_mul] using Complex.abs_im_le_norm v
  refine ⟨k, ?_⟩
  change ε * |(p i * conj (p j)).im| ≤ (‖p i‖ + ‖p j‖) * H
  calc
    _ ≤ ε * (‖p i‖ * |v.re| + ‖p j‖ * |u.re|) := by
      apply mul_le_mul_of_nonneg_left _ hε
      rw [him]
      refine (abs_sub _ _).trans ?_
      simpa only [abs_mul, mul_comm |u.re| |v.im|] using
        add_le_add (mul_le_mul_of_nonneg_right hu (abs_nonneg v.re))
          (mul_le_mul_of_nonneg_right hv (abs_nonneg u.re))
    _ = ‖p i‖ * (ε * |q j|) + ‖p j‖ * (ε * |q i|) := by
      change ε * (‖p i‖ * |q j| + ‖p j‖ * |q i|) = _
      ring
    _ ≤ ‖p i‖ * H + ‖p j‖ * H :=
      add_le_add (mul_le_mul_of_nonneg_left (habs j hj) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (habs i hi) (norm_nonneg _))
    _ = _ := by ring

/-- A positive law at zero certifies the inclusion for determinants whose
modulus is within the margin from two of its supported matching products. -/
theorem holds_of_norm_le_weighted_zero_margin (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (w : Equiv.Perm ι → ℝ) (hw : ∀ k, 0 ≤ w k) (hmass : ∑ k, w k = 1)
    (hzero : ∑ k, (w k : ℂ) * matchingProduct a b k = 0)
    (i j : Equiv.Perm ι) (ε : ℝ) (hε : 0 ≤ ε) (hi : ε ≤ w i) (hj : ε ≤ w j)
    (hden : 0 < ‖matchingProduct a b i‖ + ‖matchingProduct a b j‖)
    (hdet : (‖matchingProduct a b i‖ + ‖matchingProduct a b j‖) * ‖determinantValue a b U‖ ≤
      ε * |(matchingProduct a b i * conj (matchingProduct a b j)).im|) :
    Holds a b U := by
  apply (holds_iff_directional a b U).mpr
  intro ξ
  by_cases hξ : ξ = 0
  · exact ⟨i, by simp [hξ]⟩
  have hξpos := norm_pos_iff.mpr hξ
  let η := ξ / (‖ξ‖ : ℂ)
  have hη : ‖η‖ = 1 := by
    rw [show η = ξ / (‖ξ‖ : ℂ) from rfl, Complex.norm_div, Complex.norm_real,
      Real.norm_of_nonneg hξpos.le, div_self hξpos.ne']
  obtain ⟨k, hk⟩ := exists_projection_ge_of_weighted_zero (matchingProduct a b) w hw hmass
    hzero i j ε hε hi hj η hη
  have hk' := (mul_le_mul_left hden).mp (hdet.trans hk)
  have hval : (η * determinantValue a b U).re ≤ ‖determinantValue a b U‖ := by
    simpa only [Complex.norm_mul, hη, one_mul] using Complex.re_le_norm (η * determinantValue a b U)
  have h := hval.trans hk'
  have hηre (x : ℂ) : (η * x).re = (ξ * x).re / ‖ξ‖ := by
    dsimp only [η]
    rw [div_mul_eq_mul_div, Complex.div_ofReal_re]
  rw [hηre, hηre] at h
  exact ⟨k, (div_le_div_iff_of_pos_right hξpos).mp h⟩

/-- A centered ball in the matching hull of one block lifts to the full
matching hull with radius scaled by any nonzero complementary matching. -/
theorem matchingHull_ball_directSum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a b : ι → ℂ) (c d : κ → ℂ) (τ : Equiv.Perm κ) (hτ : matchingProduct c d τ ≠ 0)
    (r : ℝ) (hball : Metric.closedBall 0 r ⊆ convexHull ℝ (Set.range (matchingProduct a b))) :
    Metric.closedBall 0 (‖matchingProduct c d τ‖ * r) ⊆
      convexHull ℝ (Set.range (matchingProduct (Sum.elim a c) (Sum.elim b d))) := by
  intro z hz
  have hz' : ‖z‖ ≤ ‖matchingProduct c d τ‖ * r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
  have hw : z / matchingProduct c d τ ∈ convexHull ℝ (Set.range (matchingProduct a b)) := by
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_div,
      div_le_iff₀ (norm_pos_iff.mpr hτ), mul_comm r]
    exact hz'
  have hprod : ∀ x ∈ Set.range (matchingProduct a b), ∀ y ∈ Set.range (matchingProduct c d),
      x * y ∈ convexHull ℝ (Set.range (matchingProduct (Sum.elim a c) (Sum.elim b d))) := by
    rintro _ ⟨σ, rfl⟩ _ ⟨π, rfl⟩
    rw [← matchingProduct_sum]
    exact matchingProduct_mem_hull _ _ _
  have h := mul_mem_of_mem_convexHulls (convex_convexHull ℝ _) hprod hw
    (matchingProduct_mem_hull c d τ)
  simpa only [div_mul_cancel₀ z hτ] using h

/-- The oriented volume of the four lifts is the signed area from the two
matching products obtained by exchanging the second pair of labels. -/
theorem cross_lift_det_eq_matching_area (x y c d : ℂ) :
    (!![(y - x).re, (y - x).im, Complex.normSq y - Complex.normSq x;
        (c - x).re, (c - x).im, Complex.normSq c - Complex.normSq x;
        (d - x).re, (d - x).im, Complex.normSq d - Complex.normSq x] :
        Matrix (Fin 3) (Fin 3) ℝ).det =
      -(((x - c) * (y - d)) * conj ((y - c) * (x - d))).im := by
  simp [Matrix.det_fin_three, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

end MOC
