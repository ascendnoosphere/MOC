import MOC.Support

/-! Finite convex certificates and exact separators for affine pencils. -/

open BigOperators
open scoped ComplexConjugate Topology

namespace MOC

/-- A feasible coefficient law gives a convex certificate at every complex parameter. -/
theorem affine_pencil_certificate_of_coefficient_weights {P : Type*} [Fintype P]
    (s q : P → ℂ) (x y : ℂ) (w : P → ℝ)
    (hn : ∀ p, 0 ≤ w p) (hs : ∑ p, w p = 1)
    (hx : ∑ p, (w p : ℂ) * s p = x) (hy : ∑ p, (w p : ℂ) * q p = y) (t : ℂ) :
    x * t + y ∈ convexHull ℝ (Set.range (fun p => s p * t + q p)) := by
  refine mem_convexHull_of_exists_fintype w _ hn hs (fun p => ⟨p, rfl⟩) ?_
  simp only [Complex.real_smul, mul_add, Finset.sum_add_distrib, ← mul_assoc,
    ← Finset.sum_mul, hx, hy]

/-- If the intercept coefficient is nonzero, an exact coefficient separator
gives an exact separator at the quotient of its two coefficients. -/
theorem affine_pencil_evaluation_of_separator {P : Type*}
    (s q : P → ℂ) (x y u v : ℂ) (hv : v ≠ 0)
    (h : ∀ p, 0 < (u * (x - s p) + v * (y - q p)).re) :
    ∀ p, 0 < (v * ((x * (u / v) + y) - (s p * (u / v) + q p))).re := by
  have huv : v * (u / v) = u := mul_div_cancel₀ _ hv
  intro p
  have heq : v * ((x * (u / v) + y) - (s p * (u / v) + q p)) =
      u * (x - s p) + v * (y - q p) := by
    calc
      _ = (v * (u / v)) * (x - s p) + v * (y - q p) := by ring
      _ = _ := by rw [huv]
  rw [heq]
  exact h p

/-- A pure slope certificate with margin `δ` remains strict after the explicit
positive perturbation of the intercept coefficient used in the exact search. -/
theorem affine_pencil_evaluation_of_pure_slope_separator {P : Type*}
    (s q : P → ℂ) (x y u : ℂ) (δ B : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hs : ∀ p, δ ≤ (u * (x - s p)).re) (hq : ∀ p, |(y - q p).re| ≤ B) :
    let v : ℂ := (δ / (2 * (1 + B)) : ℝ)
    ∀ p, 0 < (v * ((x * (u / v) + y) - (s p * (u / v) + q p))).re := by
  let v : ℝ := δ / (2 * (1 + B))
  have hden : 0 < 2 * (1 + B) := by linarith
  have hv : 0 < v := div_pos hδ hden
  have hvbound : v * B < δ := by
    change δ / (2 * (1 + B)) * B < δ
    rw [div_mul_eq_mul_div₀, div_lt_iff₀ hden]
    nlinarith only [mul_nonneg hδ.le hB, hδ]
  change ∀ p, 0 < ((v : ℂ) * ((x * (u / (v : ℂ)) + y) -
    (s p * (u / (v : ℂ)) + q p))).re
  apply affine_pencil_evaluation_of_separator s q x y u (v : ℂ)
    (Complex.ofReal_ne_zero.mpr hv.ne')
  intro p
  have hqLower : -B ≤ (y - q p).re := (abs_le.mp (hq p)).1
  simp only [Complex.add_re, Complex.mul_re ((v : ℝ) : ℂ), Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  linarith only [hs p, hvbound, mul_le_mul_of_nonneg_left hqLower hv.le]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The disks centered at every complex number, with radii equal to the
farthest matching distance, have intersection equal to the matching hull. -/
theorem holds_iff_farthest_matching_distance (a b : ι → ℂ) (U : Matrix ι ι ℂ) :
    Holds a b U ↔ ∀ w : ℂ, ∃ p : Equiv.Perm ι,
      Complex.normSq (determinantValue a b U - w) ≤
        Complex.normSq (matchingProduct a b p - w) := by
  classical
  constructor
  · intro h w
    obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
      (fun p : Equiv.Perm ι => ‖matchingProduct a b p - w‖) Finset.univ_nonempty
    have hball : determinantValue a b U ∈ Metric.closedBall w ‖matchingProduct a b p - w‖ := by
      apply convexHull_min ?_ (convex_closedBall _ _) h
      rintro _ ⟨q, rfl⟩
      exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using hp q (Finset.mem_univ q))
    refine ⟨p, ?_⟩
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hball
  · intro h
    rw [holds_iff_directional]
    intro η
    by_contra! hsep
    let d := determinantValue a b U
    let v := matchingProduct a b
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ p,
        0 < 2 * ((η * d).re - (η * v p).re) +
          t * (Complex.normSq d - Complex.normSq (v p)) := by
      apply Filter.eventually_all.mpr
      intro p
      have hc : Continuous (fun t : ℝ => 2 * ((η * d).re - (η * v p).re) +
          t * (Complex.normSq d - Complex.normSq (v p))) := by fun_prop
      apply continuousAt_const.eventually_lt hc.continuousAt
      simpa only [zero_mul, add_zero] using
        mul_pos (show (0 : ℝ) < 2 by norm_num) (sub_pos.mpr (hsep p))
    have hright := hnear.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    obtain ⟨t, htgap, ht⟩ := (hright.and self_mem_nhdsWithin).exists
    have htpos : 0 < t := ht
    let w : ℂ := -((t⁻¹ : ℝ) : ℂ) * conj η
    have hre (z : ℂ) : (z * conj w).re = -(t⁻¹ * (η * z).re) := by
      have hconj : conj w = -((t⁻¹ : ℝ) : ℂ) * η := by
        simp only [w, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]
      rw [hconj, show z * (-((t⁻¹ : ℝ) : ℂ) * η) = -((t⁻¹ : ℝ) : ℂ) * (η * z) by ring,
        neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    obtain ⟨p, hp⟩ := h w
    change Complex.normSq (d - w) ≤ Complex.normSq (v p - w) at hp
    rw [Complex.normSq_sub, Complex.normSq_sub, hre, hre] at hp
    have hscaled := mul_le_mul_of_nonneg_left hp htpos.le
    have hone : t * t⁻¹ = 1 := mul_inv_cancel₀ htpos.ne'
    have heq (x y z : ℝ) : t * (x + y - 2 * -(t⁻¹ * z)) = t * x + t * y + 2 * z := by
      calc
        _ = t * x + t * y + 2 * (t * t⁻¹) * z := by ring
        _ = _ := by rw [hone, mul_one]
    rw [heq, heq] at hscaled
    nlinarith only [hscaled, htgap p]

end MOC
