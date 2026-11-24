import MOC.Support
import MOC.SpectralMinorDecomposition

/-! Drury's external-vertices certificate (DOI: 10.13001/1081-3810.1131,
Theorem 1.1 and Corollary 1.2) uses normalized lower bounds that exclude
zero. The radial consequence below is valid in every order conditional
on those certificates; it does not promote them to upper bounds or
ordinary hull inclusion. -/

open BigOperators Matrix

namespace MOC
noncomputable section

private theorem complex_real_projection (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = (((f 1 : ℂ) - (f Complex.I : ℂ) * Complex.I) * z).re := by
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
    simp [Complex.real_smul, Complex.re_add_im]
  calc
    f z = f (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg f hz.symm
    _ = _ := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, smul_eq_mul]
      ring

/-- Only half-spaces with a positive lower threshold are needed to test
whether the line segment from zero to z intersects a finite convex hull. -/
theorem radial_meets_finite_hull_iff (S : Set ℂ) (hS : S.Finite) (z : ℂ) :
    ¬ Disjoint (segment ℝ 0 z) (convexHull ℝ S) ↔
      ∀ η : ℂ, (∀ p ∈ S, 1 ≤ (η * p).re) → 1 ≤ (η * z).re := by
  rw [← convexHull_pair]
  constructor
  · intro h η hv
    obtain ⟨p, hp, hp'⟩ := Set.not_disjoint_iff.mp h
    let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulLeft ℝ η)
    have hp₁ : 1 ≤ f p := by
      apply convexHull_min (s := S) ?_ (convex_halfSpace_ge f.isLinear 1) hp'
      exact hv
    by_contra! hz
    let t : ℝ := max 0 (f z)
    have ht : t < 1 := max_lt (by norm_num) hz
    have hp₂ : f p ≤ t := by
      apply convexHull_min (s := ({0, z} : Set ℂ)) ?_ (convex_halfSpace_le f.isLinear t) hp
      intro q hq
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · change f 0 ≤ max 0 (f z)
        rw [map_zero]
        exact le_max_left _ _
      · rw [Set.mem_singleton_iff.mp hq]
        change f z ≤ max 0 (f z)
        exact le_max_right _ _
    exact (not_lt_of_ge (hp₁.trans hp₂)) ht
  · intro h hd
    obtain ⟨f, u, v, hA, huv, hB⟩ := geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ _) (Set.toFinite _).isCompact_convexHull
      (convex_convexHull ℝ _) hS.isClosed_convexHull hd
    have hu : 0 < u := by
      simpa using hA 0 (subset_convexHull ℝ _ (by simp))
    have hv : 0 < v := hu.trans huv
    let k : ℂ := ↑(f 1) - ↑(f Complex.I) * Complex.I
    let η : ℂ := ↑(v⁻¹) * k
    have he (p : ℂ) : (η * p).re = f p / v := by
      show ((↑v⁻¹ * k) * p).re = _
      rw [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, ← complex_real_projection f p, div_eq_mul_inv, mul_comm]
    have hz := h η (by
      intro p hp
      rw [he, le_div_iff₀ hv, one_mul]
      exact (hB p (subset_convexHull ℝ _ hp)).le)
    rw [he, le_div_iff₀ hv, one_mul] at hz
    exact (not_lt_of_ge hz) ((hA z (subset_convexHull ℝ _ (by simp))).trans huv)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectrum-specific nonnegative subset certificates for the normalized external
directions imply a radial conclusion in arbitrary order. -/
theorem radial_hull_of_external_subset_certificates (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U)
    (hcert : ∀ η : ℂ, (∀ σ, 1 ≤ (η * matchingProduct a b σ).re) →
      ∃ c : Finset ι × Finset ι → ℝ, (∀ e, 0 ≤ c e) ∧
        (∀ σ, (η * matchingProduct a b σ).re - 1 =
          ∑ e, c e * subsetImageEvent e.1 e.2 σ)) :
    ¬ Disjoint (segment ℝ 0 (determinantValue a b U))
      (convexHull ℝ (Set.range (matchingProduct a b))) := by
  apply (radial_meets_finite_hull_iff _ (Set.finite_range _) _).mpr
  intro η hη
  obtain ⟨c, hc, he⟩ := hcert η (fun σ => hη _ (Set.mem_range_self σ))
  have h := spectral_support_of_subsetImage_certificate a b U hU (-η) (-1)
    Prod.fst Prod.snd c hc (fun _ => 0) (by simp) (by
      intro σ
      rw [zero_add, ← he, neg_mul, Complex.neg_re]
      ring)
  rw [neg_mul, Complex.neg_re] at h
  linarith

end
end MOC
