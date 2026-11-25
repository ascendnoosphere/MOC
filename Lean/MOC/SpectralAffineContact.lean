import MOC.AffineContact
import MOC.SpectralKKT

/-! Moving one spectral coordinate gives a finite affine support envelope.
An interior slope hull forces a minimizer with at least three contacts. -/

open BigOperators Matrix
open scoped ComplexConjugate

namespace MOC

noncomputable section

/-- An interior complex convex hull contains a uniform directional margin. -/
theorem affine_margin_of_zero_mem_interior {J : Type*} [Fintype J] [Nonempty J]
    (s : J → ℂ) (hs : (0 : ℂ) ∈ interior (convexHull ℝ (Set.range s))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℂ, ∃ j, δ * ‖v‖ ≤ (s j * v).re := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hs)
  let δ := r / 2
  have hp : 0 < δ := half_pos hr
  refine ⟨δ, hp, fun v => ?_⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => (s i * v).re)
    (Finset.univ_nonempty : (Finset.univ : Finset J).Nonempty)
  refine ⟨j, ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvn : ‖v‖ ≠ 0 := (norm_pos_iff.mpr hv).ne'
  let w := ((δ / ‖v‖ : ℝ) : ℂ) * conj v
  have hnorm : ‖w‖ = δ := by
    dsimp only [w]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hp.le (norm_nonneg v)), Complex.norm_conj,
      div_mul_cancel₀ _ hvn]
  have hw : w ∈ convexHull ℝ (Set.range s) := hball (by
    rw [Metric.mem_ball, dist_zero_right, hnorm]
    exact half_lt_self hr)
  let f : ℂ →ₗ[ℝ] ℝ := Complex.reLm.comp (LinearMap.mulRight ℝ v)
  have hle : w ∈ {z : ℂ | f z ≤ (s j * v).re} := by
    apply convexHull_min ?_ (convex_halfSpace_le f.isLinear _) hw
    rintro _ ⟨i, rfl⟩
    exact hj i (Finset.mem_univ i)
  have hval : (w * v).re = δ * ‖v‖ := by
    dsimp only [w]
    rw [mul_assoc, mul_comm (conj v) v, Complex.mul_conj, Complex.re_ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq, pow_two, ← mul_assoc,
      div_mul_cancel₀ _ hvn]
  change (w * v).re ≤ _ at hle
  rwa [hval] at hle

private theorem exists_three_contacts_at_affine_minimum {J : Type*} [Fintype J] [Nonempty J]
    (s : J → ℂ) (b : J → ℝ) (hs : (0 : ℂ) ∈ interior (convexHull ℝ (Set.range s))) :
    ∃ x : ℂ, ∃ H : ℝ, (∀ j, (s j * x).re + b j ≤ H) ∧
      (∀ y : ℂ, ∃ j, H ≤ (s j * y).re + b j) ∧
      ∃ r q t : J, r ≠ q ∧ r ≠ t ∧ q ≠ t ∧
        (s r * x).re + b r = H ∧ (s q * x).re + b q = H ∧ (s t * x).re + b t = H := by
  classical
  obtain ⟨δ, hp, hmargin⟩ := affine_margin_of_zero_mem_interior s hs
  obtain ⟨x₀, H, hx₀, hmin⟩ := exists_affine_envelope_minimizer s b δ hp hmargin
  let C (x : ℂ) := Finset.univ.filter (fun j : J => (s j * x).re + b j = H)
  let A := Finset.univ.filter (fun D : Finset J => ∃ x, (∀ j, (s j * x).re + b j ≤ H) ∧ C x = D)
  have hmem (x : ℂ) (j : J) : j ∈ C x ↔ (s j * x).re + b j = H := by simp [C]
  have hA (x : ℂ) (hx : ∀ j, (s j * x).re + b j ≤ H) : C x ∈ A :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, rfl⟩
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image A Finset.card ⟨C x₀, hA x₀ hx₀⟩
  obtain ⟨x, hx, hCx⟩ := (Finset.mem_filter.mp hD).2
  have hcard : 2 < (C x).card := by
    by_contra hno
    have hcover : ∃ r q : J, ∀ j, (s j * x).re + b j = H → j = r ∨ j = q := by
      obtain ⟨r, hr⟩ := hmin x
      have hrmem : r ∈ C x := (hmem x r).mpr (le_antisymm (hx r) hr)
      have hpos : 0 < (C x).card := Finset.card_pos.mpr ⟨r, hrmem⟩
      by_cases h1 : (C x).card = 1
      · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1
        refine ⟨q, q, fun j hj => Or.inl ?_⟩
        simpa only [hq, Finset.mem_singleton] using (hmem x j).mpr hj
      · have h2 : (C x).card = 2 := by omega
        obtain ⟨q, t, _, hqt⟩ := Finset.card_eq_two.mp h2
        refine ⟨q, t, fun j hj => ?_⟩
        simpa only [hqt, Finset.mem_insert, Finset.mem_singleton] using (hmem x j).mpr hj
    obtain ⟨r, q, hcover⟩ := hcover
    obtain ⟨y, hy, hkeep, j, hjlt, hjy⟩ :=
      exists_more_affine_contacts_at_minimum s b x H δ hp hmargin hx hmin r q hcover
    have hsub : C x ⊂ C y := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro k hk
        exact (hmem y k).mpr (hkeep k ((hmem x k).mp hk))
      · intro he
        have hj := (hmem y j).mpr hjy
        rw [← he] at hj
        exact hjlt.ne ((hmem x j).mp hj)
    have hbad := Finset.card_lt_card hsub
    rw [hCx] at hbad
    exact (not_lt_of_ge (hmax _ (hA y hy))) hbad
  obtain ⟨r, q, t, hr, hq, ht, hrq, hrt, hqt⟩ := Finset.two_lt_card_iff.mp hcard
  exact ⟨x, H, hx, hmin, r, q, t, hrq, hrt, hqt, (hmem _ _).mp hr,
    (hmem _ _).mp hq, (hmem _ _).mp ht⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem matchingProduct_update_affine (a b : ι → ℂ) (j : ι) (x : ℂ)
    (σ : Equiv.Perm ι) : matchingProduct a (Function.update b j x) σ =
      matchingCoordinateCoefficient a b σ (.inr j) * x +
        matchingProduct a (Function.update b j 0) σ := by
  have h (y : ℂ) : matchingProduct a (Function.update b j y) σ =
      (a (σ j) + y) * matchingCoordinateCoefficient a b σ (.inr j) := by
    unfold matchingProduct matchingCoordinateCoefficient
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [h x, h 0]
  ring

private theorem determinantValue_update_affine (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (j : ι) (x : ℂ) : determinantValue a (Function.update b j x) U =
      determinantCoordinateCoefficient a b U (.inr j) * x +
        determinantValue a (Function.update b j 0) U := by
  rw [← signed_determinant a _ U hU, ← signed_determinant a (Function.update b j 0) U hU]
  simp_rw [matchingProduct_update_affine a b j x, mul_add, ← mul_assoc]
  rw [Finset.sum_add_distrib, determinantCoordinateCoefficient, Finset.sum_mul]

/-- The complex slope of a matching's projected value minus the projected
determinant when the eigenvalue at label j is varied. -/
def spectralCoordinateSlope (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (j : ι)
    (σ : Equiv.Perm ι) : ℂ :=
  η * (matchingCoordinateCoefficient a b σ (.inr j) - determinantCoordinateCoefficient a b U (.inr j))

/-- The maximum projected matching value minus the projected determinant,
as a function of the second spectrum's coordinate j. -/
def spectralCoordinateDeficit (a b : ι → ℂ) (U : Matrix ι ι ℂ) (η : ℂ) (j : ι) (x : ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun σ : Equiv.Perm ι => (η * matchingProduct a (Function.update b j x) σ).re) -
  (η * determinantValue a (Function.update b j x) U).re

private theorem projected_matching_sub_det_eq (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (η : ℂ) (j : ι) (x : ℂ) (σ : Equiv.Perm ι) :
    (η * matchingProduct a (Function.update b j x) σ).re -
      (η * determinantValue a (Function.update b j x) U).re =
    (spectralCoordinateSlope a b U η j σ * x).re +
      (η * (matchingProduct a (Function.update b j 0) σ -
        determinantValue a (Function.update b j 0) U)).re := by
  rw [← Complex.sub_re, ← mul_sub, ← Complex.add_re]
  congr 1
  rw [matchingProduct_update_affine a b j x σ, determinantValue_update_affine a b U hU j x]
  unfold spectralCoordinateSlope
  ring

/-- The one-coordinate deficit is the upper envelope of the affine scores
of the matching products relative to the determinant. -/
theorem spectralCoordinateDeficit_eq_affineEnvelope (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (η : ℂ) (j : ι) (x : ℂ) :
    spectralCoordinateDeficit a b U η j x =
      Finset.univ.sup' Finset.univ_nonempty (fun σ : Equiv.Perm ι =>
        (spectralCoordinateSlope a b U η j σ * x).re +
        (η * (matchingProduct a (Function.update b j 0) σ -
          determinantValue a (Function.update b j 0) U)).re) := by
  unfold spectralCoordinateDeficit
  simp_rw [← projected_matching_sub_det_eq a b U hU η j x]
  have h (σ : Equiv.Perm ι) :
      (η * matchingProduct a (Function.update b j x) σ).re ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun τ : Equiv.Perm ι => (η * matchingProduct a (Function.update b j x) τ).re) :=
    Finset.le_sup' (fun τ : Equiv.Perm ι => (η * matchingProduct a (Function.update b j x) τ).re)
      (Finset.mem_univ σ)
  apply le_antisymm
  · obtain ⟨σ, hm, hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun τ : Equiv.Perm ι => (η * matchingProduct a (Function.update b j x) τ).re)
    rw [hσ]
    exact Finset.le_sup'
      (fun τ : Equiv.Perm ι =>
        (η * matchingProduct a (Function.update b j x) τ).re -
          (η * determinantValue a (Function.update b j x) U).re) hm
  · exact Finset.sup'_le _ _ (fun σ _ => sub_le_sub_right (h σ) _)

/-- If the slope hull contains zero in its interior, a single complex-coordinate
update minimizes the support deficit and gives three distinct active matchings.
The update preserves any strict violation on this coordinate line. -/
theorem exists_spectralCoordinate_minimum_three_contacts (a b : ι → ℂ)
    (U : Matrix ι ι ℂ) (hU : IsUnitary U) (η : ℂ) (j : ι)
    (hs : (0 : ℂ) ∈ interior (convexHull ℝ (Set.range (spectralCoordinateSlope a b U η j)))) :
    ∃ x : ℂ, (∀ y, spectralCoordinateDeficit a b U η j x ≤ spectralCoordinateDeficit a b U η j y) ∧
      (∀ y, (∀ σ, (η * matchingProduct a (Function.update b j y) σ).re <
        (η * determinantValue a (Function.update b j y) U).re) →
        ∀ σ, (η * matchingProduct a (Function.update b j x) σ).re <
        (η * determinantValue a (Function.update b j x) U).re) ∧
      ∃ r q t : Equiv.Perm ι, r ≠ q ∧ r ≠ t ∧ q ≠ t ∧
        (∀ σ, (η * matchingProduct a (Function.update b j x) σ).re ≤
          (η * matchingProduct a (Function.update b j x) r).re) ∧
        (η * matchingProduct a (Function.update b j x) r).re =
          (η * matchingProduct a (Function.update b j x) q).re ∧
        (η * matchingProduct a (Function.update b j x) r).re =
          (η * matchingProduct a (Function.update b j x) t).re := by
  let s := spectralCoordinateSlope a b U η j
  let c (σ : Equiv.Perm ι) :=
    (η * (matchingProduct a (Function.update b j 0) σ -
      determinantValue a (Function.update b j 0) U)).re
  obtain ⟨x, H, hx, hmin, r, q, t, hrq, hrt, hqt, hr, hq, ht⟩ :=
    exists_three_contacts_at_affine_minimum s c hs
  let d (y : ℂ) (σ : Equiv.Perm ι) :=
    (η * matchingProduct a (Function.update b j y) σ).re -
      (η * determinantValue a (Function.update b j y) U).re
  have hscore (y : ℂ) (σ : Equiv.Perm ι) : d y σ = (s σ * y).re + c σ :=
    projected_matching_sub_det_eq a b U hU η j y σ
  have hdef (y : ℂ) : spectralCoordinateDeficit a b U η j y =
      Finset.univ.sup' Finset.univ_nonempty (d y) := by
    rw [spectralCoordinateDeficit_eq_affineEnvelope a b U hU η j y]
    change Finset.univ.sup' Finset.univ_nonempty (fun σ => (s σ * y).re + c σ) = _
    apply Finset.sup'_congr Finset.univ_nonempty rfl
    intro σ _
    exact (hscore y σ).symm
  have hle (σ : Equiv.Perm ι) : d x σ ≤ H := by rw [hscore]; exact hx σ
  have he (σ : Equiv.Perm ι) (hσ : (s σ * x).re + c σ = H) : d x σ = H :=
      (hscore x σ).trans hσ
  have hDx : spectralCoordinateDeficit a b U η j x = H := by
    rw [hdef]
    refine le_antisymm (Finset.sup'_le _ _ (fun σ _ => hle σ)) ?_
    rw [← he r hr]
    exact Finset.le_sup' _ (Finset.mem_univ r)
  refine ⟨x, ?_, ?_, r, q, t, hrq, hrt, hqt, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := hmin y
    rw [hDx, hdef y]
    exact (hσ.trans_eq (hscore y σ).symm).trans (Finset.le_sup' _ (Finset.mem_univ σ))
  · intro y hy σ
    obtain ⟨τ, hτ⟩ := hmin y
    have h₂ : H < 0 := (hτ.trans_eq (hscore y τ).symm).trans_lt (sub_neg.mpr (hy τ))
    exact sub_neg.mp ((hle σ).trans_lt h₂)
  · intro σ
    have h := (hle σ).trans_eq (he r hr).symm
    dsimp only [d] at h
    linarith only [h]
  · exact sub_left_inj.mp ((he r hr).trans (he q hq).symm)
  · exact sub_left_inj.mp ((he r hr).trans (he t ht).symm)

end

end MOC
