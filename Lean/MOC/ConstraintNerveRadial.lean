import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Radial reduction of simultaneous linear observations on a finite convex hull.

See Boyd and Vandenberghe, *Convex Optimization*, §2.3.3, pp. 39–40, for
perspective normalization on the positive half-space.
https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf
-/

open BigOperators Set

namespace MOC

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

private def constraintTranslation (target : E) : E →ᵃ[ℝ] E where
  toFun x := x - target
  linear := LinearMap.id
  map_vadd' p v := add_sub_assoc v p target

/-- Radial normalization onto the affine hyperplane where the linear functional is one. -/
def radialNormalization (ℓ : E →ₗ[ℝ] ℝ) (x : E) : E := (ℓ x)⁻¹ • x

theorem radialNormalization_map_eq_one (ℓ : E →ₗ[ℝ] ℝ) {x : E} (hx : ℓ x ≠ 0) :
    ℓ (radialNormalization ℓ x) = 1 := by
  rw [radialNormalization, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]

theorem linearMap_radialNormalization_eq_zero_iff (ℓ : E →ₗ[ℝ] ℝ) (a : E →ₗ[ℝ] F)
    {x : E} (hx : ℓ x ≠ 0) : a (radialNormalization ℓ x) = 0 ↔ a x = 0 := by
  rw [radialNormalization, map_smul]
  constructor
  · intro h
    have he := congrArg (fun v : F => ℓ x • v) h
    simpa only [smul_smul, mul_inv_cancel₀ hx, one_smul, smul_zero] using he
  · intro h
    rw [h, smul_zero]

/-- Radial normalization of a positively separated convex hull is the convex hull
of the normalized points. -/
theorem radialNormalization_image_convexHull (ℓ : E →ₗ[ℝ] ℝ) (s : Set E)
    (hℓ : ∀ x ∈ s, 0 < ℓ x) :
    radialNormalization ℓ '' convexHull ℝ s = convexHull ℝ (radialNormalization ℓ '' s) := by
  classical
  have hpos : ∀ x ∈ convexHull ℝ s, 0 < ℓ x :=
    convexHull_min (t := ℓ ⁻¹' Ioi (0 : ℝ)) hℓ ((convex_Ioi _).linear_preimage ℓ)
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ι, inst, w, v, hw₀, _, hv, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hx
    letI : Fintype ι := inst
    let b (i : ι) := (ℓ x)⁻¹ * (w i * ℓ (v i))
    have hlinear : (∑ i, w i * ℓ (v i)) = ℓ x := by
      simpa only [map_sum, map_smul, smul_eq_mul] using congrArg ℓ hsum
    refine mem_convexHull_of_exists_fintype b (radialNormalization ℓ ∘ v) ?_ ?_ ?_ ?_
    · intro i
      exact mul_nonneg (inv_nonneg.mpr (hpos x hx).le) (mul_nonneg (hw₀ i) (hℓ _ (hv i)).le)
    · change (∑ i, (ℓ x)⁻¹ * (w i * ℓ (v i))) = 1
      rw [← Finset.mul_sum, hlinear, inv_mul_cancel₀ (hpos x hx).ne']
    · exact fun i => Set.mem_image_of_mem _ (hv i)
    · calc
        (∑ i, b i • radialNormalization ℓ (v i)) =
            ∑ i, (ℓ x)⁻¹ • (w i • v i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [b, radialNormalization, smul_smul, mul_assoc,
            mul_inv_cancel₀ (hℓ _ (hv i)).ne', mul_one]
        _ = radialNormalization ℓ x := by
          rw [← Finset.smul_sum, hsum, radialNormalization]
  · intro y hy
    obtain ⟨ι, inst, w, u, hw₀, hw₁, hu, hySum⟩ := mem_convexHull_iff_exists_fintype.mp hy
    letI : Fintype ι := inst
    choose v hv hnormalize using hu
    let a (i : ι) := w i * (ℓ (v i))⁻¹
    let q := ∑ i, a i
    have ha (i : ι) : 0 ≤ a i :=
      mul_nonneg (hw₀ i) (inv_nonneg.mpr (hℓ _ (hv i)).le)
    have hwpos : ∃ i, 0 < w i := by
      by_contra! hn
      have hz (i : ι) : w i = 0 := le_antisymm (hn i) (hw₀ i)
      simpa only [hz, Finset.sum_const_zero, zero_ne_one] using hw₁
    obtain ⟨j, hj⟩ := hwpos
    have hq : 0 < q :=
      (mul_pos hj (inv_pos.mpr (hℓ _ (hv j)))).trans_le
        (Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ j))
    have hℓy : ℓ y = 1 := by
      rw [← hySum, map_sum]
      calc
        (∑ i, ℓ (w i • u i)) = ∑ i, w i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul, smul_eq_mul, ← hnormalize i,
            radialNormalization_map_eq_one ℓ (hℓ _ (hv i)).ne', mul_one]
        _ = 1 := hw₁
    refine ⟨q⁻¹ • y, ?_, ?_⟩
    · refine mem_convexHull_of_exists_fintype (fun i => q⁻¹ * a i) v ?_ ?_ hv ?_
      · exact fun i => mul_nonneg (inv_nonneg.mpr hq.le) (ha i)
      · rw [← Finset.mul_sum, inv_mul_cancel₀ hq.ne']
      · calc
          (∑ i, (q⁻¹ * a i) • v i) = q⁻¹ • ∑ i, w i • u i := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← hnormalize i]
            simp only [a, radialNormalization, smul_smul, mul_assoc]
          _ = q⁻¹ • y := by rw [hySum]
    · rw [radialNormalization, map_smul, smul_eq_mul, hℓy, mul_one, inv_inv, smul_smul,
        mul_inv_cancel₀ hq.ne', one_smul]

/-- In the affine span of the original points, radial normalization reduces the
affine dimension by at least one when that span contains the origin. -/
theorem radialNormalization_affineSpan_finrank_add_one_le [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) (s : Set E) (hs : s.Nonempty) (hzero : 0 ∈ affineSpan ℝ s)
    (hℓ : ∀ x ∈ s, 0 < ℓ x) :
    Module.finrank ℝ (affineSpan ℝ (radialNormalization ℓ '' s)).direction + 1 ≤
      Module.finrank ℝ (affineSpan ℝ s).direction := by
  let V := (affineSpan ℝ s).direction
  let W := (affineSpan ℝ (radialNormalization ℓ '' s)).direction
  have hsV (x : E) (hx : x ∈ s) : x ∈ V := by
    have hxdir := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ s hx) hzero
    simpa only [vsub_eq_sub, sub_zero, V] using hxdir
  have hWV : W ≤ V := by
    change (affineSpan ℝ (radialNormalization ℓ '' s)).direction ≤
      (affineSpan ℝ s).direction
    apply AffineSubspace.direction_le
    apply affineSpan_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change radialNormalization ℓ x ∈ affineSpan ℝ s
    rw [← AffineSubspace.mk'_eq hzero, AffineSubspace.mem_mk', vsub_eq_sub, sub_zero]
    exact V.smul_mem _ (hsV x hx)
  obtain ⟨p, hp⟩ := hs
  let e := radialNormalization ℓ p
  have he : ℓ e = 1 := radialNormalization_map_eq_one ℓ (hℓ p hp).ne'
  have hWker : W ≤ LinearMap.ker ℓ := by
    have hsub : affineSpan ℝ (radialNormalization ℓ '' s) ≤
        AffineSubspace.mk' e (LinearMap.ker ℓ) := by
      apply affineSpan_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      change radialNormalization ℓ x ∈ AffineSubspace.mk' e (LinearMap.ker ℓ)
      rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub,
        radialNormalization_map_eq_one ℓ (hℓ x hx).ne', he, sub_self]
    simpa only [W, AffineSubspace.direction_mk'] using AffineSubspace.direction_le hsub
  let L : V →ₗ[ℝ] ℝ := ℓ.comp V.subtype
  have hL : L ≠ 0 := by
    intro h
    have hpzero : ℓ p = 0 := congrArg (fun g : V →ₗ[ℝ] ℝ => g ⟨p, hsV p hp⟩) h
    exact (hℓ p hp).ne' hpzero
  let A : W →ₗ[ℝ] LinearMap.ker L := (Submodule.inclusion hWV).codRestrict _
    (fun x => LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp (hWker x.property)))
  have hA : Function.Injective A := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : LinearMap.ker L => ((z : V) : E)) h)
  calc
    Module.finrank ℝ W + 1 ≤ Module.finrank ℝ (LinearMap.ker L) + 1 :=
      Nat.add_le_add_right (LinearMap.finrank_le_finrank_of_injective hA) 1
    _ = Module.finrank ℝ V := Module.Dual.finrank_ker_add_one_of_ne_zero hL

/-- When the target belongs to the original affine span, the radial image of
the translated points has affine dimension at least one less. -/
theorem radialNormalization_translated_affineSpan_finrank_add_one_le [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) (s : Set E) (target : E) (hs : s.Nonempty)
    (htarget : target ∈ affineSpan ℝ s) (hℓ : ∀ x ∈ s, 0 < ℓ (x - target)) :
    Module.finrank ℝ
      (affineSpan ℝ ((fun x => radialNormalization ℓ (x - target)) '' s)).direction + 1 ≤
      Module.finrank ℝ (affineSpan ℝ s).direction := by
  let τ := constraintTranslation target
  let t := τ '' s
  have hspan : (affineSpan ℝ s).map τ = affineSpan ℝ t := AffineSubspace.map_span τ s
  have hz : (0 : E) ∈ affineSpan ℝ t := by
    rw [← hspan]
    exact AffineSubspace.mem_map.mpr ⟨target, htarget, sub_self target⟩
  have hdim : (affineSpan ℝ t).direction = (affineSpan ℝ s).direction := by
    rw [← hspan, AffineSubspace.map_direction]
    change (affineSpan ℝ s).direction.map LinearMap.id = (affineSpan ℝ s).direction
    rw [Submodule.map_id]
  have himage : radialNormalization ℓ '' t = (fun x => radialNormalization ℓ (x - target)) '' s :=
    Set.image_image (radialNormalization ℓ) τ s
  rw [← himage, ← hdim]
  apply radialNormalization_affineSpan_finrank_add_one_le ℓ t (hs.image τ) hz
  rintro _ ⟨x, hx, rfl⟩
  exact hℓ x hx

section Normed

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {I : Type*}

/-- A target outside a finite convex hull can be translated to zero and strictly
separated. Radial normalization then gives a finite convex hull in the hyperplane
where the separator is one and preserves feasibility of every subfamily of the
linear observation equations. -/
theorem exists_constraint_nerve_radial_reduction (vertices : Set G) (hfinite : vertices.Finite)
    (target : G) (hout : target ∉ convexHull ℝ vertices) (coord : I → G →ₗ[ℝ] F) :
    ∃ ℓ : G →L[ℝ] ℝ,
      (∀ x ∈ convexHull ℝ vertices, 0 < ℓ (x - target)) ∧
      let r (x : G) := radialNormalization ℓ.toLinearMap (x - target)
      r '' convexHull ℝ vertices = convexHull ℝ (r '' vertices) ∧
      (∀ y ∈ convexHull ℝ (r '' vertices), ℓ y = 1) ∧
      ∀ J : Set I,
        (∃ x ∈ convexHull ℝ vertices, ∀ i ∈ J, coord i x = coord i target) ↔
        (∃ y ∈ convexHull ℝ (r '' vertices), ∀ i ∈ J, coord i y = 0) := by
  let τ := constraintTranslation target
  let s := τ '' vertices
  have hτ : τ '' convexHull ℝ vertices = convexHull ℝ s := τ.image_convexHull vertices
  have hzero : (0 : G) ∉ convexHull ℝ s := by
    rw [← hτ]
    rintro ⟨x, hx, hxt⟩
    have he : x = target := sub_eq_zero.mp hxt
    exact hout (he ▸ hx)
  obtain ⟨ℓ, δ, hδ, hℓ⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ s)
    (hfinite.image τ).isClosed_convexHull hzero
  have hpos (x : G) (hx : x ∈ convexHull ℝ s) : 0 < ℓ x :=
    (show 0 < δ by simpa only [map_zero] using hδ).trans (hℓ x hx)
  have hsource (x : G) (hx : x ∈ convexHull ℝ vertices) : 0 < ℓ (x - target) := by
    have h := Set.mem_image_of_mem τ hx
    rw [hτ] at h
    exact hpos (τ x) h
  let r (x : G) := radialNormalization ℓ.toLinearMap (x - target)
  have himage : r '' convexHull ℝ vertices = convexHull ℝ (r '' vertices) := by
    change (radialNormalization ℓ.toLinearMap ∘ τ) '' convexHull ℝ vertices =
      convexHull ℝ ((radialNormalization ℓ.toLinearMap ∘ τ) '' vertices)
    simpa only [← Set.image_image, hτ] using
      radialNormalization_image_convexHull ℓ.toLinearMap s
        (fun x hx => hpos x (subset_convexHull ℝ s hx))
  refine ⟨ℓ, hsource, himage, ?_, ?_⟩
  · rw [← himage]
    rintro _ ⟨x, hx, rfl⟩
    exact radialNormalization_map_eq_one ℓ.toLinearMap (hsource x hx).ne'
  · intro J
    rw [← himage]
    constructor
    · rintro ⟨x, hx, hcoord⟩
      refine ⟨r x, Set.mem_image_of_mem r hx, fun i hi => ?_⟩
      apply (linearMap_radialNormalization_eq_zero_iff ℓ.toLinearMap (coord i)
        (hsource x hx).ne').2
      rw [map_sub, hcoord i hi, sub_self]
    · rintro ⟨_, ⟨x, hx, rfl⟩, hcoord⟩
      refine ⟨x, hx, fun i hi => sub_eq_zero.mp ?_⟩
      have h := (linearMap_radialNormalization_eq_zero_iff ℓ.toLinearMap (coord i)
        (hsource x hx).ne').mp (hcoord i hi)
      simpa only [map_sub] using h

end Normed

end

end MOC
