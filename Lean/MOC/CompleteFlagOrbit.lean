import MOC.FlagSuperlevel
import MOC.HighContact
import Mathlib.Topology.Algebra.Group.Quotient

/-! A simple normal spectrum realizes the homogeneous complete flag space. -/

open Matrix

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The embedding of the coordinate torus into the unitary group. -/
def coordinateTorusEmbedding : (ι → Circle) →* Matrix.unitaryGroup ι ℂ where
  toFun t := ⟨coordinateTorusDiagonal t,
    Matrix.mem_unitaryGroup_iff.mpr (coordinateTorusDiagonal_unitary t).1⟩
  map_one' := by
    apply Subtype.ext
    change coordinateTorusDiagonal (1 : ι → Circle) = 1
    simp only [coordinateTorusDiagonal, Pi.one_apply, Circle.coe_one, Matrix.diagonal_one]
  map_mul' s t := by
    apply Subtype.ext
    change coordinateTorusDiagonal (s * t) = coordinateTorusDiagonal s * coordinateTorusDiagonal t
    simp only [coordinateTorusDiagonal, Pi.mul_apply, Circle.coe_mul,
      Matrix.diagonal_mul_diagonal] <;> rfl

/-- The subgroup of diagonal unitary matrices. -/
def unitaryCoordinateTorus (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Subgroup (Matrix.unitaryGroup ι ℂ) :=
  (coordinateTorusEmbedding (ι := ι)).range

private theorem unitaryOfDiagonal_mem_coordinateTorus (U : Matrix.unitaryGroup ι ℂ)
    (d : ι → ℂ) (h : U.val = diagonal d) : U ∈ unitaryCoordinateTorus ι := by
  have hU : U.val * U.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
  rw [h, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at hU
  have hnorm (i : ι) : ‖d i‖ = 1 := by
    have he := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hU
    change (diagonal (fun k => d k * star (d k)) i i).re = ((1 : Matrix ι ι ℂ) i i).re at he
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Complex.star_def,
      Complex.mul_conj, Complex.ofReal_re, Complex.one_re, Complex.normSq_eq_norm_sq] at he
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using he)
  let t (i : ι) : Circle := ⟨d i, Metric.mem_sphere_zero_iff_norm.mpr (hnorm i)⟩
  exact ⟨t, Subtype.ext h.symm⟩

private def flagOrbitMap (b : ι → ℂ) (U : Matrix.unitaryGroup ι ℂ) : spectralFlagOrbit b :=
  ⟨U.val * diagonal b * U.valᴴ,
    ⟨U.val, ⟨Matrix.mem_unitaryGroup_iff.mp U.property, Matrix.mem_unitaryGroup_iff'.mp U.property⟩,
      rfl⟩⟩

private theorem flagOrbitMap_mul (b : ι → ℂ) (V U : Matrix.unitaryGroup ι ℂ) :
    (flagOrbitMap b (V * U)).val = V.val * (flagOrbitMap b U).val * V.valᴴ := by
  change (V.val * U.val) * diagonal b * (V.val * U.val)ᴴ = _
  simp only [flagOrbitMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem flagOrbitMap_eq_iff (b : ι → ℂ) (hb : Function.Injective b)
    (V U : Matrix.unitaryGroup ι ℂ) : flagOrbitMap b V = flagOrbitMap b U ↔
      V⁻¹ * U ∈ unitaryCoordinateTorus ι := by
  constructor
  · intro h
    let W := V⁻¹ * U
    have hW : (flagOrbitMap b W).val = diagonal b := by
      have he := congrArg (fun X : spectralFlagOrbit b => V.valᴴ * X.val * V.val) h
      have hVV : V.valᴴ * V.val = 1 := Matrix.mem_unitaryGroup_iff'.mp V.property
      have hleft : V.valᴴ * (flagOrbitMap b V).val * V.val = diagonal b := by
        change V.valᴴ * (V.val * diagonal b * V.valᴴ) * V.val = _
        calc
          _ = (V.valᴴ * V.val) * diagonal b * (V.valᴴ * V.val) := by
            simp only [Matrix.mul_assoc]
          _ = _ := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
      rw [hleft] at he
      change (V.valᴴ * U.val) * diagonal b * (V.valᴴ * U.val)ᴴ = _
      simpa only [flagOrbitMap, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc] using he.symm
    have hWW : W.valᴴ * W.val = 1 := Matrix.mem_unitaryGroup_iff'.mp W.property
    have hcomm : W.val * diagonal b = diagonal b * W.val := by
      have h' := congrArg (fun X : Matrix ι ι ℂ => X * W.val) hW
      change W.val * diagonal b * W.valᴴ * W.val = _ at h'
      simpa only [Matrix.mul_assoc, hWW, Matrix.mul_one] using h'
    apply unitaryOfDiagonal_mem_coordinateTorus W W.val.diag
    ext i j : 1
    by_cases hne : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.diag_apply]
    · rw [Matrix.diagonal_apply_ne _ hne]
      have hentry := congrArg (fun X : Matrix ι ι ℂ => X i j) hcomm
      change (W.val * diagonal b) i j = (diagonal b * W.val) i j at hentry
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
      have hzero : W.val i j * (b j - b i) = 0 := by linear_combination hentry
      exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr (hb.ne hne.symm))
  · rintro ⟨t, ht⟩
    have hU : V * coordinateTorusEmbedding t = U := by
      rw [ht]
      simp
    have hfix : (flagOrbitMap b (coordinateTorusEmbedding t)).val = diagonal b :=
      coordinateTorusConj_diagonal t b
    apply Subtype.ext
    rw [← hU, flagOrbitMap_mul, hfix] <;> rfl

private def flagCosetOrbit (b : ι → ℂ) (hb : Function.Injective b) :
    Matrix.unitaryGroup ι ℂ ⧸ unitaryCoordinateTorus ι → spectralFlagOrbit b :=
  Quotient.lift (flagOrbitMap b) (fun V U h =>
    (flagOrbitMap_eq_iff b hb V U).mpr (QuotientGroup.leftRel_apply.mp h))

/-- For distinct eigenvalues, conjugation is a homeomorphism from the
complete flag space onto the spectral orbit. -/
def completeFlagOrbitHomeomorph (b : ι → ℂ) (hb : Function.Injective b) :
    Matrix.unitaryGroup ι ℂ ⧸ unitaryCoordinateTorus ι ≃ₜ spectralFlagOrbit b := by
  have hs : {U : Matrix ι ι ℂ | IsUnitary U} = (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
    ext U
    exact ⟨fun h => Matrix.mem_unitaryGroup_iff.mpr h.1,
      fun h => ⟨Matrix.mem_unitaryGroup_iff.mp h, Matrix.mem_unitaryGroup_iff'.mp h⟩⟩
  letI : CompactSpace (Matrix.unitaryGroup ι ℂ) :=
    isCompact_iff_compactSpace.mp (hs ▸ isCompact_setOf_isUnitary)
  have hc : Continuous (flagCosetOrbit b hb) := by
    apply (QuotientGroup.isQuotientMap_mk (unitaryCoordinateTorus ι)).continuous_iff.mpr
    change Continuous (flagOrbitMap b)
    have hm : Continuous (fun U : Matrix ι ι ℂ => U * diagonal b * Uᴴ) := by fun_prop
    exact (hm.comp continuous_subtype_val).subtype_mk _
  let e := Equiv.ofBijective (flagCosetOrbit b hb) (by
    constructor
    · intro x y h
      obtain ⟨V, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨U, rfl⟩ := QuotientGroup.mk_surjective y
      exact QuotientGroup.eq.mpr ((flagOrbitMap_eq_iff b hb V U).mp h)
    · intro X
      obtain ⟨U, hU, hX⟩ := X.property
      let V : Matrix.unitaryGroup ι ℂ := ⟨U, Matrix.mem_unitaryGroup_iff.mpr hU.1⟩
      exact ⟨QuotientGroup.mk V, Subtype.ext hX⟩)
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap

/-- Left multiplication of a flag representative by a diagonal unitary
becomes the coordinate-torus action on the spectral orbit. -/
theorem completeFlagOrbitHomeomorph_torus (b : ι → ℂ) (hb : Function.Injective b)
    (t : ι → Circle) (U : Matrix.unitaryGroup ι ℂ) :
    completeFlagOrbitHomeomorph b hb (QuotientGroup.mk (coordinateTorusEmbedding t * U)) =
      t • completeFlagOrbitHomeomorph b hb (QuotientGroup.mk U) := by
  apply Subtype.ext
  change (flagOrbitMap b (coordinateTorusEmbedding t * U)).val =
    coordinateTorusConj t (flagOrbitMap b U).val
  rw [flagOrbitMap_mul] <;> rfl

/-- Simple spectra suffice for the flag superlevel formulation. -/
theorem conjecture_iff_simpleFlagSuperlevel_fixed : Conjecture ι ↔
    ∀ (a b : ι → ℂ), Function.Injective b → ∀ (η : ℂ) (r : ℝ),
      (flagDeterminantSuperlevel a b η r).Nonempty →
      ∃ X ∈ flagDeterminantSuperlevel a b η r,
        ∀ t : ι → Circle, coordinateTorusConj t X = X := by
  constructor
  · intro h a b _ η r hX
    exact conjecture_iff_flagSuperlevel_fixed.mp h a b η r hX
  · intro h
    apply conjecture_iff_regular_matching_products.mpr
    intro a b U hU _ hinj
    apply (holds_iff_directional a b U).mpr
    intro η
    obtain ⟨p, _, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun p : Equiv.Perm ι => (η * matchingProduct a b p).re) Finset.univ_nonempty
    let r := (η * matchingProduct a b p).re
    refine ⟨p, le_of_not_gt fun hgt => ?_⟩
    have hX : (flagDeterminantSuperlevel a b η r).Nonempty :=
      ⟨U * diagonal b * Uᴴ, ⟨U, hU, rfl⟩, hgt⟩
    have hb := (injective_spectra_of_matchingProduct_injective hinj).2
    obtain ⟨X, hX, hfix⟩ := h a b hb η r hX
    obtain ⟨q, rfl⟩ := (spectralFlagOrbit_fixed_iff b X).mp ⟨hX.1, hfix⟩
    have hlt := hX.2
    change r < flagDeterminantScore a η (diagonal (b ∘ q)) at hlt
    rw [flagDeterminantScore_permutation] at hlt
    exact (not_lt_of_ge (hmax q.symm (Finset.mem_univ _))) hlt

end

end MOC
