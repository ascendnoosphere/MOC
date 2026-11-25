import MOC.Geometry
import MOC.Support
import MOC.Variational
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! At an attained nonsingular boundary value, the orbit derivative lies in
a real line. A normal to that line gives the Hermitian inverse commutator. -/

open BigOperators Filter Matrix
open scoped Topology

namespace MOC

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private theorem phase_of_dual (φ : ℂ →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) :
    ∃ η : ℂ, η ≠ 0 ∧ ∀ z : ℂ, φ z = (η * z).re := by
  let η := (φ 1 : ℂ) - (φ Complex.I : ℂ) * Complex.I
  have he (z : ℂ) : φ z = (η * z).re := by
    have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
      simp [Complex.real_smul, Complex.re_add_im]
    calc
      φ z = φ (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg φ hz.symm
      _ = (η * z).re := by
        rw [map_add, map_smul, map_smul]
        simp [η, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, smul_eq_mul]
        ring
  refine ⟨η, ?_, he⟩
  intro hη
  apply hφ
  ext z
  simp only [he, hη, zero_mul, Complex.zero_re, LinearMap.zero_apply]

/-- Every unitary attaining a nonsingular boundary value has a Hermitian
inverse commutator after multiplying by a nonzero complex scalar. -/
theorem boundary_inverse_commutator (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) (hdet : determinantValue a b U ≠ 0)
    (hbd : determinantValue a b U ∈ frontier (determinantRange a b)) :
    let B := U * diagonal b * Uᴴ
    let C := diagonal a + B
    ∃ η : ℂ, η ≠ 0 ∧
      let D := (η * C.det) • (B * C⁻¹ - C⁻¹ * B)
      Dᴴ = D := by
  let A := diagonal a
  let B := U * diagonal b * Uᴴ
  let C := A + B
  let S := skewAdjoint.submodule ℝ (Matrix ι ι ℂ)
  let M (X : S) := A + NormedSpace.exp ℝ (X : Matrix ι ι ℂ) * B *
    NormedSpace.exp ℝ (-(X : Matrix ι ι ℂ))
  let f (X : S) := (M X).det
  have h₀ : f 0 = determinantValue a b U := by
    simp [f, M, A, B, determinantValue, NormedSpace.exp_zero]
  have hSmooth : ContDiffAt ℝ 1 f 0 := by
    have hExp : ContDiffAt ℝ 1 (NormedSpace.exp ℝ : Matrix ι ι ℂ → Matrix ι ι ℂ) 0 :=
      (NormedSpace.exp_analytic (𝕂 := ℝ) (0 : Matrix ι ι ℂ)).contDiffAt
    have hp : ContDiffAt ℝ 1 (fun X : S => NormedSpace.exp ℝ (X : Matrix ι ι ℂ)) 0 :=
      hExp.comp (0 : S) S.subtypeL.contDiff.contDiffAt
    have hn : ContDiffAt ℝ 1 (fun X : S => NormedSpace.exp ℝ (-(X : Matrix ι ι ℂ))) 0 :=
      have hg : ContDiffAt ℝ 1 (NormedSpace.exp ℝ : Matrix ι ι ℂ → Matrix ι ι ℂ)
          ((-S.subtypeL) 0) := by simpa only [map_zero] using hExp
      hg.comp (0 : S) (-S.subtypeL).contDiff.contDiffAt
    have hm : ContDiffAt ℝ 1 M 0 := contDiffAt_const.add ((hp.mul contDiffAt_const).mul hn)
    simp only [f, Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro i _
    let entry : Matrix ι ι ℂ →L[ℝ] ℂ :=
      ⟨Matrix.entryLinearMap ℝ ℂ (σ i) i, continuous_apply_apply (σ i) i⟩
    exact entry.contDiff.contDiffAt.comp 0 hm
  let L := fderiv ℝ f 0
  have hproper : LinearMap.range L.toLinearMap ≠ ⊤ := by
    intro htop
    letI : CompleteSpace S := FiniteDimensional.complete ℝ S
    have hmap := (hSmooth.hasStrictFDerivAt le_rfl).map_nhds_eq_of_surj htop
    have hrange : Set.range f ∈ Filter.map f (𝓝 (0 : S)) := by
      rw [Filter.mem_map]
      exact Filter.Eventually.of_forall (fun X : S => Set.mem_range_self (f := f) X)
    have hsub : Set.range f ⊆ determinantRange a b := by
      rintro z ⟨X, rfl⟩
      let V := NormedSpace.exp ℝ (X : Matrix ι ι ℂ)
      have hXV : (X : Matrix ι ι ℂ) ∈ skewAdjoint (Matrix ι ι ℂ) := X.property
      have hx : (X : Matrix ι ι ℂ)ᴴ = -(X : Matrix ι ι ℂ) :=
        skewAdjoint.mem_iff.mp hXV
      have hVe := unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ℝ hXV)
      have hV : IsUnitary V := ⟨hVe.2, hVe.1⟩
      have hvstar : Vᴴ = NormedSpace.exp ℝ (-(X : Matrix ι ι ℂ)) := by
        change (NormedSpace.exp ℝ (X : Matrix ι ι ℂ))ᴴ = _
        rw [← Matrix.exp_conjTranspose ℝ, hx]
      have hU' : IsUnitary Vᴴ := ⟨by simpa using hV.2, by simpa using hV.1⟩
      have hVU : IsUnitary (V * U) := by
        simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Vᴴ U hU' hU
      refine ⟨V * U, hVU, ?_⟩
      simp only [determinantValue, f, M, A, B, ← hvstar, V, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hi : f 0 ∈ interior (determinantRange a b) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hmap ▸ hrange) hsub)
    rw [h₀] at hi
    exact hbd.2 hi
  obtain ⟨φ, hφ, hkill⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hproper) inferInstance
  obtain ⟨η, hη, he⟩ := phase_of_dual φ hφ
  refine ⟨η, hη, ?_⟩
  change (((η * C.det) • (B * C⁻¹ - C⁻¹ * B)))ᴴ = (η * C.det) • (B * C⁻¹ - C⁻¹ * B)
  apply conjTranspose_eq_of_real_trace_mul_skew_eq_zero
  intro X hx
  let x : S := ⟨X, skewAdjoint.mem_iff.mpr hx⟩
  have hzero : φ (L x) = 0 := by
    have hmem : φ (L x) ∈ (LinearMap.range L.toLinearMap).map φ :=
      Submodule.mem_map.mpr ⟨L x, ⟨x, rfl⟩, rfl⟩
    rw [hkill, Submodule.mem_bot] at hmem
    exact hmem
  have hline : HasDerivAt (fun t : ℝ => f (t • x)) (L x) 0 := by
    have hpath : HasDerivAt (fun t : ℝ => t • x) x 0 := by
      simpa only [one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const x
    exact (hSmooth.hasStrictFDerivAt le_rfl).hasFDerivAt.comp_hasDerivAt_of_eq
      (0 : ℝ) hpath (zero_smul ℝ x).symm
  have hexp : HasDerivAt (fun t : ℝ => f (t • x))
      (C.det * ((B * C⁻¹ - C⁻¹ * B) * X).trace) 0 := by
    change HasDerivAt (fun t : ℝ => (A + NormedSpace.exp ℝ (t • X) * B *
      NormedSpace.exp ℝ (-(t • X))).det) _ 0
    simp only [← smul_neg]
    exact hasDerivAt_orbit_determinant A B X hdet
  rw [he, hline.unique hexp] at hzero
  simpa only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_assoc] using hzero

/-- A maximum in a nonzero support direction is an attained boundary value. -/
theorem determinant_support_mem_frontier (a b : ι → ℂ) (U : Matrix ι ι ℂ)
    (hU : IsUnitary U) {η : ℂ} (hη : η ≠ 0)
    (hmax : ∀ V : Matrix ι ι ℂ, IsUnitary V →
      (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) :
    determinantValue a b U ∈ frontier (determinantRange a b) := by
  let d := determinantValue a b U
  refine ⟨subset_closure ⟨U, hU, rfl⟩, ?_⟩
  intro hi
  let w (t : ℝ) := d + (t : ℂ) * star η
  have hw : Continuous w := by
    change Continuous (fun t : ℝ => d + (t : ℂ) * star η)
    fun_prop
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), w t ∈ determinantRange a b := by
    apply hw.continuousAt.eventually_mem
    simpa only [w, Complex.ofReal_zero, zero_mul, add_zero] using
      (mem_interior_iff_mem_nhds.mp hi : determinantRange a b ∈ 𝓝 d)
  obtain ⟨t, ht, htpos⟩ :=
    ((hevent.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  obtain ⟨V, hV, hVal⟩ := ht
  have hrew : (η * w t).re = (η * d).re + t * Complex.normSq η := by
    rw [show η * w t = η * d + (t : ℂ) * (η * star η) by dsimp [w]; ring,
      Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.add_re, Complex.ofReal_re]
  have hs := hmax V hV
  rw [hVal, hrew] at hs
  exact (not_le_of_gt (lt_add_of_pos_right _ (mul_pos htpos (Complex.normSq_pos.mpr hη)))) hs

/-- The boundary inclusion for fixed spectra is equivalent to the inclusion
for every unitary mixer. -/
theorem determinant_frontier_subset_iff (a b : ι → ℂ) :
    frontier (determinantRange a b) ⊆ convexHull ℝ (Set.range (matchingProduct a b)) ↔
      ∀ U : Matrix ι ι ℂ, IsUnitary U → Holds a b U := by
  constructor
  · intro h U hU
    apply (holds_iff_directional a b U).mpr
    intro η
    by_cases hη : η = 0
    · exact ⟨1, by simp [hη]⟩
    obtain ⟨V, hV, hmax⟩ := exists_support_maximizer a b η
    have hVh : Holds a b V := h (determinant_support_mem_frontier a b V hV hη hmax)
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b V).mp hVh η
    exact ⟨σ, (hmax U hU).trans hσ⟩
  · intro h z hz
    have hc : IsCompact (determinantRange a b) := by
      have hd : Continuous (determinantValue a b) := by unfold determinantValue; fun_prop
      change IsCompact (determinantValue a b '' {U : Matrix ι ι ℂ | IsUnitary U})
      exact isCompact_setOf_isUnitary.image hd
    obtain ⟨U, hU, rfl⟩ := hc.isClosed.frontier_subset hz
    exact h U hU

/-- The determinant image of a difference of two unitary matrices lies on a
fixed real line through zero as the second summand varies by conjugation. -/
theorem star_det_sub_mul_unitary_dets (A B : Matrix ι ι ℂ)
    (hA : IsUnitary A) (hB : IsUnitary B) :
    star ((A - B).det) * (A.det * B.det) =
      (-1 : ℂ) ^ Fintype.card ι * (A - B).det := by
  have hstar : (A - B)ᴴ = Aᴴ * (B - A) * Bᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc Aᴴ B Bᴴ,
      hA.2, hB.1, Matrix.one_mul, Matrix.mul_one]
  have ha : Aᴴ.det * A.det = 1 := by rw [← Matrix.det_mul, hA.2, Matrix.det_one]
  have hb : Bᴴ.det * B.det = 1 := by rw [← Matrix.det_mul, hB.2, Matrix.det_one]
  rw [← Matrix.det_conjTranspose, hstar, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = (Aᴴ.det * A.det) * (Bᴴ.det * B.det) * (B - A).det := by ring
    _ = _ := by rw [ha, hb, one_mul, one_mul, ← neg_sub A B, Matrix.det_neg]

end

end MOC
