import MOC.FourMinorTransport
import MOC.FourT34MinorBranch
import MOC.FourT34RadialSupport

/-! The T34 certificate in the original spectral support coordinates. -/

namespace MOC

open BigOperators Matrix

noncomputable section

private abbrev MinorTable (R : Type*) := Finset (Fin 4) → Finset (Fin 4) → R

private def matchingMinorTable {R : Type*} [Zero R] [One R] (σ : FourPerm) : MinorTable R :=
  fun I J => if J.map σ.toEmbedding = I then 1 else 0

private def doubleMinorMap : MinorTable ℝ →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := FourT34QuaternionGram.doubleMinorForm
  map_add' := by
    intro m n
    funext i
    fin_cases i <;> simp [FourT34QuaternionGram.doubleMinorForm] <;> ring
  map_smul' := by
    intro c m
    funext i
    fin_cases i <;> simp [FourT34QuaternionGram.doubleMinorForm, smul_eq_mul] <;> ring

private def t34Coordinates : Fin 8 → Fin 14 → ℤ :=
  ![![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1],
    ![0, 1, 0, -1, 0, 0, -1, 0, 0, 1, 0, -1, 0, 0],
    ![-1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 1, 0],
    ![-1, 1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0],
    ![-1, 1, 0, -1, 1, 1, 0, -1, 1, 1, -1, -1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem exact_t34_profile :
    ∀ (k : Fin 8) (i : Fin 24), 2 * fourMatchingEvaluation (t34Coordinates k) i =
      FourT34QuaternionGram.doubleMinorForm (matchingMinorTable (fourPerm i).symm) k := by
  decide +kernel

private theorem cast_doubleMinorForm (σ : FourPerm) (k : Fin 8) :
    ((FourT34QuaternionGram.doubleMinorForm (matchingMinorTable σ) k : ℤ) : ℝ) =
      FourT34QuaternionGram.doubleMinorForm (matchingMinorTable σ) k := by
  fin_cases k <;>
    simp [FourT34QuaternionGram.doubleMinorForm, matchingMinorTable, apply_ite]

set_option maxHeartbeats 4000000 in
private theorem t34HeightLift_eval (p r a b c q d s H : ℝ) (i : Fin 24) :
    fourMatchingEvaluation (t34HeightLift p r a b c q d s H) i - H =
      ∑ k : Fin 8, (![p, r, a, b, c, q, d, s] : Fin 8 → ℝ) k *
        (FourT34QuaternionGram.doubleMinorForm (matchingMinorTable (fourPerm i).symm) k / 2) := by
  have hcast (k : Fin 8) :
      FourT34QuaternionGram.doubleMinorForm (matchingMinorTable (fourPerm i).symm) k =
        2 * ((fourMatchingEvaluation (t34Coordinates k) i : ℤ) : ℝ) := by
    rw [← cast_doubleMinorForm, ← exact_t34_profile, Int.cast_mul, Int.cast_ofNat]
  simp_rw [hcast]
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, fourMatchingEvaluation, t34HeightLift, t34Coordinates] <;> ring

private theorem t34_signed_minor_response (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (k : Fin 8) :
    (∑ σ : FourPerm, realSignedWeight U σ *
        FourT34QuaternionGram.doubleMinorForm (matchingMinorTable σ) k) =
      FourT34QuaternionGram.doubleMinorResponse U k := by
  have hm : (subsetMinorSq U : MinorTable ℝ) =
      ∑ σ : FourPerm, realSignedWeight U σ • matchingMinorTable σ := by
    funext I J
    have h := congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)
    simp only [Finset.sum_filter, Complex.re_sum, apply_ite, Complex.zero_re, Complex.ofReal_re] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, matchingMinorTable, mul_ite, mul_one, mul_zero]
    exact h.symm
  change _ = doubleMinorMap (subsetMinorSq U) k
  rw [hm, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] <;> rfl

/-- The eight T34 source coefficients in the order of the minor response. -/
def fourT34GapBudgets (g : Fin 24 → ℝ) : Fin 8 → ℝ :=
  ![g 18, g 16, g 13, g 8, g 4, g 14, g 11, g 7]

/-- The difference from the contact height is half the full minor response
of the exact T34 gap budgets. -/
theorem fourT34_projected_gap_eq_response (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
    (η * determinantValue α β U).re - H =
      ∑ k, fourT34GapBudgets g k * FourT34QuaternionGram.doubleMinorResponse U k / 2 := by
  let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
  let w := fourT34GapBudgets g
  let m (i : Fin 14) := (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct α β (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part α β η i
  have hrep : m = t34HeightLift (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7) H := by
    have h := fourT34_height_lift_of_contacts m H (fun i hi => (hm i).trans (hc i hi))
    dsimp only at h
    simpa only [g, hm] using h
  have hvalues (i : Fin 24) :
      g i = ∑ k : Fin 8, w k *
        (FourT34QuaternionGram.doubleMinorForm (matchingMinorTable (fourPerm i).symm) k / 2) := by
    have h := t34HeightLift_eval (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7) H i
    rwa [← hrep, hm] at h
  have hgap := support_gap_eq α β U hU (-η) (fourPerm 2).symm
  have h₂ := hc 2 (by decide)
  simp only [matchingGap, neg_mul, Complex.neg_re, h₂] at hgap
  have hneg (x y : ℝ) : -x - -y = y - x := by ring
  simp only [hneg] at hgap
  rw [hgap]
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  rw [← Equiv.sum_comp e]
  change (∑ i : Fin 24, realSignedWeight U (fourPerm i).symm * g i) =
    ∑ k : Fin 8, w k * FourT34QuaternionGram.doubleMinorResponse U k / 2
  simp_rw [hvalues, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hinner :
      (∑ i : Fin 24, realSignedWeight U (fourPerm i).symm *
        (w k * (FourT34QuaternionGram.doubleMinorForm (matchingMinorTable (fourPerm i).symm) k / 2))) =
      w k / 2 *
        (∑ σ : FourPerm, realSignedWeight U σ *
          FourT34QuaternionGram.doubleMinorForm (matchingMinorTable σ) k) := by
    rw [← Equiv.sum_comp e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change _ = (w k / 2) *
      (realSignedWeight U (fourPerm i).symm *
        FourT34QuaternionGram.doubleMinorForm (matchingMinorTable (fourPerm i).symm) k)
    ring
  rw [hinner, t34_signed_minor_response U hU]
  ring

private theorem t34_unitary_response_nonneg (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    {p r a b c q d s : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hd : 0 < d) (hs : 0 ≤ s) (hM : 0 < b + c)
    (hroot : FourT34PolynomialCertificate.radialPolynomial p r a b c q d s = 0) :
    0 ≤ ∑ k : Fin 8, (![p, r, a, b, c, q, d, s] : Fin 8 → ℝ) k *
        FourT34QuaternionGram.doubleMinorResponse U k / 2 := by
  let w : Fin 8 → ℝ := ![p, r, a, b, c, q, d, s]
  obtain ⟨κ, inst, μ, O, hμ, _, hm⟩ := four_minor_mixture U hU
  letI : Fintype κ := inst
  let table (t : κ) := subsetMinorSq (Complex.ofRealHom.mapMatrix (O t).val)
  have htable : subsetMinorSq U = ∑ t, μ t • table t := by
    funext I J
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hm I J
  have hresponse : FourT34QuaternionGram.doubleMinorResponse U =
      ∑ t, μ t • FourT34QuaternionGram.doubleResponse (O t).val := by
    change doubleMinorMap (subsetMinorSq U) = _
    rw [htable, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [map_smul]
    exact congrArg (fun z : Fin 8 → ℝ => μ t • z)
      (FourT34QuaternionGram.doubleMinorResponse_of_real (O t))
  have hpart (t : κ) :
      0 ≤ ∑ k : Fin 8, w k * FourT34QuaternionGram.doubleResponse (O t).val k := by
    have hO := (Matrix.mem_orthogonalGroup_iff' _ ℝ).mp (O t).property
    obtain ⟨P, hP, hdet, heq⟩ := FourT34QuaternionGram.exists_specialOrthogonal_same_response
      (O t).val hO
    have h := fourT34_response_nonneg_of_radial_root P hP hdet
      hp hr ha hb hc hq hd hs hM hroot
    dsimp only at h
    rw [heq] at h
    simpa [w, Fin.sum_univ_succ, add_assoc] using h
  change 0 ≤ ∑ k : Fin 8, w k * FourT34QuaternionGram.doubleMinorResponse U k / 2
  have hpositive : 0 ≤ ∑ k : Fin 8, w k * FourT34QuaternionGram.doubleMinorResponse U k := by
    rw [hresponse]
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg (fun t _ => ?_)
    have ht : (∑ k : Fin 8, w k * (μ t * FourT34QuaternionGram.doubleResponse (O t).val k)) =
        μ t * ∑ k : Fin 8, w k * FourT34QuaternionGram.doubleResponse (O t).val k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [ht]
    exact mul_nonneg (hμ t) (hpart t)
  rw [← Finset.sum_div]
  exact div_nonneg hpositive (by norm_num)

/-- The radial root condition gives the original order-four T34 support
inequality, including coincident spectra and additional contacts. -/
theorem fourT34_support_of_radial_root (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hroot : H < (η * matchingProduct α β (fourPerm 11).symm).re →
      let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
      FourT34PolynomialCertificate.radialPolynomial (g 18) (g 16) (g 13)
        (g 8) (g 4) (g 14) (g 11) (g 7) = 0) :
    H ≤ (η * determinantValue α β U).re := by
  have hbound (hh : Holds α β U) : H ≤ (η * determinantValue α β U).re := by
    obtain ⟨σ, hσ⟩ := (holds_iff_directional α β U).mp hh (-η)
    obtain ⟨i, hi⟩ := fourPerm_surjective σ.symm
    have hei : (fourPerm i).symm = σ := by simp [hi]
    have hgi := hn i
    rw [hei] at hgi
    simp only [neg_mul, Complex.neg_re, neg_le_neg_iff] at hσ
    exact hgi.trans hσ
  by_cases h11 : (η * matchingProduct α β (fourPerm 11).symm).re = H
  · exact fourT34_support_of_contact_eleven α β η H hn hc h11 U hU
  have hd := lt_of_le_of_ne (hn 11) h11.symm
  by_cases hη : η = 0
  · have h₂ := hc 2 (by decide)
    simp only [hη, zero_mul, Complex.zero_re] at h₂ h11
    exact (h11 h₂).elim
  by_cases hα : Function.Injective α
  · by_cases hβ : Function.Injective β
    · by_cases hzero : ∃ i j, α i + β j = 0
      · obtain ⟨i, j, hij⟩ := hzero
        exact hbound (holds_four_of_opposite_entries α β U hU hij)
      · have hnz : ∀ i j, α i + β j ≠ 0 := fun i j hij => hzero ⟨i, j, hij⟩
        have hM := fourT34_donor_sum_pos_of_mixed α β η H hα hβ hnz hη hn hc hd
        have hg (i : Fin 24) :
            0 ≤ (η * matchingProduct α β (fourPerm i).symm).re - H := sub_nonneg.mpr (hn i)
        apply sub_nonneg.mp
        rw [fourT34_projected_gap_eq_response α β η H hc U hU]
        exact t34_unitary_response_nonneg U hU (hg 18) (hg 16) (hg 13) (hg 8)
          (hg 4) (hg 14) (sub_pos.mpr hd) (hg 7)
          (by simpa only [add_comm] using hM) (hroot hd)
    · exact hbound (holds_four_of_repeated_spectrum α β U hU (Or.inr hβ))
  · exact hbound (holds_four_of_repeated_spectrum α β U hU (Or.inl hα))

/-- The Hessian determinant factor is one way to supply the radial root. -/
theorem fourT34_support_of_radial_factor (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (hfactor :
      let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
      t34RadialFactorIdentity (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7)) :
    H ≤ (η * determinantValue α β U).re :=
  fourT34_support_of_radial_root α β η H hn hc U hU
    (fun hd => fourT34_radial_root_of_factor α β η H hn hc hd hfactor)

end

end MOC
