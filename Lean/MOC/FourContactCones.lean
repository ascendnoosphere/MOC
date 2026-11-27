import MOC.FourMatchingHessian
import MOC.FourT21ContactCone

/-! The contact lift and radial Hessian condition for T34. -/

namespace MOC

noncomputable section

/-- The six matching permutations of contact pattern T34. -/
def fourT34ContactIndices : Finset (Fin 24) := {2, 3, 5, 9, 10, 12}

set_option maxHeartbeats 2000000 in
/-- The eight coefficients of the simplicial cone of paper case T34 are
individual matching gaps. The lift includes the common contact height. -/
theorem fourT34_height_lift_of_contacts (m : Fin 14 → ℝ) (H : ℝ)
    (hc : ∀ i ∈ fourT34ContactIndices, fourMatchingEvaluation m i = H) :
    let g := fun i => fourMatchingEvaluation m i - H
    m = t34HeightLift (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7) H := by
  have h2 := hc 2 (by decide)
  have h3 := hc 3 (by decide)
  have h5 := hc 5 (by decide)
  have h9 := hc 9 (by decide)
  have h10 := hc 10 (by decide)
  have h12 := hc 12 (by decide)
  simp [fourMatchingEvaluation] at h2 h3 h5 h9 h10 h12
  dsimp only
  funext i
  fin_cases i <;> simp [t34HeightLift, fourMatchingEvaluation] <;>
    linarith only [h2, h3, h5, h9, h10, h12]

/-- On the positive mixed branch, the T34 radial coefficient is nonzero
under the actual contact and spectral gap inequalities. -/
theorem fourT34_radialQ_ne_zero_of_contacts (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (hd : H < (η * matchingProduct α β (fourPerm 11).symm).re) :
    let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
    t34RadialQ (g 13) (g 8) (g 4) (g 11) (g 16) (g 7) ≠ 0 := by
  let m (i : Fin 14) := (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct α β (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part α β η i
  have hrep := fourT34_height_lift_of_contacts m H (fun i hi => (hm i).trans (hc i hi))
  dsimp only at hrep ⊢
  simp only [hm] at hrep
  exact t34_radialQ_ne_zero_of_spectral α β η
    (sub_nonneg.mpr (hn 18)) (sub_nonneg.mpr (hn 16)) (sub_nonneg.mpr (hn 8))
    (sub_nonneg.mpr (hn 4)) (sub_nonneg.mpr (hn 14)) (sub_pos.mpr hd) (sub_nonneg.mpr (hn 7))
    (fun i => by rw [← hrep, hm])

/-- The radial height determined by the T34 cubic also has singular matching
Hessian. The arguments of both polynomials are the actual matching gaps. -/
theorem fourT34_hessian_at_radial_height_eq_zero (α β : Fin 4 → ℂ) (η : ℂ) (H : ℝ)
    (hn : ∀ i, H ≤ (η * matchingProduct α β (fourPerm i).symm).re)
    (hc : ∀ i ∈ fourT34ContactIndices, (η * matchingProduct α β (fourPerm i).symm).re = H)
    (hd : H < (η * matchingProduct α β (fourPerm 11).symm).re) :
    let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
    let Q := t34RadialQ (g 13) (g 8) (g 4) (g 11) (g 16) (g 7)
    let C := t34RadialC (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7)
    (fourMatchingHessian (t34HeightLift (g 18) (g 16) (g 13) (g 8)
      (g 4) (g 14) (g 11) (g 7) (-C / Q))).det = 0 := by
  let g := fun i => (η * matchingProduct α β (fourPerm i).symm).re - H
  let Q := t34RadialQ (g 13) (g 8) (g 4) (g 11) (g 16) (g 7)
  let C := t34RadialC (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7)
  let L := t34HeightLift (g 18) (g 16) (g 13) (g 8) (g 4) (g 14) (g 11) (g 7)
  change (fourMatchingHessian (L (-C / Q))).det = 0
  let m (i : Fin 14) := (η * fourNoncrossingCoordinates (fourSpectralPoints α β) i).re
  have hm (i : Fin 24) : fourMatchingEvaluation m i =
      (η * matchingProduct α β (fourPerm i).symm).re :=
    fourMatchingEvaluation_spectral_real_part α β η i
  have hrep : m = L H := by
    have h := fourT34_height_lift_of_contacts m H (fun i hi => (hm i).trans (hc i hi))
    dsimp only at h
    simpa only [hm, L, g] using h
  have hQ : Q ≠ 0 := fourT34_radialQ_ne_zero_of_contacts α β η H hn hc hd
  have hC : C + H * Q = 0 := by
    have hzero : fourMatchingCubic m = 0 := fourMatchingCubic_of_spectral_real_part α β η
    rw [hrep] at hzero
    simpa only [L, t34_height_cubic, C, Q] using hzero
  have hH : H = -C / Q := (eq_div_iff hQ).mpr (by linarith only [hC])
  rw [← hH, ← hrep]
  exact fourMatchingHessian_det_spectral_real_part_eq_zero α β η

end

end MOC
