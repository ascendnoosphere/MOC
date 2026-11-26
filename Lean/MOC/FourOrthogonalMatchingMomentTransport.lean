import MOC.FourOrthogonalCorrectedMoment
import MOC.FourMatchingIndicatorBasis

/-! Transport of the corrected fourteen-column moment to the real matching jet. -/

open Matrix BigOperators

namespace MOC

/-- The explicit alternating correction gives a positive matching jet
moment for every order-four real orthogonal mixer. -/
theorem fourOrthogonalMatchingMoment_exists_correction (O : Matrix.orthogonalGroup (Fin 4) ℝ) :
    ∃ t : ℝ, (realMatchingMoment (fun p =>
      realSignedWeight (Complex.ofRealHom.mapMatrix O.val) (fourPerm p).symm +
        t * matchingSign p)).PosSemidef := by
  have hO : O.valᵀ * O.val = 1 := (Matrix.mem_orthogonalGroup_iff' _ ℝ).mp O.property
  let t := O.val.det * fourMatchingCorrectionCandidate O.val
  refine ⟨t, ?_⟩
  have hweight : (fun p => realSignedWeight (Complex.ofRealHom.mapMatrix O.val) (fourPerm p).symm +
      t * matchingSign p) = (fun p => fourCorrectedIndicatorWeight O.val (fourPerm p)) := by
    funext p
    rw [realSignedWeight_ofReal_orthogonal O (fourPerm p)]
    rfl
  rw [hweight]
  exact realMatchingMoment_posSemidef_of_indicator_basis _
    (fourCorrectedIndicatorMoment_posSemidef O.val hO)

end MOC
