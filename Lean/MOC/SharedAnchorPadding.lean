import MOC.FiveSharedAnchors
import MOC.Support
import MOC.Geometry
import MOC.SpectralZeroPadding

/-! Add opposite scalar centers to the two spectra with harmonic shared marks. -/

open Matrix

namespace MOC.FiveSharedAnchors

/-- Append zeros, then apply a common complex scale and opposite translations.
All unitary matrices of the enlarged order are allowed. -/
theorem holds_padded_affine (x y s c : ℂ) (m : ℕ)
    (U : Matrix (Fin (5 + m)) (Fin (5 + m)) ℂ) (hU : IsUnitary U) :
    Holds (fun i => s * padSpectrumWithZeros (left x) m i + c)
      (fun i => s * padSpectrumWithZeros (right y) m i - c) U := by
  apply (holds_shift_iff _ _ hU c).mpr
  apply hull_of_common_factor (determinantValue_scale _ _ U s) (matchingProduct_scale _ _ s)
  apply holds_all_zero_paddings_five _ _ 0 0 _ _ (holds x y) m U hU
  · simp [left, firstMarks]
  · simp [right, secondMarks]

end MOC.FiveSharedAnchors
