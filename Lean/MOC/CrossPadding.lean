import MOC.FiveCross
import MOC.SpectralZeroPadding

/-! The order-five cross and the two opposite scalar centers in larger orders. -/

open Matrix

namespace MOC.FiveCross

/-- Repeat the two opposite centers any number of times.
The relative unitary is arbitrary at the enlarged order. -/
theorem holds_padded_affine_dilation (m : ℕ) (s c : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (U : Matrix (Fin (5 + m)) (Fin (5 + m)) ℂ) (hU : IsUnitary U) :
    Holds (fun i => padSpectrumWithZeros (fun j => s * spectrum j) m i + c)
      (fun i => padSpectrumWithZeros (fun j => s * ((t : ℂ) * spectrum j)) m i - c) U := by
  apply (holds_shift_iff _ _ hU c).mpr
  have hz : spectrum 0 = 0 := rfl
  apply holds_all_zero_paddings_five _ _ 0 0 (by simp [hz]) (by simp [hz]) _ m U hU
  intro V hV
  simpa only [add_zero, sub_zero] using holds_affine_dilation s 0 t ht V hV

end MOC.FiveCross
