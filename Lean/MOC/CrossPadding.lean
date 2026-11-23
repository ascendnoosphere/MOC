import MOC.FiveCross
import MOC.RankTwoOverlap

/-! Scalar padding of the five-point cross allows every relative unitary.
The rank bound applies as soon as the dimension reaches six. -/

open Matrix

namespace MOC.FiveCross

/-- Append `m` zero eigenvalues to the five-point cross. -/
def paddedSpectrum (m : ℕ) (i : Fin (m + 5)) : ℂ :=
  if h : i.val < 5 then spectrum ⟨i.val, h⟩ else 0

private theorem zero_label : spectrum 0 = 0 := rfl

private theorem padded_support_le (m : ℕ) (s : ℂ) :
    (spectralSupport (fun i => s * paddedSpectrum m i)).card ≤ 4 := by
  classical
  let e : Fin 5 ↪ Fin (m + 5) :=
    ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.ext (congrArg Fin.val h)⟩
  have sub : spectralSupport (fun i => s * paddedSpectrum m i) ⊆
      (Finset.univ.erase (0 : Fin 5)).map e := by
    intro i hi
    have hn : s * paddedSpectrum m i ≠ 0 := (Finset.mem_filter.mp hi).2
    by_cases h : i.val < 5
    · let j : Fin 5 := ⟨i.val, h⟩
      have hij : paddedSpectrum m i = spectrum j := dif_pos h
      have hj : j ≠ 0 := by
        intro hzero
        exact hn (by rw [hij, hzero, zero_label, mul_zero])
      exact Finset.mem_map.mpr ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩, Fin.ext rfl⟩
    · exact (hn (by simp [paddedSpectrum, h])).elim
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ = 4 := by rw [Finset.card_map]; decide

private theorem padded_zero (i : Fin 5) : paddedSpectrum 0 i = spectrum i := dif_pos i.isLt

/-- At every order at least five, repeat the two opposite centers any
number of times. All relative unitary matrices are permitted. -/
theorem holds_padded_affine_dilation (m : ℕ) (s c : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (U : Matrix (Fin (m + 5)) (Fin (m + 5)) ℂ) (hU : IsUnitary U) :
    Holds (fun i => s * paddedSpectrum m i + c)
      (fun i => s * ((t : ℂ) * paddedSpectrum m i) - c) U := by
  cases m with
  | zero =>
    simpa only [padded_zero] using holds_affine_dilation s c t ht U hU
  | succ m =>
    apply (holds_shift_iff _ _ hU c).mpr
    apply holds_of_shifted_support_le_card_add_two _ _ U hU 0
    simp only [add_zero, sub_zero, ← mul_assoc, Fintype.card_fin]
    have ha := padded_support_le (m + 1) s
    have hb := padded_support_le (m + 1) (s * (t : ℂ))
    omega

end MOC.FiveCross
