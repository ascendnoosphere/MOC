import MOC.HomotheticFour
import MOC.MarkedPadding

/-! Add opposite values to the two homothetic order-four spectra. -/

open Matrix

namespace MOC.HomotheticFour

/-- Append m copies of c and -c to the two quadruples. Only the case
m = 1 needs a mark. Then c must occur on the first side or -c on the second. -/
theorem holds_with_padded_values (x y t c : ℂ) (m : ℕ)
    (hmark : m = 1 → (∃ i, spectrum x y i = c) ∨ (∃ i, t * spectrum x y i = -c))
    (U : Matrix (Fin (4 + m)) (Fin (4 + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithValue (spectrum x y) c m)
      (padSpectrumWithValue (fun i => t * spectrum x y i) (-c) m) U := by
  rcases m with _ | m
  · have he (v : Fin 4 → ℂ) (s : ℂ) : padSpectrumWithValue v s 0 = v := by
      funext i
      exact dif_pos i.isLt
    simpa only [he] using holds_homothetic x y t U hU
  · cases m with
    | zero =>
      exact holds_all_marked_paddings_four _ _ c (hmark rfl) (holds_homothetic x y t) 1 U hU
    | succ k =>
      exact holds_value_padding_of_order_bound _ _ _ _ (by omega) U hU

end MOC.HomotheticFour
