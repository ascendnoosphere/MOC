import MOC.SpectralZeroPadding
import MOC.Small

/-! Append opposite values to the two spectral lists. The multiplicity at the
chosen value determines when the enlarged pair allows every unitary. -/

open Matrix

namespace MOC

private theorem shifted_support_count {d : ℕ} (v : Fin d → ℂ) (c : ℂ) :
    (spectralSupport (fun i => v i - c)).card +
      (Finset.univ.filter (fun i => v i = c)).card = d := by
  simpa [spectralSupport, sub_eq_zero] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ)
      (fun i => v i - c ≠ 0))

/-- Append m copies of c and -c. Count the entries equal to the two values
before padding. If the two counts plus m plus two reach d, every unitary of
order d + m satisfies the determinant inclusion. -/
theorem holds_value_padding_of_count {d : ℕ} (a b : Fin d → ℂ) (c : ℂ) (m : ℕ)
    (h : d ≤ (Finset.univ.filter (fun i => a i = c)).card +
      (Finset.univ.filter (fun i => b i = -c)).card + m + 2)
    (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithValue a c m) (padSpectrumWithValue b (-c) m) U := by
  classical
  let x := fun i => a i - c
  let y := fun i => b i - (-c)
  have hx := shifted_support_count a c
  have hy := shifted_support_count b (-c)
  have hp := spectralSupport_pad_card_le x m
  have hq := spectralSupport_pad_card_le y m
  have hsum : (spectralSupport (padSpectrumWithZeros x m)).card +
      (spectralSupport (padSpectrumWithZeros y m)).card ≤ d + m + 2 := by
    change (spectralSupport x).card + _ = d at hx
    change (spectralSupport y).card + _ = d at hy
    omega
  have hz : Holds (padSpectrumWithZeros x m) (padSpectrumWithZeros y m) U := by
    apply holds_of_shifted_support_le_card_add_two _ _ U hU 0
    simpa only [add_zero, sub_zero, Fintype.card_fin] using hsum
  have ha : (fun i => padSpectrumWithZeros x m i + c) = padSpectrumWithValue a c m := by
    funext i
    by_cases hi : i.val < d <;> simp [x, padSpectrumWithZeros, padSpectrumWithValue, hi]
  have hb : (fun i => padSpectrumWithZeros y m i - c) = padSpectrumWithValue b (-c) m := by
    funext i
    by_cases hi : i.val < d <;> simp [y, padSpectrumWithZeros, padSpectrumWithValue, hi]
  rw [← ha, ← hb]
  exact (holds_shift_iff _ _ hU c).mpr hz

/-- If at least d minus two opposite pairs are appended, the original
d entries on each side can have arbitrary complex values. -/
theorem holds_value_padding_of_order_bound {d : ℕ} (a b : Fin d → ℂ) (c : ℂ) (m : ℕ)
    (h : d ≤ m + 2) (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ)
    (hU : IsUnitary U) :
    Holds (padSpectrumWithValue a c m) (padSpectrumWithValue b (-c) m) U :=
  holds_value_padding_of_count a b c m (by omega) U hU

/-- A case that holds for every unitary at order d extends to every larger
order when the two multiplicities at c and -c total at least d minus three. -/
theorem holds_all_value_paddings_of_count {d : ℕ} (a b : Fin d → ℂ) (c : ℂ)
    (h : d ≤ (Finset.univ.filter (fun i => a i = c)).card +
      (Finset.univ.filter (fun i => b i = -c)).card + 3)
    (hbase : ∀ V : Matrix (Fin d) (Fin d) ℂ, IsUnitary V → Holds a b V)
    (m : ℕ) (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithValue a c m) (padSpectrumWithValue b (-c) m) U := by
  cases m with
  | zero =>
    have he (v : Fin d → ℂ) (s : ℂ) : padSpectrumWithValue v s 0 = v := by
      funext i
      exact dif_pos i.isLt
    simpa only [he] using hbase U hU
  | succ m =>
    exact holds_value_padding_of_count a b c (m+1) (by omega) U hU

/-- An order-four all-unitary result extends to every larger order if the
first list contains c or the second list contains -c. -/
theorem holds_all_marked_paddings_four (a b : Fin 4 → ℂ) (c : ℂ)
    (hc : (∃ i, a i = c) ∨ (∃ i, b i = -c))
    (hbase : ∀ V : Matrix (Fin 4) (Fin 4) ℂ, IsUnitary V → Holds a b V)
    (m : ℕ) (U : Matrix (Fin (4 + m)) (Fin (4 + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithValue a c m) (padSpectrumWithValue b (-c) m) U := by
  refine holds_all_value_paddings_of_count a b c ?_ hbase m U hU
  rcases hc with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hp : 0 < (Finset.univ.filter (fun k => a k = c)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    omega
  · have hp : 0 < (Finset.univ.filter (fun k => b k = -c)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    omega

/-- Choose up to three entries freely on each side. Fill the remaining
positions with c on the first side and -c on the second side. -/
theorem holds_all_paddings_of_order_le_three {d : ℕ} (hd : d ≤ 3)
    (a b : Fin d → ℂ) (c : ℂ) (m : ℕ)
    (U : Matrix (Fin (d + m)) (Fin (d + m)) ℂ) (hU : IsUnitary U) :
    Holds (padSpectrumWithValue a c m) (padSpectrumWithValue b (-c) m) U :=
  holds_all_value_paddings_of_count a b c (by omega)
    (fun V hV => conjecture_le_three hd a b V hV) m U hU

end MOC
