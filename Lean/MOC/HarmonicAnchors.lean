import MOC.FiveSharedAnchors
import MOC.ProjectiveTransport
import MOC.TwoFreeEntries
import MOC.SpectralZeroPadding

/-! A fractional-linear image of the four shared marks admits two free entries. -/

open BigOperators Matrix

namespace MOC.FiveSharedAnchors

noncomputable section

/-- The four prescribed signed values are f(0), f(2), f(3) and f(6).
The entry at index four is free. -/
def mappedLeft (f : ℂ → ℂ) (x : ℂ) : Fin 5 → ℂ :=
  Function.update (fun i => f (firstMarks i : ℂ)) 4 x

/-- The partner has the negatives of the four prescribed signed values. -/
def mappedRight (f : ℂ → ℂ) (y : ℂ) : Fin 5 → ℂ :=
  Function.update (fun i => -f (firstMarks i : ℂ)) 4 y

private theorem anchor_law (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    ∃ w : Label → ℝ, (∀ p, 0 ≤ w p) ∧ ∑ p, w p = 1 ∧
      ∀ x y, weightedMatchingValue (left x) (right y) w = determinantValue (left x) (right y) U := by
  classical
  obtain ⟨σ, w, hw, hs, he⟩ := exists_common_law U hU
  let W (p : Label) := ∑ j ∈ Finset.univ.filter (fun j => σ j = p), w j
  refine ⟨W, fun _ => Finset.sum_nonneg fun j _ => hw j, ?_, ?_⟩
  · simpa only [W, Finset.sum_fiberwise] using hs
  · intro x y
    unfold weightedMatchingValue
    rw [← he x y, ← Finset.sum_fiberwise Finset.univ σ
      (fun j => (w j : ℂ) * matchingProduct (left x) (right y) (σ j))]
    apply Finset.sum_congr rfl
    intro p _
    simp only [W, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]

private theorem marks_neg (i : Fin 5) : (secondMarks i : ℂ) = -(firstMarks i : ℂ) := by
  fin_cases i <;> norm_num [firstMarks, secondMarks]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 18000 in
/-- Every unitary admits one law for the whole projective family of four
shared harmonic marks. The remaining entries can take all complex values. -/
theorem exists_harmonic_law (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    ∃ w : Label → ℝ, (∀ p, 0 ≤ w p) ∧ ∑ p, w p = 1 ∧
      ∀ α β γ δ : ℂ, α*δ-β*γ ≠ 0 → (∀ i, γ*(firstMarks i : ℂ)+δ ≠ 0) →
        ∀ x y : ℂ, let f := fractionalMap α β γ δ
        weightedMatchingValue (mappedLeft f x) (mappedRight f y) w =
          determinantValue (mappedLeft f x) (mappedRight f y) U := by
  classical
  obtain ⟨w, hw, hs, he⟩ := anchor_law U hU
  refine ⟨w, hw, hs, ?_⟩
  intro α β γ δ hd hmark
  let f := fractionalMap α β γ δ
  let a (i : Fin 5) := (firstMarks i : ℂ)
  have corners (r s : Fin 5) :
      weightedMatchingValue (mappedLeft f (f (a r))) (mappedRight f (-f (a s))) w =
        determinantValue (mappedLeft f (f (a r))) (mappedRight f (-f (a s))) U := by
    have hl (i : Fin 5) : γ*left (a r) i+δ ≠ 0 := by
      by_cases hi : i = 4
      · subst i
        simpa [left, a] using hmark r
      · simpa [left, hi] using hmark i
    have hr (i : Fin 5) : γ*(-right (-a s) i)+δ ≠ 0 := by
      by_cases hi : i = 4
      · subst i
        simpa [right, a] using hmark s
      · simpa only [right, Function.update_of_ne hi, marks_neg, neg_neg] using hmark i
    have el : (f ∘ left (a r)) = mappedLeft f (f (a r)) := by
      funext i
      by_cases hi : i = 4
      · subst i
        simp [left, mappedLeft]
      · simp [left, mappedLeft, hi]
    have er : (fun j => -f (-right (-a s) j)) = mappedRight f (-f (a s)) := by
      funext i
      by_cases hi : i = 4
      · subst i
        simp [right, mappedRight]
      · simp [right, mappedRight, hi, marks_neg]
    have h := weight_agreement_fractional _ _ U hU w α β γ δ hd hl hr (he _ _)
    change weightedMatchingValue (f ∘ left (a r)) (fun j => -f (-right (-a s) j)) w =
      determinantValue (f ∘ left (a r)) (fun j => -f (-right (-a s) j)) U at h
    rwa [el, er] at h
  have hf : f (a 0) ≠ f (a 1) := by
    intro h
    have heq := fractionalMap_injOn α β γ δ hd (hmark 0) (hmark 1) h
    norm_num [firstMarks] at heq
  have hn : -f (a 0) ≠ -f (a 1) := by
    intro h
    apply hf
    simpa only [neg_neg] using congrArg (fun t : ℂ => -t) h
  apply (weightedMatchingValue_eq_iff_four_corners
    (fun i => f (firstMarks i : ℂ)) (fun i => -f (firstMarks i : ℂ))
    U hU w 4 4 hf hn).mpr
  intro x hx y hy
  rcases Set.mem_insert_iff.mp hx with h | h <;> rcases Set.mem_insert_iff.mp hy with g | g
  · simpa only [h, g] using corners 0 0
  · simpa only [h, Set.mem_singleton_iff.mp g] using corners 0 1
  · simpa only [Set.mem_singleton_iff.mp h, g] using corners 1 0
  · simpa only [Set.mem_singleton_iff.mp h, Set.mem_singleton_iff.mp g] using corners 1 1

/-- Four harmonic shared signed values suffice in order five for every
relative unitary and every pair of remaining eigenvalues. -/
theorem holds_harmonic (α β γ δ : ℂ) (hd : α*δ-β*γ ≠ 0)
    (hm : ∀ i, γ*(firstMarks i : ℂ)+δ ≠ 0) (x y : ℂ)
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    Holds (mappedLeft (fractionalMap α β γ δ) x) (mappedRight (fractionalMap α β γ δ) y) U := by
  obtain ⟨w, hw, hs, he⟩ := exists_harmonic_law U hU
  exact holds_of_weights w hw hs (he α β γ δ hd hm x y)

/-- Repeat any one of the four shared signed values. Every unitary at the
larger order satisfies the inclusion for all choices of the two free entries. -/
theorem holds_padded_harmonic (α β γ δ : ℂ) (hd : α*δ-β*γ ≠ 0)
    (hm : ∀ i, γ*(firstMarks i : ℂ)+δ ≠ 0) (x y : ℂ)
    (r : Fin 5) (hr : r ≠ 4) (m : ℕ)
    (U : Matrix (Fin (5+m)) (Fin (5+m)) ℂ) (hU : IsUnitary U) :
    let f := fractionalMap α β γ δ
    let v := f (firstMarks r : ℂ)
    Holds (padSpectrumWithValue (mappedLeft f x) v m)
      (padSpectrumWithValue (mappedRight f y) (-v) m) U := by
  apply holds_all_shared_value_paddings_five _ _ _ r r _ _
    (holds_harmonic α β γ δ hd hm x y) m U hU
  · simp [mappedLeft, hr]
  · simp [mappedRight, hr]

end

end MOC.FiveSharedAnchors
