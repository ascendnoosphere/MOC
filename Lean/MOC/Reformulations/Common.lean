import MOC.Claim

namespace MOC.Reformulations

/-- The atlas's common labelled finite layer. The mode index lets the evaluator
distinguish repeated labels. This does not assert the native geometric or
operator statement from which the samples were chosen. -/
def LabelledSpectralForm (Sample : ℕ → Type) : Prop :=
  ∀ (n : ℕ) (s t : Sample n) (f g : Sample n → Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U → Holds (f s) (g t) U

/-- Every labelled lift with samples in every order is exact. The reverse
direction evaluates a fixed sample by functions that only use the mode index. -/
theorem labelledSpectralForm_iff (Sample : ℕ → Type) (sample : ∀ n, Sample n) :
    LabelledSpectralForm Sample ↔ MOCIsTrue := by
  constructor
  · intro h n a b U hU
    exact h n (sample n) (sample n) (fun _ => a) (fun _ => b) U hU
  · intro h n s t f g U hU
    exact h n (f s) (g t) U hU

/-- With no assumption on sample availability, only the restricted direction
is automatic. In particular a failure of the restriction refutes MOC. -/
theorem labelledSpectralForm_of_moc (Sample : ℕ → Type) (h : MOCIsTrue) :
    LabelledSpectralForm Sample := by
  intro n s t f g U hU
  exact h n (f s) (g t) U hU

theorem not_moc_of_not_labelledSpectralForm (Sample : ℕ → Type)
    (h : ¬ LabelledSpectralForm Sample) : ¬ MOCIsTrue :=
  fun hMOC => h (labelledSpectralForm_of_moc Sample hMOC)

end MOC.Reformulations
