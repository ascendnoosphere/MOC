import MOC.IntegerRayCut

/-! Compact checks for the order-four ray census. A support mask records
the positive coordinates of one ray on the inequalities already imposed. -/

namespace MOC.RayCoefficients

/-- A skipped crossing needs one inclusion between three support masks. -/
def maskCrossing {m n : ℕ} (old : Fin m → Row) (next : Fin n → Row)
    (s : Finset (Fin 24)) (j : Fin 24) (mask : Fin m → ℕ) (p k : Fin m) :
    Crossing m n → Prop
  | .skip q => q ≠ p ∧ q ≠ k ∧ (mask q &&& (mask p ||| mask k)) = mask q
  | .keep l c => RayCutPlan.CrossingValid old next s j p k (.keep l c)

instance {m n : ℕ} (old : Fin m → Row) (next : Fin n → Row)
    (s : Finset (Fin 24)) (j : Fin 24) (mask : Fin m → ℕ) (p k : Fin m) (c : Crossing m n) :
    Decidable (maskCrossing old next s j mask p k c) := by
  cases c <;> unfold maskCrossing <;> infer_instance

theorem validateRayMasks {m n : ℕ} {old : Fin m → Row} {next : Fin n → Row}
    {s : Finset (Fin 24)} {j : Fin 24} (plan : RayCutPlan m n) (mask : Fin m → ℕ)
    (hsign : ∀ p i, i ∈ s → zero (old p i) = true ∨ positive (old p i) = true)
    (hm : ∀ p i, (mask p).testBit i.val = (decide (i ∈ s) && positive (old p i)))
    (hsep : ∀ p k, p ≠ k → ∃ i : Fin 24,
      (mask p).testBit i.val = true ∧ (mask k).testBit i.val = false)
    (hcross : ∀ p k, positive (old p j) = true → negative (old k j) = true →
      maskCrossing old next s j mask p k (plan.crossing p k)) :
    (∀ p k, p ≠ k → ∃ i ∈ s, positive (old p i) = true ∧ zero (old k i) = true) ∧
    (∀ p k, positive (old p j) = true → negative (old k j) = true →
      RayCutPlan.CrossingValid old next s j p k (plan.crossing p k)) := by
  have hz (p i) (hi : i ∈ s) (h : (mask p).testBit i.val = false) : zero (old p i) = true := by
    rcases hsign p i hi with he | he
    · exact he
    · simp [hm, hi, he] at h
  have hb (p i) (h : zero (old p i) = true) : (mask p).testBit i.val = false := by
    have he : positive (old p i) = false := by
      cases hp : positive (old p i) with
      | false => rfl
      | true =>
        exact False.elim ((eval_pos_of_check zero_lt_one hp).ne' (eval_zero_of_check 1 h))
    simp only [hm, he, Bool.and_false]
  constructor
  · intro p k h
    obtain ⟨i, hp, hk⟩ := hsep p k h
    have hi : i ∈ s ∧ positive (old p i) = true := by
      simpa only [hm, Bool.and_eq_true, decide_eq_true_eq] using hp
    exact ⟨i, hi.1, hi.2, hz k i hi.1 hk⟩
  · intro p k hp hk
    have h := hcross p k hp hk
    cases he : plan.crossing p k with
    | keep l c => simpa only [he, maskCrossing] using h
    | skip q =>
      rw [he] at h
      obtain ⟨hqp, hqk, heq⟩ := h
      refine ⟨hqp, hqk, ?_⟩
      intro i hi hpz hkz
      apply hz q i hi
      have heBit := congrArg (fun a : ℕ => a.testBit i.val) heq
      simpa only [Nat.testBit_and, Nat.testBit_or, hb p i hpz, hb k i hkz,
        Bool.false_or, Bool.and_false] using heBit.symm

end MOC.RayCoefficients
