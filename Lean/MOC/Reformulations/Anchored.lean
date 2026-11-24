import MOC.Claim
import MOC.Geometry
import MOC.FullSupportReduction

/-! One can fix two spectral coordinates without weakening the conjecture.
The reduction also discards zero unitary entries, vanishing spectral sums, and
coincident matching values. The normalization itself leaves the unitary fixed. -/

open Matrix

namespace MOC.Reformulations

private theorem regular_anchors
    {n : ℕ} (i : Fin n) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitary U) (hnz : ∀ j k, a j + b k ≠ 0)
    (hinj : Function.Injective (matchingProduct a b)) :
    ∃ x y : Fin n → ℂ, x i = 0 ∧ y i = 1 ∧
      (∀ j k, x j + y k ≠ 0) ∧ Function.Injective (matchingProduct x y) ∧
      (Holds x y U ↔ Holds a b U) := by
  let a' : Fin n → ℂ := fun j => a j + -a i
  let b' : Fin n → ℂ := fun j => b j - -a i
  let c : ℂ := (a i + b i)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (hnz i i)
  have hs (j k : Fin n) : a' j + b' k = a j + b k := by
    simp only [a', b', sub_neg_eq_add]
    ring
  let x : Fin n → ℂ := fun j => c * a' j
  let y : Fin n → ℂ := fun j => c * b' j
  have hp (σ : Equiv.Perm (Fin n)) :
      matchingProduct x y σ = c ^ Fintype.card (Fin n) * matchingProduct a b σ := by
    change matchingProduct (fun j => c * a' j) (fun j => c * b' j) σ = _
    rw [matchingProduct_scale]
    rw [show matchingProduct a' b' σ = matchingProduct a b σ from
      matchingProduct_shift a b (-a i) σ]
  refine ⟨x, y, by simp [x, a'], ?_, ?_, ?_, ?_⟩
  · simpa [y, c, b', sub_neg_eq_add, add_comm (b i) (a i)] using
      inv_mul_cancel₀ (hnz i i)
  · intro j k
    change c * a' j + c * b' k ≠ 0
    rw [← mul_add, hs]
    exact mul_ne_zero hc (hnz j k)
  · intro σ τ he
    rw [hp, hp] at he
    exact hinj (mul_left_cancel₀ (pow_ne_zero _ hc) he)
  · change Holds (fun j => c * a' j) (fun j => c * b' j) U ↔ Holds a b U
    exact (hull_common_factor_iff (pow_ne_zero _ hc)
      (determinantValue_scale a' b' U c) (matchingProduct_scale a' b' c)).trans
      (holds_shift_iff a b hU (-a i))

/-- One anchored coordinate on each side suffices in any nonempty order,
even if the statement is only proved for regular spectra and full-support
relative unitaries. -/
theorem conjecture_iff_anchored_regular {n : ℕ} (i : Fin n) :
    Conjecture (Fin n) ↔
      ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
        IsUnitary U → (∀ j k, U j k ≠ 0) → a i = 0 → b i = 1 →
        (∀ j k, a j + b k ≠ 0) → Function.Injective (matchingProduct a b) →
        Holds a b U := by
  constructor
  · intro h a b U hU _ _ _ _ _
    exact h a b U hU
  · intro h
    apply conjecture_iff_regular_spectra_full_support.mpr
    intro a b U hU hnz hinj hfull
    obtain ⟨x, y, hx, hy, hnz', hinj', hiff⟩ := regular_anchors i a b U hU hnz hinj
    exact hiff.mp (h x y U hU hfull hx hy hnz' hinj')

/-- Full MOC is equivalent to its restriction to the anchored regular slice
in orders at least four. Refuting even one instance on the slice refutes MOC. -/
theorem moc_iff_anchored_regular :
    MOCIsTrue ↔ ∀ (n : ℕ) (hn : 4 ≤ n),
      let i : Fin n := ⟨0, by omega⟩
      ∀ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
        IsUnitary U → (∀ j k, U j k ≠ 0) → a i = 0 → b i = 1 →
        (∀ j k, a j + b k ≠ 0) → Function.Injective (matchingProduct a b) →
        Holds a b U := by
  rw [mocIsTrue_iff_from_four]
  exact forall_congr' fun n => forall_congr' fun hn =>
    conjecture_iff_anchored_regular ⟨0, by omega⟩

/-- A least-order counterexample can be found on the anchored regular slice. -/
theorem exists_anchored_regular_failure (h : ¬ MOCIsTrue) :
    ∃ (n : ℕ) (hn : 4 ≤ n), (∀ m < n, Conjecture (Fin m)) ∧
      let i : Fin n := ⟨0, by omega⟩
      ∃ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
        IsUnitary U ∧ (∀ j k, U j k ≠ 0) ∧ a i = 0 ∧ b i = 1 ∧
        (∀ j k, a j + b k ≠ 0) ∧ Function.Injective (matchingProduct a b) ∧
        ¬ Holds a b U := by
  obtain ⟨n, hn, hfail, hbelow⟩ := exists_least_bad_order h
  refine ⟨n, hn, hbelow, ?_⟩
  rw [conjecture_iff_anchored_regular ⟨0, by omega⟩] at hfail
  push_neg at hfail
  exact hfail

end MOC.Reformulations
