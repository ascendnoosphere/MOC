import MOC.ReducingCommutant
import MOC.SupportedCompressionReduction

/-! The least-order argument rules out every regular normal pole on either
side, alongside the scalar common commutant reduction. -/

open Matrix

namespace MOC

/-- A smaller-order proof excludes a normal principal compression at any
regular reciprocal pole of a failure. The same exclusion holds after
swapping the summands. -/
theorem nonnormal_poles_of_not_holds {n : ℕ} (hSmall : Conjecture (Fin n))
    (a b : Fin (n + 1) → ℂ) (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : IsUnitary U)
    (hnz : ∀ i j, a i + b j ≠ 0) (hnot : ¬ Holds a b U) :
    (∀ p, (∀ k ≠ p, a k - a p ≠ 0) → ¬ IsStarNormal (poleCompression a b U p)) ∧
    (∀ p, (∀ k ≠ p, b k - b p ≠ 0) → ¬ IsStarNormal (poleCompression b a Uᴴ p)) := by
  have hU' : IsUnitary Uᴴ := ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hU.2,
    by simpa only [Matrix.conjTranspose_conjTranspose] using hU.1⟩
  constructor
  · intro p hp hnormal
    exact hnot (holds_of_normal_poleCompression hSmall a b U hU p hp
      (fun j => by simpa only [add_comm] using hnz p j) hnormal)
  · intro p hp hnormal
    apply hnot
    apply (holds_swap_iff a b hU).mp
    exact holds_of_normal_poleCompression hSmall b a Uᴴ hU' p hp (fun j => hnz j p) hnormal

/-- The unrestricted conjecture is equivalent to the case of regular
matching products, a scalar common commutant, and nonnormal compressions
at every regular pole of either spectrum. -/
theorem mocIsTrue_iff_regular_scalar_nonnormal_poles :
    MOCIsTrue ↔ ∀ n : ℕ, 3 ≤ n → ∀ (a b : Fin (n + 1) → ℂ)
      (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), IsUnitary U →
      (∀ i j, a i + b j ≠ 0) → Function.Injective (matchingProduct a b) →
      (∀ Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Commute (diagonal a) Y →
        Commute (U * diagonal b * Uᴴ) Y →
        ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) →
      (∀ p, (∀ k ≠ p, a k - a p ≠ 0) → ¬ IsStarNormal (poleCompression a b U p)) →
      (∀ p, (∀ k ≠ p, b k - b p ≠ 0) → ¬ IsStarNormal (poleCompression b a Uᴴ p)) →
      Holds a b U := by
  constructor
  · intro h n _ a b U hU _ _ _ _ _
    exact h (n + 1) a b U hU
  · intro h
    by_contra hfail
    obtain ⟨N, hN, hbad, hbelow⟩ := exists_least_bad_order hfail
    cases N with
    | zero => omega
    | succ n =>
        rw [conjecture_iff_regular_matching_products] at hbad
        push_neg at hbad
        obtain ⟨a, b, U, hU, hnz, hinj, hnot⟩ := hbad
        obtain ⟨hleft, hright⟩ := nonnormal_poles_of_not_holds
          (hbelow n (Nat.lt_succ_self n)) a b U hU hnz hnot
        exact hnot (h n (by omega) a b U hU hnz hinj
          (scalar_of_commute_normal_pair_of_smaller_orders hbelow a b hU hnot) hleft hright)

end MOC
