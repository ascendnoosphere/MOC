import MOC.Claim
import MOC.Singular
import MOC.Support
import MOC.Variational

/-! Necessary conditions for a counterexample at a unitary support maximum. -/

open Matrix

namespace MOC

/-- In the least failing order there is a strict support violation at an invertible,
stationary sum. The relative eigenbasis has no proper paired block split. -/
theorem exists_least_bad_support_maximizer (h : ¬ MOCIsTrue) :
    ∃ n : ℕ, 4 ≤ n ∧ (∀ m < n, Conjecture (Fin m)) ∧
      ∃ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (η : ℂ),
        IsUnitary U ∧ (∀ i j, a i + b j ≠ 0) ∧ determinantValue a b U ≠ 0 ∧
        ¬ HasProperPairedBlocks U ∧
        (∀ σ : Equiv.Perm (Fin n),
          (η * matchingProduct a b σ).re < (η * determinantValue a b U).re) ∧
        (∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
          (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) ∧
        let B := U * diagonal b * Uᴴ
        let C := diagonal a + B
        let E := (η * C.det) • (B * C⁻¹ - C⁻¹ * B)
        Eᴴ = E := by
  classical
  obtain ⟨n, hn, hbad, hbelow⟩ := exists_least_bad_order h
  have hex : ∃ (a b : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ),
      IsUnitary V ∧ (∀ i j, a i + b j ≠ 0) ∧ ¬ Holds a b V := by
    by_contra hnone
    apply hbad
    apply conjecture_iff_nonopposite.mpr
    intro a b V hV hab
    by_contra hfail
    exact hnone ⟨a, b, V, hV, hab, hfail⟩
  obtain ⟨a, b, V, hV, hab, hfail⟩ := hex
  rw [holds_iff_directional] at hfail
  push_neg at hfail
  obtain ⟨η, hsep⟩ := hfail
  obtain ⟨U, hU, hmax⟩ := exists_support_maximizer a b η
  have hstrict (σ : Equiv.Perm (Fin n)) :
      (η * matchingProduct a b σ).re < (η * determinantValue a b U).re :=
    (hsep σ).trans_le (hmax V hV)
  have hnot : ¬ Holds a b U := by
    intro hh
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hh η
    exact (not_le_of_gt (hstrict σ)) hσ
  have hdet : determinantValue a b U ≠ 0 := fun hz => hnot (holds_of_singular a b hU hz)
  have hblocks : ¬ HasProperPairedBlocks U := by
    rintro ⟨m, k, eRow, eCol, X, Y, hm, hk, hsplit⟩
    have hcard := Fintype.card_congr eRow
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    exact hnot (holds_of_paired_blocks (hbelow m (by omega)) (hbelow k (by omega))
      eRow eCol a b U hU X Y hsplit)
  refine ⟨n, hn, hbelow, a, b, U, η, hU, hab, hdet, hblocks, hstrict, hmax, ?_⟩
  let B := U * diagonal b * Uᴴ
  apply support_maximum_inverse_commutator (diagonal a) B η hdet
  intro R hR
  have hR' : IsUnitary Rᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hR.2 hR.1
  have hRU : IsUnitary (R * U) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ U hR' hU
  simpa only [determinantValue, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
    hmax (R * U) hRU

end MOC
