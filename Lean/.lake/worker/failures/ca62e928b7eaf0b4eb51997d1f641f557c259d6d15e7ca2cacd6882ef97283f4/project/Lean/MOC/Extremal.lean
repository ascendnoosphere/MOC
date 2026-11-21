import MOC.Claim
import MOC.NormalOrbit
import MOC.SpectralPerturbation

/-! Necessary conditions for a counterexample at a unitary support maximum. -/

open Matrix

namespace MOC

/-- In the least failing order a counterexample can be chosen with distinct matching
products and an invertible, nonnormal sum at a support and Frobenius maximum.
The relative eigenbasis has no proper paired block split. -/
theorem exists_least_bad_support_maximizer (h : ¬ MOCIsTrue) :
    ∃ n : ℕ, 4 ≤ n ∧ (∀ m < n, Conjecture (Fin m)) ∧
      ∃ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (η : ℂ),
        IsUnitary U ∧ (∀ i j, a i + b j ≠ 0) ∧
        Function.Injective (matchingProduct a b) ∧ determinantValue a b U ≠ 0 ∧
        ¬ HasProperPairedBlocks U ∧
        (∀ σ : Equiv.Perm (Fin n),
          (η * matchingProduct a b σ).re < (η * determinantValue a b U).re) ∧
        (∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
          (η * determinantValue a b V).re ≤ (η * determinantValue a b U).re) ∧
        (∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
          (η * determinantValue a b V).re = (η * determinantValue a b U).re →
          frobeniusSq (diagonal a + V * diagonal b * Vᴴ) ≤
            frobeniusSq (diagonal a + U * diagonal b * Uᴴ)) ∧
        let B := U * diagonal b * Uᴴ
        let C := diagonal a + B
        let E := (η * C.det) • (B * C⁻¹ - C⁻¹ * B)
        ¬ IsStarNormal C ∧ Eᴴ = E := by
  classical
  obtain ⟨n, hn, hbad, hbelow⟩ := exists_least_bad_order h
  unfold Conjecture at hbad
  push_neg at hbad
  obtain ⟨a₀, b₀, V, hV, hfail⟩ := hbad
  rw [holds_iff_directional] at hfail
  push_neg at hfail
  obtain ⟨η, hsep⟩ := hfail
  obtain ⟨a, b, hab, hinj, hsep'⟩ :=
    exists_regular_spectra_of_support_violation a₀ b₀ V η hsep
  obtain ⟨U, hU, hmax, htie⟩ := exists_support_frobenius_maximizer a b η
  have hstrict (σ : Equiv.Perm (Fin n)) :
      (η * matchingProduct a b σ).re < (η * determinantValue a b U).re :=
    (hsep' σ).trans_le (hmax V hV)
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
  refine ⟨n, hn, hbelow, a, b, U, η, hU, hab, hinj, hdet, hblocks, hstrict, hmax, htie, ?_⟩
  let B := U * diagonal b * Uᴴ
  refine ⟨fun hnormal =>
    hnot (holds_of_normal_support_frobenius_maximum a b hU η hnormal hmax htie), ?_⟩
  apply support_maximum_inverse_commutator (diagonal a) B η hdet
  intro R hR
  have hR' : IsUnitary Rᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hR.2 hR.1
  have hRU : IsUnitary (R * U) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ U hR' hU
  simpa only [determinantValue, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
    hmax (R * U) hRU

end MOC
