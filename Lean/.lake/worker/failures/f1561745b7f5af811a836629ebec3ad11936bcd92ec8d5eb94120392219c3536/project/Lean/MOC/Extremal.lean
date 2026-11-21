import MOC.Claim
import MOC.SpectralGap
import MOC.SpectralPerturbation
import MOC.StrongSupport
import MOC.SupportBlocks

/-! Necessary conditions for a counterexample at a unitary support maximum. -/

open BigOperators Matrix

namespace MOC

private theorem no_paired_blocks_of_smaller_orders {n : ℕ}
    (hbelow : ∀ m < n, Conjecture (Fin m))
    {a b : Fin n → ℂ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitary U) (hnot : ¬ Holds a b U) : ¬ HasProperPairedBlocks U := by
  rintro ⟨m, k, eRow, eCol, X, Y, hm, hk, hsplit⟩
  have hcard := Fintype.card_congr eRow
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  exact hnot (holds_of_paired_blocks (hbelow m (by omega)) (hbelow k (by omega))
    eRow eCol a b U hU X Y hsplit)

/-- In the least failing order a counterexample can be chosen with distinct matching
products and an invertible, nonnormal sum at a support and Frobenius maximum.
The relative eigenbasis has no proper paired block split, and a quadratic
support penalty controls every determinant change on its unitary orbit. -/
theorem exists_least_bad_support_maximizer (h : ¬ MOCIsTrue) :
    ∃ n : ℕ, 4 ≤ n ∧ (∀ m < n, Conjecture (Fin m)) ∧
      ∃ (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (η : ℂ),
        IsUnitary U ∧ (∀ i j, a i + b j ≠ 0) ∧
        Function.Injective (matchingProduct a b) ∧ determinantValue a b U ≠ 0 ∧
        ¬ HasProperPairedBlocks U ∧
        (∀ σ : Equiv.Perm (Fin n),
          (η * matchingProduct a b σ).re < (η * determinantValue a b U).re) ∧
        (∀ V : Matrix (Fin n) (Fin n) ℂ, IsUnitary V →
          (η * (determinantValue a b V - determinantValue a b U)).re ≤
            -Complex.normSq (determinantValue a b V - determinantValue a b U) / 2) ∧
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
  obtain ⟨U, ξ, hU, hstrict, hpenalty, htie⟩ :=
    exists_quadratic_support_frobenius_maximizer a b V hV η hsep'
  have hmax (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnitary W) :
      (ξ * determinantValue a b W).re ≤ (ξ * determinantValue a b U).re := by
    have hle := hpenalty W hW
    rw [mul_sub, Complex.sub_re] at hle
    linarith only [hle, Complex.normSq_nonneg (determinantValue a b W - determinantValue a b U)]
  have hnot : ¬ Holds a b U := by
    intro hh
    obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hh ξ
    exact (not_le_of_gt (hstrict σ)) hσ
  have hdet : determinantValue a b U ≠ 0 := fun hz => hnot (holds_of_singular a b hU hz)
  have hblocks := no_paired_blocks_of_smaller_orders hbelow hU hnot
  refine ⟨n, hn, hbelow, a, b, U, ξ, hU, hab, hinj, hdet, hblocks, hstrict, hpenalty, hmax, htie, ?_⟩
  let B := U * diagonal b * Uᴴ
  refine ⟨fun hnormal =>
    hnot (holds_of_normal_support_frobenius_maximum a b hU ξ hnormal hmax htie), ?_⟩
  apply support_maximum_inverse_commutator (diagonal a) B ξ hdet
  intro R hR
  have hR' : IsUnitary Rᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hR.2 hR.1
  have hRU : IsUnitary (R * U) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Rᴴ U hR' hU
  simpa only [determinantValue, B, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
    hmax (R * U) hRU

/-- The normalized spectral optimization and least-order induction can be imposed
on the same counterexample. Its nonsingular, nonnormal sum satisfies both moment
balances, the centered Möbius bound, and strict support expansion. -/
theorem mocIsTrue_iff_balanced_expanding :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n → ∀ (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      spectralEnergy a b = 1 →
      (∑ i, a i) = (∑ i, b i) →
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
        (∑ i, (Complex.normSq (b i) : ℂ) * b i) →
      determinantValue a b U ≠ 0 →
      ¬ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) →
      (∀ s : Finset (Fin n), s.Nonempty → (∃ i, i ∉ s) →
        s.card < (supportColumns U s).card) →
      (∀ t : ℂ, (∀ i, 1 - t * a i ≠ 0) → (∀ j, 1 + t * b j ≠ 0) →
        let E := centeredSpectralEnergy (mobiusSpectrum t a) (mobiusSpectrum (-t) b)
        0 < E → 1 ≤ E ^ n * Complex.normSq (mobiusDenominator a b t)) →
      Holds a b U := by
  constructor
  · intro h n _ a b U hU _ _ _ _ _ _ _
    exact h n a b U hU
  · intro h
    by_contra hbad
    obtain ⟨n, hn, hfail, hbelow⟩ := exists_least_bad_order hbad
    unfold Conjecture at hfail
    push_neg at hfail
    obtain ⟨a₀, b₀, U₀, hU₀, hnot₀⟩ := hfail
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    obtain ⟨a, b, U, η, g, hU, henergy, hη, hg, htrace, hcubic, hnormal, hgap, hglobal⟩ :=
      exists_balanced_support_gap_maximizer a₀ b₀ U₀ hU₀ hnot₀
    have hnot : ¬ Holds a b U := by
      intro hh
      obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hh η
      have hgt := hg.trans_le (hgap σ)
      simp only [mul_sub, Complex.sub_re, sub_pos] at hgt
      exact (not_lt_of_ge hσ) hgt
    have hdet : determinantValue a b U ≠ 0 := fun hz =>
      hnot (holds_of_singular a b hU hz)
    have hexpand := card_lt_supportColumns_of_no_paired_blocks hU
      (no_paired_blocks_of_smaller_orders hbelow hU hnot)
    apply hnot
    apply h n hn a b U hU henergy htrace hcubic hdet hnormal hexpand
    intro t ha hb
    simpa only [Fintype.card_fin] using
      spectralEnergy_centered_mobius_bound a b U hU η hη hg hgap
        (fun c d k henergy' hk => hglobal c d U k henergy' hU hk) t ha hb

end MOC
