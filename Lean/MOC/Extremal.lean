import MOC.BalancedStrongSupport
import MOC.SparseRow
import MOC.SpectralPerturbation

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
balances, the centered Möbius bound, strict support expansion, and the quadratic
orbit support penalty. Each row and column has at least three nonzero entries. -/
theorem mocIsTrue_iff_balanced_expanding :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n → ∀ (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ) (ξ : ℂ), IsUnitary U →
      spectralEnergy a b = 1 →
      (∑ i, a i) = (∑ i, b i) →
      (∑ i, (Complex.normSq (a i) : ℂ) * a i) =
        (∑ i, (Complex.normSq (b i) : ℂ) * b i) →
      determinantValue a b U ≠ 0 →
      ¬ IsStarNormal (diagonal a + U * diagonal b * Uᴴ) →
      (∀ s : Finset (Fin n), s.Nonempty → (∃ i, i ∉ s) →
        s.card < (supportColumns U s).card) →
      (∀ i, 3 ≤ (supportColumns U {i}).card) →
      (∀ j, 3 ≤ (supportColumns Uᴴ {j}).card) →
      (∀ t : ℂ, (∀ i, 1 - t * a i ≠ 0) → (∀ j, 1 + t * b j ≠ 0) →
        let E := centeredSpectralEnergy (mobiusSpectrum t a) (mobiusSpectrum (-t) b)
        0 < E → 1 ≤ E ^ n * Complex.normSq (mobiusDenominator a b t)) →
      (∀ W : Matrix (Fin n) (Fin n) ℂ, IsUnitary W →
        (ξ * (determinantValue a b W - determinantValue a b U)).re ≤
          -Complex.normSq (determinantValue a b W - determinantValue a b U) / 2) →
      (∀ W : Matrix (Fin n) (Fin n) ℂ, IsUnitary W →
        (ξ * determinantValue a b W).re = (ξ * determinantValue a b U).re →
        frobeniusSq (diagonal a + W * diagonal b * Wᴴ) ≤
          frobeniusSq (diagonal a + U * diagonal b * Uᴴ)) →
      Holds a b U := by
  constructor
  · intro h n _ a b U _ hU _ _ _ _ _ _ _ _ _ _ _
    exact h n a b U hU
  · intro h
    by_contra hbad
    obtain ⟨n, hn, hfail, hbelow⟩ := exists_least_bad_order hbad
    cases n with
    | zero => omega
    | succ n =>
      unfold Conjecture at hfail
      push_neg at hfail
      obtain ⟨a₀, b₀, U₀, hU₀, hnot₀⟩ := hfail
      letI : Nonempty (Fin (n + 1)) := ⟨⟨0, Nat.succ_pos n⟩⟩
      obtain ⟨a, b, U, ξ, hU, henergy, htrace, hcubic, hshift, hdet, hnormal,
        hstrict, hpenalty, htie⟩ :=
        exists_balanced_quadratic_support_frobenius_maximizer a₀ b₀ U₀ hU₀ hnot₀
      have hnot : ¬ Holds a b U := by
        intro hh
        obtain ⟨σ, hσ⟩ := (holds_iff_directional a b U).mp hh ξ
        exact (not_lt_of_ge hσ) (hstrict σ)
      have hexpand := card_lt_supportColumns_of_no_paired_blocks hU
        (no_paired_blocks_of_smaller_orders hbelow hU hnot)
      have hSmall := hbelow n (Nat.lt_succ_self n)
      apply hnot
      refine h (n + 1) hn a b U ξ hU henergy htrace hcubic hdet hnormal hexpand
        ?_ ?_ ?_ hpenalty htie
      · intro i
        by_contra hi
        exact hnot (holds_of_row_degree_le_two hSmall a b hU i (by omega))
      · intro j
        by_contra hj
        exact hnot (holds_of_column_degree_le_two hSmall a b hU j (by omega))
      · intro t ha hb
        let c := mobiusSpectrum t a
        let d := mobiusSpectrum (-t) b
        let N : ℝ := 2 * (Fintype.card (Fin (n + 1)) : ℝ)
        let s : ℂ := -((∑ i, c i) - ∑ j, d j) / (N : ℂ)
        have he : spectralEnergy (fun i => c i + s) (fun j => d j - s) =
            centeredSpectralEnergy c d := spectralEnergy_centering c d
        have hbound := hshift t s ha hb
        change 0 < spectralEnergy (fun i => c i + s) (fun j => d j - s) →
          1 ≤ spectralEnergy (fun i => c i + s) (fun j => d j - s) ^
            Fintype.card (Fin (n + 1)) * Complex.normSq (mobiusDenominator a b t) at hbound
        simpa only [he, Fintype.card_fin] using hbound

end MOC
