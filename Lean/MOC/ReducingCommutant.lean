import MOC.NormalOrbit
import MOC.CommonCommutant
import MOC.SpectralPerturbation

/-! A common Hermitian symmetry reduces normal summands to smaller pairs,
including when their spectra have multiplicities. -/

open Matrix
open scoped ComplexStarModule

namespace MOC

/-- A nonscalar Hermitian common commutant puts both normal summands in
proper reducing blocks, so lower-order determinant inclusions suffice. -/
theorem holds_of_reducing_commutant {n : ℕ} [Nonempty (Fin n)]
    (hbelow : ∀ m < n, Conjecture (Fin m))
    (a b : Fin n → ℂ) {U H : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitary U) (hH : H.IsHermitian)
    (hAH : Commute (diagonal a) H) (hBH : Commute (U * diagonal b * Uᴴ) H)
    (hnonscalar : ¬ ∃ μ : ℂ, H = μ • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    Holds a b U := by
  classical
  have h1 : IsUnitary (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [IsUnitary]
  have hAH' : Commute (1 * diagonal a * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ) H := by
    simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using hAH
  obtain ⟨d, V, hV, hAV, hd⟩ :=
    joint_diagonalization_with_hermitian_commutant a 1 H h1 hH hAH'
  obtain ⟨e, W, hW, hBW, he⟩ :=
    joint_diagonalization_with_hermitian_commutant b U H hU hH hBH
  have hdV : Vᴴ * H = diagonal d * Vᴴ := by
    calc
      _ = (Vᴴ * V) * diagonal d * Vᴴ := by rw [hd]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV.2, Matrix.one_mul]
  have heW : H * W = W * diagonal e := by
    rw [he, Matrix.mul_assoc (W * diagonal e), hW.2, Matrix.mul_one]
  have hde : diagonal d * (Vᴴ * W) = (Vᴴ * W) * diagonal e := by
    calc
      _ = (Vᴴ * H) * W := by rw [hdV, Matrix.mul_assoc]
      _ = Vᴴ * (W * diagonal e) := by rw [Matrix.mul_assoc, heW]
      _ = _ := by rw [Matrix.mul_assoc]
  have hR := relative_unitary V W hV hW
  have hblocks : HasProperPairedBlocks (Vᴴ * W) := by
    by_contra hnoBlocks
    obtain ⟨μ, hμ⟩ := constant_left_labels_of_diagonal_intertwining hR
      (card_lt_supportColumns_of_no_paired_blocks hR hnoBlocks) d e hde
    apply hnonscalar
    refine ⟨μ, ?_⟩
    rw [hd, hμ, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hV.1]
  obtain ⟨m, k, er, ec, P, Q, hm, hk, hRsplit⟩ := hblocks
  have hcard := Fintype.card_congr er
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hAV' : diagonal a = V * diagonal a * Vᴴ := by
    simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using hAV
  apply (holds_iff_relative_to_diagonalizations a b a b hU hV hW hAV' hBW).mpr
  exact holds_of_paired_blocks (hbelow m (by omega)) (hbelow k (by omega))
    er ec _ _ _ hR P Q hRsplit

/-- A complex scale on the right spectrum preserves its reducing commutant. -/
theorem holds_of_hermitian_reducing_commutant {n : ℕ} [Nonempty (Fin n)]
    (hbelow : ∀ m < n, Conjecture (Fin m))
    (a c : Fin n → ℂ) {U H : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsUnitary U) (_ha : (diagonal a).IsHermitian)
    (_hc : (U * diagonal c * Uᴴ).IsHermitian) (hH : H.IsHermitian)
    (hAH : Commute (diagonal a) H) (hCH : Commute (U * diagonal c * Uᴴ) H)
    (hnonscalar : ¬ ∃ μ : ℂ, H = μ • (1 : Matrix (Fin n) (Fin n) ℂ)) (z : ℂ) :
    Holds a (fun i => z * c i) U := by
  apply holds_of_reducing_commutant hbelow a (fun i => z * c i) hU hH hAH _ hnonscalar
  change Commute (U * diagonal (z • c) * Uᴴ) H
  rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  exact hCH.smul_left z

/-- A least-order violation has scalar common commutant, even for repeated
spectra. A nonscalar Hermitian part of a common commuter would give a split. -/
theorem scalar_of_commute_normal_pair_of_smaller_orders {n : ℕ} [Nonempty (Fin n)]
    (hbelow : ∀ m < n, Conjecture (Fin m)) (a b : Fin n → ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (hnot : ¬ Holds a b U)
    (Y : Matrix (Fin n) (Fin n) ℂ)
    (hAY : Commute (diagonal a) Y) (hBY : Commute (U * diagonal b * Uᴴ) Y) :
    ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hreal (A : Matrix (Fin n) (Fin n) ℂ) (h : Commute A Y) (h' : Commute A Yᴴ) :
      Commute A (ℜ Y : Matrix (Fin n) (Fin n) ℂ) ∧ Commute A (ℑ Y : Matrix (Fin n) (Fin n) ℂ) := by
    constructor
    · simpa only [realPart_apply_coe] using (h.add_right h').smul_right (2⁻¹ : ℝ)
    · simpa only [imaginaryPart_apply_coe] using
        (((h.sub_right h').smul_right (2⁻¹ : ℝ)).smul_right (-Complex.I))
  have h1 : IsUnitary (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [IsUnitary]
  have hAY' : Commute (1 * diagonal a * (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ) Y := by
    simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using hAY
  have hAYstar : Commute (diagonal a) Yᴴ := by
    simpa only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using
      commute_adjoint_of_commute_spectral_diagonalization a 1 Y h1 hAY'
  have hBYstar := commute_adjoint_of_commute_spectral_diagonalization b U Y hU hBY
  obtain ⟨hAR, hAI⟩ := hreal _ hAY hAYstar
  obtain ⟨hBR, hBI⟩ := hreal _ hBY hBYstar
  have hscalar (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
      (hAH : Commute (diagonal a) H) (hBH : Commute (U * diagonal b * Uᴴ) H) :
      ∃ μ : ℂ, H = μ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    by_contra hn
    exact hnot (holds_of_reducing_commutant hbelow a b hU hH hAH hBH hn)
  obtain ⟨μ, hμ⟩ := hscalar (ℜ Y : Matrix (Fin n) (Fin n) ℂ) (ℜ Y).property hAR hBR
  obtain ⟨ν, hν⟩ := hscalar (ℑ Y : Matrix (Fin n) (Fin n) ℂ) (ℑ Y).property hAI hBI
  refine ⟨μ + Complex.I * ν, ?_⟩
  calc
    Y = (ℜ Y : Matrix (Fin n) (Fin n) ℂ) + Complex.I • (ℑ Y : Matrix (Fin n) (Fin n) ℂ) :=
      (realPart_add_I_smul_imaginaryPart Y).symm
    _ = _ := by rw [hμ, hν, smul_smul, ← add_smul]

/-- It suffices to prove the conjecture for normal pairs with scalar common
commutant, without any simplicity requirements on the spectra. -/
theorem mocIsTrue_iff_scalar_common_commutant :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n → ∀ (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      (∀ Y : Matrix (Fin n) (Fin n) ℂ, Commute (diagonal a) Y →
        Commute (U * diagonal b * Uᴴ) Y → ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ)) →
      Holds a b U := by
  constructor
  · intro h n _ a b U hU _
    exact h n a b U hU
  · intro h
    by_contra hfail
    obtain ⟨n, hn, hbelow, a, b, U, hU, hnot, _⟩ := exists_least_bad_instance hfail
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact hnot (h n hn a b U hU (scalar_of_commute_normal_pair_of_smaller_orders hbelow a b hU hnot))

/-- Nonzero spectral sums, distinct matching products, and scalar common
commutant can be imposed simultaneously on a least-order violation. -/
theorem mocIsTrue_iff_regular_scalar_common_commutant :
    MOCIsTrue ↔ ∀ (n : ℕ), 4 ≤ n → ∀ (a b : Fin n → ℂ)
      (U : Matrix (Fin n) (Fin n) ℂ), IsUnitary U →
      (∀ i j, a i + b j ≠ 0) → Function.Injective (matchingProduct a b) →
      (∀ Y : Matrix (Fin n) (Fin n) ℂ, Commute (diagonal a) Y →
        Commute (U * diagonal b * Uᴴ) Y → ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ)) →
      Holds a b U := by
  constructor
  · intro h n _ a b U hU _ _ _
    exact h n a b U hU
  · intro h
    by_contra hfail
    obtain ⟨n, hn, hbelow, a, b, U, hU, hnot, _⟩ := exists_least_bad_instance hfail
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    rw [holds_iff_directional] at hnot
    push_neg at hnot
    obtain ⟨η, hsep⟩ := hnot
    obtain ⟨a', b', hnz, hinj, hsep'⟩ :=
      exists_regular_spectra_of_support_violation a b U η hsep
    have hnot' : ¬ Holds a' b' U := by
      intro hh
      obtain ⟨σ, hσ⟩ := (holds_iff_directional a' b' U).mp hh η
      exact (not_le_of_gt (hsep' σ)) hσ
    exact hnot' (h n hn a' b' U hU hnz hinj
      (scalar_of_commute_normal_pair_of_smaller_orders hbelow a' b' hU hnot'))

/-- At a violation of least order, the Hermitian-pencil scalar commutant
condition holds without simple spectra. -/
theorem scalar_of_commute_hermitian_pencil_of_smaller_orders {n : ℕ} [Nonempty (Fin n)]
    (hbelow : ∀ m < n, Conjecture (Fin m)) (a c : Fin n → ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (_ha : (diagonal a).IsHermitian) (_hc : (U * diagonal c * Uᴴ).IsHermitian)
    {z : ℂ} (hnot : ¬ Holds a (fun i => z * c i) U)
    (Y : Matrix (Fin n) (Fin n) ℂ)
    (hAY : Commute (diagonal a) Y) (hCY : Commute (U * diagonal c * Uᴴ) Y) :
    ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  apply scalar_of_commute_normal_pair_of_smaller_orders hbelow a (fun i => z * c i) hU hnot Y hAY
  change Commute (U * diagonal (z • c) * Uᴴ) Y
  rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  exact hCY.smul_left z

/-- The scalar commutant hypothesis for the resolvent pencil follows from
least-order induction even when the spectra of its Hermitian terms repeat. -/
theorem scalar_of_commute_hermitian_resolvent_of_smaller_orders {n : ℕ} [Nonempty (Fin n)]
    (hbelow : ∀ m < n, Conjecture (Fin m)) (a c : Fin n → ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : IsUnitary U)
    (ha : (diagonal a).IsHermitian) (hc : (U * diagonal c * Uᴴ).IsHermitian)
    (hinv : IsUnit (diagonal a).det) {z : ℂ} (hnot : ¬ Holds a (fun i => z * c i) U)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hAY : Commute (diagonal a) Y)
    (hXY : Commute ((U * diagonal c * Uᴴ) * (diagonal a)⁻¹) Y) :
    ∃ μ : ℂ, Y = μ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hCY := hXY.mul_left hAY
  rw [Matrix.mul_assoc (U * diagonal c * Uᴴ), (diagonal a).nonsing_inv_mul hinv,
    Matrix.mul_one] at hCY
  exact scalar_of_commute_hermitian_pencil_of_smaller_orders hbelow a c hU ha hc hnot Y hAY hCY

end MOC
