import MOC.SinglePortComposition
import MOC.OrderFourComplexHadamard
import MOC.OrderFourZeroDiagonalUnitary
import MOC.TwoByTwoTensorPermutationLaw
import MOC.FiveFourierNeighborhood

/-! Determinant inclusion for trees of unitary blocks joined at one coordinate. -/

open Matrix
open scoped Kronecker Matrix.L2OpNorm

namespace MOC

noncomputable section

private def portLast {n : ℕ} (p : Fin (n + 1)) : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.optionEquivSumPUnit (Fin n)).symm.trans (finSuccEquiv' p).symm

private def portFirst {n : ℕ} (p : Fin (n + 1)) : Unit ⊕ Fin n ≃ Fin (n + 1) :=
  (Equiv.sumComm Unit (Fin n)).trans (portLast p)

private def portOutput {n m : ℕ} (p : Fin (n + 1)) :
    ((Fin n ⊕ Unit) ⊕ Fin m) ≃ Fin (n + 1 + m) :=
  (Equiv.sumCongr (portLast p) (Equiv.refl (Fin m))).trans finSumFinEquiv

/-- Merge two unitary blocks at the selected coordinates. The left block acts after
the right block. The output keeps all left labels, then the right labels other
than the shared coordinate in their original order. -/
def joinMixerAtPort {n m : ℕ} (p : Fin (n + 1)) (q : Fin (m + 1))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (V : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    Matrix (Fin (n + 1 + m)) (Fin (n + 1 + m)) ℂ :=
  (singlePortLeft (U.submatrix (portLast p) (portLast p)) *
    singlePortRight (V.submatrix (portFirst q) (portFirst q))).submatrix
      (portOutput (m := m) p).symm (portOutput (m := m) p).symm

theorem joinMixerAtPort_unitary {n m : ℕ} (p : Fin (n + 1)) (q : Fin (m + 1))
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {V : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (joinMixerAtPort p q U V) := by
  let X := singlePortLeft (R := Fin m) (U.submatrix (portLast p) (portLast p))
  let Y := singlePortRight (L := Fin n) (V.submatrix (portFirst q) (portFirst q))
  have hX : IsUnitary X := unitary_directSum (unitary_reindex _ _ hU) isUnitary_one
  have hY : IsUnitary Y :=
    unitary_reindex _ _ (unitary_directSum isUnitary_one (unitary_reindex _ _ hV))
  have hX' : IsUnitary Xᴴ := by
    simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose, and_comm] using hX
  have hXY : IsUnitary (X * Y) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Xᴴ Y hX' hY
  exact unitary_reindex _ _ hXY

theorem holds_joinMixerAtPort {n m : ℕ} (p : Fin (n + 1)) (q : Fin (m + 1))
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {V : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hU : IsUnitary U) (hV : IsUnitary V)
    (hUholds : ∀ a b, Holds a b U) (hVholds : ∀ a b, Holds a b V)
    (a b : Fin (n + 1 + m) → ℂ) : Holds a b (joinMixerAtPort p q U V) := by
  let X := U.submatrix (portLast p) (portLast p)
  let Y := V.submatrix (portFirst q) (portFirst q)
  let e := portOutput (m := m) p
  have hX : ∀ c d, Holds c d X := by
    intro c d
    have h := (holds_reindex_iff (portLast p) (portLast p) (c ∘ (portLast p).symm)
      (d ∘ (portLast p).symm) U).mpr (hUholds _ _)
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using h
  have hY : ∀ c d, Holds c d Y := by
    intro c d
    have h := (holds_reindex_iff (portFirst q) (portFirst q) (c ∘ (portFirst q).symm)
      (d ∘ (portFirst q).symm) V).mpr (hVholds _ _)
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using h
  have h := holds_singlePortComposition (a ∘ e) (b ∘ e) X Y
    (unitary_reindex _ _ hU) (unitary_reindex _ _ hV) hX hY
  have h' := (holds_reindex_iff e.symm e.symm (a ∘ e) (b ∘ e)
    (singlePortLeft X * singlePortRight Y)).mpr h
  simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using h'

private def tensorLabels : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m := 2) (n := 2)).symm

/-- A radius of a unitary neighborhood of the order-five Fourier mixer in
which the inclusion holds for arbitrary spectra. -/
def blockTreeFourierRadius : ℝ := Classical.choose holds_on_cyclicFourier_five_ball

theorem blockTreeFourierRadius_pos : 0 < blockTreeFourierRadius :=
  (Classical.choose_spec holds_on_cyclicFourier_five_ball).1

/-- Start with an identity mixer, an order at most three unitary, or an order-four
flat or zero-diagonal unitary, a tensor of two order-two unitaries, or a
unitary in the order-five Fourier neighborhood. Recursively join any two
such mixers at one label. The selected labels can differ at each join. -/
inductive UnitaryBlockTree : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ → Prop
  | identity (n : ℕ) : UnitaryBlockTree n 1
  | small {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
      (hn : n ≤ 3) (hU : IsUnitary U) : UnitaryBlockTree n U
  | flatFour {U : Matrix (Fin 4) (Fin 4) ℂ}
      (hU : IsUnitary U) (hFlat : ∀ i j, Complex.normSq (U i j) = 1 / 4) :
      UnitaryBlockTree 4 U
  | zeroDiagonalFour {U : Matrix (Fin 4) (Fin 4) ℂ}
      (hU : IsUnitary U) (hZero : ∀ i, U i i = 0) : UnitaryBlockTree 4 U
  | tensorFour {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnitary A) (hB : IsUnitary B) :
      UnitaryBlockTree 4 ((A ⊗ₖ B).submatrix tensorLabels tensorLabels)
  | fourierFive {U : Matrix (ZMod 5) (ZMod 5) ℂ} (hU : IsUnitary U)
      (hDist : dist U (cyclicFourier 5) < blockTreeFourierRadius) :
      UnitaryBlockTree 5 (U.submatrix (ZMod.finEquiv 5) (ZMod.finEquiv 5))
  | join {n m : ℕ} (p : Fin (n + 1)) (q : Fin (m + 1))
      {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
      {V : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
      (hU : UnitaryBlockTree (n + 1) U) (hV : UnitaryBlockTree (m + 1) V) :
      UnitaryBlockTree (n + 1 + m) (joinMixerAtPort p q U V)

private theorem tensorFour_unitary (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A ⊗ₖ B) := by
  have hstar : (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.conjTranspose_apply, Matrix.kronecker_apply, star_mul', mul_comm]
  constructor
  · rw [hstar, ← Matrix.mul_kronecker_mul, hA.1, hB.1, Matrix.one_kronecker_one]
  · rw [hstar, ← Matrix.mul_kronecker_mul, hA.2, hB.2, Matrix.one_kronecker_one]

/-- All orders of a unitary block tree satisfy determinant inclusion for every
pair of complex spectra. -/
theorem UnitaryBlockTree.unitary_and_holds {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (h : UnitaryBlockTree n U) : IsUnitary U ∧ ∀ a b : Fin n → ℂ, Holds a b U := by
  induction h with
  | identity => exact ⟨isUnitary_one, holds_identity⟩
  | small hn hU =>
    exact ⟨hU, fun a b =>
      conjecture_of_card_le_three (by simpa only [Fintype.card_fin] using hn) a b _ hU⟩
  | flatFour hU hFlat => exact ⟨hU, fun a b => holds_flat_four a b _ hU hFlat⟩
  | zeroDiagonalFour hU hZero => exact ⟨hU, fun a b => four_holds_zero_diagonal_unitary a b hU hZero⟩
  | @tensorFour A B hA hB =>
    refine ⟨unitary_reindex _ _ (tensorFour_unitary A B hA hB), fun a b => ?_⟩
    have h := (holds_reindex_iff tensorLabels tensorLabels (a ∘ tensorLabels.symm)
      (b ∘ tensorLabels.symm) (A ⊗ₖ B)).mpr (holds_twoByTwoTensor A B hA hB _ _)
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using h
  | @fourierFive U hU hDist =>
    let e := (ZMod.finEquiv 5).toEquiv
    refine ⟨unitary_reindex e e hU, fun a b => ?_⟩
    have hlocal := (Classical.choose_spec holds_on_cyclicFourier_five_ball).2 U hU hDist
    have h := (holds_reindex_iff e e (a ∘ e.symm) (b ∘ e.symm) U).mpr (hlocal _ _)
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using h
  | join p q _ _ ihU ihV =>
    exact ⟨joinMixerAtPort_unitary p q ihU.1 ihV.1,
      holds_joinMixerAtPort p q ihU.1 ihV.1 ihU.2 ihV.2⟩

end

end MOC
