import MOC.CyclicFourier
import MOC.Reformulations.FirstMatrix
import MOC.Reformulations.NativeLinksCTraceless

/-! A loopless complex weighted directed graph has an adjacency matrix
with zero diagonal. A Fourier change of basis realizes each traceless
spectral list by such a matrix. The relative unitary remains arbitrary. -/

open BigOperators Matrix

namespace MOC.Reformulations

/-- Directed graphs with no loops, complex edge weights, normal adjacency
matrices, and arbitrary relative unitary position. -/
def LooplessDirectedAdjacencyForm : Prop :=
  ∀ (n : ℕ) (A B U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ),
    IsStarNormal A → IsStarNormal B → IsUnitary U →
    (∀ j, A j j = 0) → (∀ j, B j j = 0) →
    A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a →
    B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b →
    (A + U * B * Uᴴ).det ∈ convexHull ℝ (Set.range (matchingProduct a b))

theorem looplessDirectedAdjacencyForm_iff : LooplessDirectedAdjacencyForm ↔ MOCIsTrue := by
  constructor
  · intro h
    apply tracelessCartanForm_iff.mp
    intro n a b U hU ha hb
    by_cases hn : n = 0
    · subst n
      exact conjecture_le_three (by decide) a b U hU
    letI : NeZero n := ⟨hn⟩
    let e : Fin n ≃ ZMod n := Fintype.equivOfCardEq (by rw [Fintype.card_fin, ZMod.card])
    let F := (cyclicFourier n).submatrix e e
    have hF : IsUnitary F := unitary_reindex e e (cyclicFourier_unitary n)
    have hFadj : IsUnitary Fᴴ :=
      ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hF.2,
        by simpa only [Matrix.conjTranspose_conjTranspose] using hF.1⟩
    have hFU : IsUnitary (F * U) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using relative_unitary Fᴴ U hFadj hU
    have hFUadj : IsUnitary (F * U)ᴴ :=
      ⟨by simpa only [Matrix.conjTranspose_conjTranspose] using hFU.2,
        by simpa only [Matrix.conjTranspose_conjTranspose] using hFU.1⟩
    let R := F * U * Fᴴ
    have hR : IsUnitary R := by
      simpa only [R, Matrix.conjTranspose_conjTranspose] using
        relative_unitary (F * U)ᴴ Fᴴ hFUadj hFadj
    have hzero (d : Fin n → ℂ) (hs : ∑ i, d i = 0) (i : Fin n) :
        (F * diagonal d * Fᴴ) i i = 0 := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
      calc
        _ = ∑ j, (n : ℂ)⁻¹ * d j := by
          apply Finset.sum_congr rfl
          intro j _
          have he : F i j * star (F i j) = (n : ℂ)⁻¹ :=
            cyclicFourier_mul_conj_entry n (e i) (e j)
          rw [← he]
          ring
        _ = 0 := by rw [← Finset.mul_sum, hs, mul_zero]
    have hRF : R * F = F * U := by
      dsimp only [R]
      rw [Matrix.mul_assoc (F * U), hF.2, Matrix.mul_one]
    have hconj : R * (F * diagonal b * Fᴴ) * Rᴴ =
        F * (U * diagonal b * Uᴴ) * Fᴴ := by
      calc
        _ = (R * F) * diagonal b * (R * F)ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hRF, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    have hsum : F * diagonal a * Fᴴ + R * (F * diagonal b * Fᴴ) * Rᴴ =
        F * (diagonal a + U * diagonal b * Uᴴ) * Fᴴ := by
      rw [hconj, Matrix.mul_add, Matrix.add_mul]
    have hv := h n (F * diagonal a * Fᴴ) (F * diagonal b * Fᴴ) R a b
      (isStarNormal_unitary_diagonalization a hF) (isStarNormal_unitary_diagonalization b hF)
      hR (hzero a ha) (hzero b hb) (roots_unitary_diagonalization a hF)
      (roots_unitary_diagonalization b hF)
    rw [hsum, det_unitary_conjugation F _ hF] at hv
    exact hv
  · intro h n A B U a b hA hB hU _ _ ha hb
    exact moc_iff_complexMatrices.mp h n A B U a b hA hB hU ha hb

end MOC.Reformulations
