import MOC.Reformulations.Compounds
import MOC.Weights
import MOC.FourMinorTransport
import MOC.Reformulations.SecondCoefficient

open Matrix BigOperators

namespace MOC.Reformulations.CStar

noncomputable section

private theorem eval_charpoly_eq_det_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) : M.charpoly.eval z = (z • 1 - M).det := by
  rw [Matrix.charpoly, Matrix.eval_det]
  congr 1
  ext i j
  change (matPolyEquiv M.charmatrix).eval (Matrix.scalar (Fin n) z) i j = _
  rw [Matrix.matPolyEquiv_eval]
  by_cases h : i = j
  · subst j
    simp [Matrix.charmatrix_apply_eq, Matrix.smul_apply]
  · simp [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, Matrix.one_apply_ne h]

/-- A subset-image law determines a single characteristic-polynomial law.
In contrast to scalar MOC, the law does not change with the parameter. -/
theorem charpoly_eq_sum_of_indexed_minor_law {n : ℕ} {κ : Type*} [Fintype κ]
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (p : κ → Equiv.Perm (Fin n)) (w : κ → ℝ) (hm : ∀ I J : Finset (Fin n),
      subsetMinorSq U I J = ∑ k ∈ Finset.univ.filter (fun k => J.map (p k).toEmbedding = I), w k) :
    (∑ k, w k • (diagonal (fun j => a (p k j) + b j)).charpoly) =
      (diagonal a + U * diagonal b * Uᴴ).charpoly := by
  apply Polynomial.funext
  intro z
  have hd (d : Fin n → ℂ) :
      diagonal (fun j => z - d j) = z • (1 : Matrix (Fin n) (Fin n) ℂ) - diagonal d := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_smul, Complex.real_smul,
    eval_charpoly_eq_det_sub, ← hd, Matrix.det_diagonal]
  have he := determinantValue_eq_sum_of_indexed_minor_law
    (fun j => z - a j) (fun j => -b j) U hU p w hm
  change (∑ k, (w k : ℂ) * ∏ j, (z - a (p k j) + -b j)) =
    (diagonal (fun j => z - a j) + U * diagonal (fun j => -b j) * Uᴴ).det at he
  rw [hd, ← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul] at he
  simpa only [← sub_eq_add_neg, sub_sub] using he

/-- The strong compound comparison implies the full simultaneous
characteristic-polynomial comparison, not just its determinant projection. -/
theorem simultaneousCharacteristicForm_of_strongCompoundForm
    (h : StrongCompoundForm) : SimultaneousCharacteristicForm := by
  classical
  intro n a b U hU
  obtain ⟨w, hw, hs, hm⟩ := h n U hU
  have hmap (I J : Finset (Fin n)) (p : Equiv.Perm (Fin n)) :
      J.map p.symm.toEmbedding = I ↔ I.map p.toEmbedding = J := by
    constructor
    · intro h'
      rw [← h']
      ext k
      simp [Finset.mem_map_equiv]
    · intro h'
      rw [← h']
      ext k
      simp [Finset.mem_map_equiv]
  have hminor (I J : Finset (Fin n)) :
      subsetMinorSq U I J =
        ∑ p ∈ Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
          J.map p.symm.toEmbedding = I), w p := by
    rw [← hm I J, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    simp only [hmap]
    split_ifs <;> simp
  exact mem_convexHull_of_exists_fintype w
    (fun p : Equiv.Perm (Fin n) => (diagonal (fun j => a (p.symm j) + b j)).charpoly)
    hw hs (fun p => ⟨p.symm, rfl⟩)
    (charpoly_eq_sum_of_indexed_minor_law a b U hU Equiv.symm w hminor)


/-- A mixture of complete minor tables transports the entire characteristic
polynomial. The coefficients of this outer mixture are fixed before the spectra
and the scalar characteristic parameter are chosen. -/
theorem charpoly_eq_sum_of_minor_mixture {n : ℕ} {κ : Type*} [Fintype κ]
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U)
    (V : κ → Matrix (Fin n) (Fin n) ℂ) (hV : ∀ k, IsUnitary (V k))
    (w : κ → ℝ) (hm : ∀ I J : Finset (Fin n),
      subsetMinorSq U I J = ∑ k, w k * subsetMinorSq (V k) I J) :
    (diagonal a + U * diagonal b * Uᴴ).charpoly =
      ∑ k, w k • (diagonal a + V k * diagonal b * (V k)ᴴ).charpoly := by
  have hcompound (c d : Fin n → ℂ) :
      compoundValue c d U = ∑ k, (w k : ℂ) * compoundValue c d (V k) := by
    simp only [compoundValue, hm, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
      Finset.mul_sum]
    conv_lhs =>
      arg 2
      intro J
      rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact mul_assoc _ _ _
  have hdet (c d : Fin n → ℂ) :
      determinantValue c d U = ∑ k, (w k : ℂ) * determinantValue c d (V k) := by
    simpa only [determinantValue_eq_sum_subsetMinors c d U hU,
      determinantValue_eq_sum_subsetMinors c d _ (hV _), compoundValue] using hcompound c d
  apply Polynomial.funext
  intro z
  have heval (W : Matrix (Fin n) (Fin n) ℂ) :
      (diagonal a + W * diagonal b * Wᴴ).charpoly.eval z =
        determinantValue (fun j => z - a j) (fun j => -b j) W := by
    rw [eval_charpoly_eq_det_sub, determinantValue]
    congr 1
    have hd : diagonal (fun j => z - a j) =
        z • (1 : Matrix (Fin n) (Fin n) ℂ) - diagonal a := by
      rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
    rw [hd, ← Matrix.diagonal_neg, Matrix.mul_neg, Matrix.neg_mul, sub_add_eq_sub_sub]
    abel
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_smul, Complex.real_smul, heval]
  exact hdet _ _

/-- At order four even the simultaneous coefficient comparison reduces exactly
to real orthogonal mixers, without requiring an order-four permutation law. -/
theorem simultaneousCharacteristic_four_iff_orthogonal :
    (∀ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ), IsUnitary U →
      (diagonal a + U * diagonal b * Uᴴ).charpoly ∈ convexHull ℝ
        (Set.range fun p : Equiv.Perm (Fin 4) =>
          (diagonal (fun j => a (p j) + b j)).charpoly)) ↔
    (∀ (a b : Fin 4 → ℂ) (O : Matrix.orthogonalGroup (Fin 4) ℝ),
      let U := Complex.ofRealHom.mapMatrix O.val
      (diagonal a + U * diagonal b * Uᴴ).charpoly ∈ convexHull ℝ
        (Set.range fun p : Equiv.Perm (Fin 4) =>
          (diagonal (fun j => a (p j) + b j)).charpoly)) := by
  constructor
  · intro h a b O
    exact h a b _ (isUnitary_ofReal_orthogonal O)
  · intro h a b U hU
    obtain ⟨κ, _, w, O, hw, hs, hm⟩ := four_minor_mixture U hU
    let V (k : κ) := Complex.ofRealHom.mapMatrix (O k).val
    rw [charpoly_eq_sum_of_minor_mixture a b U hU V
      (fun k => isUnitary_ofReal_orthogonal (O k)) w hm]
    rw [← Finset.univ.centerMass_eq_of_sum_1 _ hs]
    exact (convex_convexHull ℝ _).centerMass_mem (fun k _ => hw k)
      (hs.symm ▸ zero_lt_one) (fun k _ => h a b (O k))


/-- Birkhoff singleton marginals already determine all minor marginals through
order three, because each higher minor is the complement of a singleton or
the empty set. The same law gives all characteristic coefficients. -/
theorem simultaneousCharacteristic_of_order_le_three {n : ℕ} (hn : n ≤ 3)
    (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) :
    (diagonal a + U * diagonal b * Uᴴ).charpoly ∈ convexHull ℝ
      (Set.range fun p : Equiv.Perm (Fin n) =>
        (diagonal (fun j => a (p j) + b j)).charpoly) := by
  classical
  obtain ⟨w, hw, hs, hm⟩ := exists_singleton_weights U hU
  have hminor := indexed_minor_law_of_small U hU id w (by
    intro I J hc hsmall
    have hI : I.card ≤ 1 := by
      rw [Fintype.card_fin] at hsmall
      omega
    by_cases hz : I.card = 0
    · have hI' := Finset.card_eq_zero.mp hz
      have hJ' := Finset.card_eq_zero.mp (hc.symm.trans hz)
      subst I J
      simpa [subsetMinorSq] using hs.symm
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (show I.card = 1 by omega)
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (show J.card = 1 by omega)
      rw [subsetMinorSq_singleton _ hU, Finset.sum_filter]
      apply Complex.ofReal_injective
      simpa [marginal, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using (hm i j).symm)
  exact mem_convexHull_of_exists_fintype w
    (fun p : Equiv.Perm (Fin n) => (diagonal (fun j => a (p j) + b j)).charpoly)
    hw hs (fun p => ⟨p, rfl⟩)
    (charpoly_eq_sum_of_indexed_minor_law a b U hU id w hminor)

end

end MOC.Reformulations.CStar
