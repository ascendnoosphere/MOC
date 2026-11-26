import MOC.FourTerminalCoverage
import MOC.FourCanonicalHeightSquares

open Matrix BigOperators

namespace MOC

/-- An order-four violation has a regular orthogonal witness with at least
seven contacts and canonical mixed coefficient one. Its normalized support
height is negative or greater than one half. -/
theorem exists_canonical_mixed_terminal_witness_outside_height_interval
    (h : ¬ Conjecture (Fin 4)) :
    ∃ O : Matrix.orthogonalGroup (Fin 4) ℝ,
      ∃ w : StrictMatchingSupport (Complex.ofRealHom.mapMatrix O.val),
        FourRegularSpectra w ∧ 7 ≤ w.contacts.card ∧
        ∃ c : Fin 34 → ℝ, (∀ j, 0 ≤ c j) ∧
          (∀ j ∉ fourCanonicalCapOrdinaryRays, c j = 0) ∧
          fourTerminalGap w = (∑ j, c j • ordinaryCostRay j) + mixedCostRay 0 ∧
          let height := (w.η * matchingProduct w.a w.b w.pivot).re
          height < 0 ∨ 1 / 2 < height := by
  classical
  obtain ⟨O, w, hreg, hcontacts, c, hc, hcs, hgap⟩ := exists_canonical_mixed_terminal_witness h
  refine ⟨O, w, hreg, hcontacts, c, hc, hcs, hgap, ?_⟩
  let height := (w.η * matchingProduct w.a w.b w.pivot).re
  change height < 0 ∨ 1 / 2 < height
  by_cases hnegative : height < 0
  · exact Or.inl hnegative
  by_cases hhigh : 1 / 2 < height
  · exact Or.inr hhigh
  let c' (j : Fin 13) := c (fourCanonicalZeroHeightRay j)
  have hinj : Function.Injective fourCanonicalZeroHeightRay := by
    change ∀ i j : Fin 13, fourCanonicalZeroHeightRay i = fourCanonicalZeroHeightRay j → i = j
    decide +kernel
  have hcap : Finset.univ.image fourCanonicalZeroHeightRay = fourCanonicalCapOrdinaryRays := by
    decide +kernel
  have hsums (p : Fin 24) :
      (∑ j, c' j * ordinaryCostRay (fourCanonicalZeroHeightRay j) p) =
        ∑ j, c j * ordinaryCostRay j p := by
    calc
      _ = ∑ j ∈ Finset.univ.image fourCanonicalZeroHeightRay, c j * ordinaryCostRay j p :=
        (Finset.sum_image (fun _ _ _ _ he => hinj he)).symm
      _ = _ := by
        rw [hcap]
        exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by rw [hcs j hj, zero_mul])
  have hvalues (p : Fin 24) : fourCanonicalZeroHeightProfile c' p =
      height - (w.η * matchingProduct w.a w.b (fourPerm p).symm).re := by
    change fourCanonicalZeroHeightProfile c' p = fourTerminalGap w p
    rw [hgap, fourCanonicalZeroHeightProfile]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsums, add_comm]
  have hbound := fourCanonicalHeight_le_half_support w.a w.b w.η c'
    (fun j => hc (fourCanonicalZeroHeightRay j)) height
    (le_of_not_gt hnegative) (le_of_not_gt hhigh) hvalues _
    (isUnitary_ofReal_orthogonal O)
  exact (not_lt_of_ge hbound w.strict).elim

end MOC
