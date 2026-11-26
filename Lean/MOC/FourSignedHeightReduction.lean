import MOC.FourFourteenTermSupport
import MOC.FourMinorTransport
import MOC.FourSignedMinorIdentity

/-! Independent row and column permutations identify each order-four mixed ray
with the negative of the signed minor correction. -/

open BigOperators

namespace MOC

noncomputable section

private def correctionRows (r : Fin 48) : FourPerm :=
  fourPerm ⟨r.val % 24, Nat.mod_lt _ (by decide)⟩ * (fourPerm 5)⁻¹

private def correctionColumns (r : Fin 48) : FourPerm :=
  (fourPerm (if r.val < 24 then 0 else 1))⁻¹ * fourPerm 1

private def correctionEventInt (r : Fin 48) (k : Fin 34) (p : Fin 24) : ℤ :=
  let I := (ordinaryCostRows k).map (correctionRows r).toEmbedding
  let J := (ordinaryCostColumns k).map (correctionColumns r).toEmbedding
  if J.map (fourPerm p).symm.toEmbedding = I then 1 else 0

private def correctionEvent (r : Fin 48) (k : Fin 34) (p : Fin 24) : ℝ :=
  correctionEventInt r k p

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem correctionEvent_profile (r : Fin 48) :
    -mixedCostRay r = correctionEvent r 18 - correctionEvent r 0 -
      correctionEvent r 14 - correctionEvent r 27 := by
  have h : ∀ (i : Fin 48) (p : Fin 24),
      -mixedCostRayInt i p = correctionEventInt i 18 p - correctionEventInt i 0 p -
        correctionEventInt i 14 p - correctionEventInt i 27 p := by
    intro i
    fin_cases i <;> decide +kernel
  funext p
  simpa only [Pi.neg_apply, Pi.sub_apply, correctionEvent, mixedCostRay,
    Int.cast_neg, Int.cast_sub] using congrArg (Int.cast : ℤ → ℝ) (h r p)

private theorem correctionEvent_value (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U)
    (r : Fin 48) (k : Fin 34) :
    fourSupportCostValue U (correctionEvent r k) =
      subsetMinorSq (U.submatrix (correctionRows r) (correctionColumns r))
        (ordinaryCostRows k) (ordinaryCostColumns k) := by
  rw [squared_minor_reindex _ _ U hU]
  let I := (ordinaryCostRows k).map (correctionRows r).toEmbedding
  let J := (ordinaryCostColumns k).map (correctionColumns r).toEmbedding
  let e : Fin 24 ≃ FourPerm := fourPermEquiv.trans (Equiv.inv FourPerm)
  let f (σ : FourPerm) := if J.map σ.toEmbedding = I then realSignedWeight U σ else 0
  have hevent (p : Fin 24) : correctionEvent r k p =
      if J.map (fourPerm p).symm.toEmbedding = I then 1 else 0 := by
    change ((if J.map (fourPerm p).symm.toEmbedding = I then 1 else 0 : ℤ) : ℝ) = _
    by_cases h : J.map (fourPerm p).symm.toEmbedding = I
    · simp only [if_pos h, Int.cast_one]
    · simp only [if_neg h, Int.cast_zero]
  change (∑ p, realSignedWeight U (fourPerm p).symm * correctionEvent r k p) =
    subsetMinorSq U I J
  simp only [hevent, mul_ite, mul_one, mul_zero]
  change (∑ p, f (e p)) = subsetMinorSq U I J
  rw [Equiv.sum_comp e f]
  simpa only [f, realSignedWeight, Finset.sum_filter, Complex.re_sum, apply_ite,
    Complex.ofReal_re, Complex.zero_re] using
    congrArg Complex.re (sum_signedWeight_image_eq_subsetMinorSq U hU I J)

/-- For each mixed ray, permute the rows and columns so that the signed minor
correction equals the negative of the ray value. -/
theorem fourSignedMinorCorrection_relabel (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (r : Fin 48) :
    ∃ eRow eCol : FourPerm, fourSignedMinorCorrection (U.submatrix eRow eCol) =
      -fourSupportCostValue U (mixedCostRay r) := by
  refine ⟨correctionRows r, correctionColumns r, ?_⟩
  rw [fourSignedMinorCorrection_eq_minors _ (unitary_reindex _ _ hU)]
  have h := congrArg (fourSupportCostValue U) (correctionEvent_profile r)
  simpa only [map_neg, map_sub, correctionEvent_value U hU] using h.symm

/-- The order-four conjecture is equivalent to its restriction to unitaries
with positive signed minor correction. -/
theorem conjecture_four_iff_positive_signed_minor :
    Conjecture (Fin 4) ↔ ∀ (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ),
      IsUnitary U → 0 < fourSignedMinorCorrection U → Holds a b U := by
  constructor
  · intro h a b U hU _
    exact h a b U hU
  · intro h a b U hU
    by_cases hn : ∃ r : Fin 48, fourSupportCostValue U (mixedCostRay r) < 0
    · obtain ⟨r, hr⟩ := hn
      obtain ⟨eRow, eCol, he⟩ := fourSignedMinorCorrection_relabel U hU r
      apply (holds_reindex_iff eRow eCol a b U).mp
      exact h _ _ _ (unitary_reindex _ _ hU) (he.symm ▸ neg_pos.mpr hr)
    · exact four_holds_of_nonnegative_mixed_rays a b U hU
        (fun r => le_of_not_gt (fun hr => hn ⟨r, hr⟩))

end

end MOC
