import MOC.GrassmannianUnitaryAction
import MOC.GrassmannianUnitaryLift
import MOC.OrderFivePairCost

/-! The order-five support bound as a quadratic objective on isometric
linear preservers of the decomposable bivectors. -/

open BigOperators Matrix

namespace MOC

noncomputable section

local notation "Pair₅" => SubsetLayer (Fin 5) 2

private def pairEndpoints (I : Pair₅) : {p : Fin 5 × Fin 5 // p.1 ≠ p.2 ∧ I.val = {p.1, p.2}} :=
  Classical.choice (by
    obtain ⟨i, j, h, hj⟩ := Finset.card_eq_two.mp I.property
    exact ⟨⟨(i, j), h, hj⟩⟩)

/-- The coordinate of the image of the column pair in the row pair.
Either orientation of either pair gives the same squared modulus. -/
def orderFiveGrassmannianEntry (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace)
    (I J : Pair₅) : ℂ :=
  (W (bivectorSkew (grassmannianBasisVector (pairEndpoints J).val.1)
    (grassmannianBasisVector (pairEndpoints J).val.2)) : GrassmannianMatrix)
    (pairEndpoints I).val.1 (pairEndpoints I).val.2

private theorem orderFiveGrassmannianEntry_normSq
    (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace) (U : GrassmannianMatrix) (hU : IsUnitary U)
    (hW : ∀ x y : GrassmannianVector,
      (W (bivectorSkew x y) : GrassmannianMatrix) = bivectorMatrix (U *ᵥ x) (U *ᵥ y))
    (I J : Pair₅) : Complex.normSq (orderFiveGrassmannianEntry W I J) = subsetMinorSq U I.val J.val := by
  let i := (pairEndpoints I).val.1
  let k := (pairEndpoints I).val.2
  let j := (pairEndpoints J).val.1
  let l := (pairEndpoints J).val.2
  have hI : I.val = {i, k} := (pairEndpoints I).property.2
  have hJ : J.val = {j, l} := (pairEndpoints J).property.2
  change Complex.normSq ((W (bivectorSkew (grassmannianBasisVector j) (grassmannianBasisVector l)) :
    GrassmannianMatrix) i k) = _
  rw [hW, hI, hJ, subsetMinorSq_pair U hU (pairEndpoints I).property.1 (pairEndpoints J).property.1]
  simp only [grassmannianBasisVector, Matrix.mulVec_single_one, Matrix.col_apply, bivectorMatrix]
    <;> congr 1 <;> ring

private theorem orderFive_support_eq_grassmannian (a b : Fin 5 → ℂ) (η : ℂ)
    (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace) (U : GrassmannianMatrix) (hU : IsUnitary U)
    (hW : ∀ x y : GrassmannianVector,
      (W (bivectorSkew x y) : GrassmannianMatrix) = bivectorMatrix (U *ᵥ x) (U *ᵥ y)) :
    (η * determinantValue a b U).re = orderFivePairOffset a b η +
      ∑ J : Pair₅, ∑ I : Pair₅, orderFivePairCost a b η I J *
        Complex.normSq (orderFiveGrassmannianEntry W I J) := by
  rw [orderFive_determinant_support_eq_pair_cost a b η U hU]
  simp only [orderFiveGrassmannianEntry_normSq W U hU hW]

/-- The order-five support problem is a quadratic bound on the
isometric preservers of the decomposable bivectors. -/
def OrderFiveGrassmannianSupport : Prop :=
  ∀ (a b : Fin 5 → ℂ) (η : ℂ) (W : bivectorSkewSpace ≃ₗ[ℂ] bivectorSkewSpace),
    (∀ A : bivectorSkewSpace, PluckerBivector (A : GrassmannianMatrix) →
      PluckerBivector (W A : GrassmannianMatrix)) →
    (∀ A B : bivectorSkewSpace, bivectorMatrixPair (W A) (W B) = bivectorMatrixPair A B) →
    ∃ σ : Equiv.Perm (Fin 5),
      orderFivePairOffset a b η + (∑ J : Pair₅, ∑ I : Pair₅,
        orderFivePairCost a b η I J * Complex.normSq (orderFiveGrassmannianEntry W I J)) ≤
      (η * matchingProduct a b σ).re

/-- The Grassmannian support problem is equivalent to unrestricted
Marcus–de Oliveira in order five. -/
theorem conjecture_five_iff_grassmannian_support :
    Conjecture (Fin 5) ↔ OrderFiveGrassmannianSupport := by
  constructor
  · intro h a b η W hP hpair
    obtain ⟨U, hU, hW⟩ := exists_unitary_of_grassmannian_preserver W hP hpair
    obtain ⟨σ, hs⟩ := (holds_iff_directional a b U).mp (h a b U hU) η
    refine ⟨σ, ?_⟩
    rw [← orderFive_support_eq_grassmannian a b η W U hU hW]
    exact hs
  · intro h a b U hU
    obtain ⟨W, hP, hpair, hW⟩ := exists_grassmannian_preserver_of_unitary U hU
    apply (holds_iff_directional a b U).mpr
    intro η
    obtain ⟨σ, hs⟩ := h a b η W hP hpair
    exact ⟨σ, (orderFive_support_eq_grassmannian a b η W U hU hW).le.trans hs⟩

end

end MOC
