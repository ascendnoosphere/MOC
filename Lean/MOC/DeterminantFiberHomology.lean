import MOC.HermitianDeterminantFibers
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Data.Set.Card

/-! Zeroth singular homology of an exact two-point determinant fiber. -/

open CategoryTheory CategoryTheory.Limits Matrix

namespace MOC

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- With integral coefficients, the zeroth singular homology of a
two-point determinant fiber is free of rank two. -/
theorem determinantOrbitFiber_H0_of_two_points (a b : ι → ℂ) (z : ℂ)
    (h : ∃ C D : Matrix ι ι ℂ, C ≠ D ∧ determinantOrbitFiber a b z = {C, D}) :
    Nonempty ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (determinantOrbitFiber a b z))) ≅
        ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  obtain ⟨C, D, hne, heq⟩ := h
  let S := determinantOrbitFiber a b z
  have hfinite : S.Finite := by
    change (determinantOrbitFiber a b z).Finite
    rw [heq]
    exact (Set.finite_singleton D).insert C
  letI : Finite S := hfinite.to_subtype
  letI : DiscreteTopology S := Finite.instDiscreteTopology
  have hc : Nat.card S = 2 := by
    change Nat.card (determinantOrbitFiber a b z) = 2
    rw [Set.Nat.card_coe_set_eq, heq, Set.ncard_pair hne]
  let e : S ≃ Fin 2 := Finite.equivFinOfCardEq hc
  let T : TopCat := TopCat.of S
  letI : TotallyDisconnectedSpace T := inferInstanceAs (TotallyDisconnectedSpace S)
  let g (_ : S) : ModuleCat ℤ := ModuleCat.of ℤ ℤ
  let h₀ := AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) T
  exact ⟨h₀ ≪≫ (biproduct.isoCoproduct g).symm ≪≫ ModuleCat.biproductIsoPi g ≪≫
    (LinearEquiv.funCongrLeft ℤ ℤ e.symm).toModuleIso⟩

end MOC
