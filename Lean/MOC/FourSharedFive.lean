import MOC.FourSharedFiveCone
import MOC.FourSharedFiveMatching
import MOC.FourSharedFiveMinors
import MOC.FiveMatchingLaw

/-! A common probability law for every order-five pair with four shared signed marks. -/

open BigOperators Matrix

namespace MOC.FourSharedFive

noncomputable section

private theorem point_zero : ∀ i : Fin 51, point i 0 = 1 := by decide +kernel

private theorem label_surjective : Function.Surjective labelPoint := by
  change ∀ i : Fin 51, ∃ p : Fin 120, labelPoint p = i
  decide +kernel

/-- At a fixed unitary, the law does not depend on any of the six complex marks. -/
theorem exists_common_law (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    ∃ w : Fin 120 → ℝ, (∀ p, 0 ≤ w p) ∧ (∑ p, w p = 1) ∧
      ∀ z : Fin 6 → ℂ, ∑ p, (w p : ℂ) *
        matchingProduct (left z) (right z) (FivePermutations.perm p) =
          determinantValue (left z) (right z) U :=
  FiveMatchingLaw.exists_common_law 0 point labelPoint finalRay point_zero label_surjective
    exists_ray_weights left right basis matching_eq U hU (signed_ray_nonneg U hU)

/-- Four common signed marks give the determinant inclusion for every relative unitary. -/
theorem holds (z : Fin 6 → ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : IsUnitary U) : Holds (left z) (right z) U := by
  obtain ⟨w, hw, hm, he⟩ := exists_common_law U hU
  unfold Holds
  refine mem_convexHull_of_exists_fintype w _ hw hm
    (fun p => ⟨FivePermutations.perm p, rfl⟩) ?_
  simpa only [Complex.real_smul] using he z

end
end MOC.FourSharedFive
