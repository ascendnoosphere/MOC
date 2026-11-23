import MOC.WeightedDiamondComplete
import MOC.FourNonrealReduction

/-! Circle and line cases that follow from the order-four Hermitian-by-normal theorem. -/

open Matrix

namespace MOC

/-- In order four, either spectrum can lie on a circle or a line. -/
theorem holds_four_of_generalized_circle (a b : Fin 4 → ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) (hc : SpectrumOnGeneralizedCircle a ∨ SpectrumOnGeneralizedCircle b) :
    Holds a b U :=
  FourNonrealReduction.holds_four_on_circle hermitianByNormal_four a b U hU hc

/-- At most four nonreal partner entries suffice in every order. Count entries with multiplicity. -/
theorem hermitianByNormalAtMost_four (n : ℕ) : HermitianByNormalAtMost (Fin n) 4 :=
  FourNonrealReduction.at_most_four hermitianByNormal_four n

/-- Up to four entries of the negated partner spectrum may lie outside the first circle or line. -/
theorem holds_of_common_generalized_circle_with_four_outliers {n : ℕ}
    (a b : Fin n → ℂ) (outliers : Finset (Fin n)) (hcard : outliers.card ≤ 4)
    (hc : SpectrumOnGeneralizedCircle
      (Sum.elim a (fun i : {i // i ∉ outliers} => -b i.val)))
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : IsUnitary U) : Holds a b U :=
  FourNonrealReduction.holds_with_four_outliers hermitianByNormal_four a b outliers hcard hc U hU

/-- In order five, one reflected partner entry on the circle or line suffices. -/
theorem holds_five_of_common_generalized_circle_contact (a b : Fin 5 → ℂ) (j : Fin 5)
    (hc : SpectrumOnGeneralizedCircle (Sum.elim a (fun _ : Unit => -b j)))
    (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) : Holds a b U :=
  FourNonrealReduction.holds_five_with_contact hermitianByNormal_four a b j hc U hU

end MOC
