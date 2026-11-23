import MOC.DoubleAntipodalCertificate
import MOC.LiftedSimplex

/-! A common law for two centrally symmetric complex spectra when the second
spectrum is twice the first. The certificate uses five matching products. -/

open BigOperators Matrix

namespace MOC

/-- Two pairs of opposite points in the complex plane. -/
def antipodalQuadruple (x y : ℂ) : Fin 4 → ℂ := ![x, -x, y, -y]

namespace DoubleAntipodalCertificate

noncomputable section

private def monomial (x y : ℂ) : Fin 5 → ℂ := ![x^4, x^3*y, x^2*y^2, x*y^3, y^4]

private theorem product_eq (x y : ℂ) (p : Label) :
    matchingProduct (antipodalQuadruple x y) (fun i => 2 * antipodalQuadruple x y i)
      (fourPerm p) = ∑ k, (coeff p k : ℂ) * monomial x y k := by
  fin_cases p <;> simp only [matchingProduct, Fin.prod_univ_four, Fin.sum_univ_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  · change (x + 2 * x) * ((-x) + 2 * (-x)) * (y + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((0 : ℤ) : ℂ) * (x^3*y) + (((81 : ℤ) : ℂ) * (x^2*y^2) + (((0 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * ((-x) + 2 * (-x)) * ((-y) + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((0 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((0 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * (y + 2 * (-x)) * ((-x) + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-18 : ℤ) : ℂ) * (x^3*y) + (((45 : ℤ) : ℂ) * (x^2*y^2) + (((-18 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * (y + 2 * (-x)) * ((-y) + 2 * y) * ((-x) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((-6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * ((-y) + 2 * (-x)) * ((-x) + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (x + 2 * x) * ((-y) + 2 * (-x)) * (y + 2 * y) * ((-x) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((18 : ℤ) : ℂ) * (x^3*y) + (((45 : ℤ) : ℂ) * (x^2*y^2) + (((18 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * (x + 2 * (-x)) * (y + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((0 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((0 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * (x + 2 * (-x)) * ((-y) + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((0 : ℤ) : ℂ) * (x^3*y) + (((1 : ℤ) : ℂ) * (x^2*y^2) + (((0 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * (y + 2 * (-x)) * (x + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((-6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * (y + 2 * (-x)) * ((-y) + 2 * y) * (x + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-2 : ℤ) : ℂ) * (x^3*y) + (((5 : ℤ) : ℂ) * (x^2*y^2) + (((-2 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * ((-y) + 2 * (-x)) * (x + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((2 : ℤ) : ℂ) * (x^3*y) + (((5 : ℤ) : ℂ) * (x^2*y^2) + (((2 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-x) + 2 * x) * ((-y) + 2 * (-x)) * (y + 2 * y) * (x + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * (x + 2 * (-x)) * ((-x) + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * (x + 2 * (-x)) * ((-y) + 2 * y) * ((-x) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((2 : ℤ) : ℂ) * (x^3*y) + (((5 : ℤ) : ℂ) * (x^2*y^2) + (((2 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * ((-x) + 2 * (-x)) * (x + 2 * y) * ((-y) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((18 : ℤ) : ℂ) * (x^3*y) + (((45 : ℤ) : ℂ) * (x^2*y^2) + (((18 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * ((-x) + 2 * (-x)) * ((-y) + 2 * y) * (x + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * ((-y) + 2 * (-x)) * (x + 2 * y) * ((-x) + 2 * (-y)) =
      ((4 : ℤ) : ℂ) * x^4 + (((20 : ℤ) : ℂ) * (x^3*y) + (((33 : ℤ) : ℂ) * (x^2*y^2) + (((20 : ℤ) : ℂ) * (x*y^3) + (((4 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change (y + 2 * x) * ((-y) + 2 * (-x)) * ((-x) + 2 * y) * (x + 2 * (-y)) =
      ((4 : ℤ) : ℂ) * x^4 + (((-12 : ℤ) : ℂ) * (x^3*y) + (((1 : ℤ) : ℂ) * (x^2*y^2) + (((12 : ℤ) : ℂ) * (x*y^3) + (((4 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * (x + 2 * (-x)) * ((-x) + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-2 : ℤ) : ℂ) * (x^3*y) + (((5 : ℤ) : ℂ) * (x^2*y^2) + (((-2 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * (x + 2 * (-x)) * (y + 2 * y) * ((-x) + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((-6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * ((-x) + 2 * (-x)) * (x + 2 * y) * (y + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((6 : ℤ) : ℂ) * (x^3*y) + (((9 : ℤ) : ℂ) * (x^2*y^2) + (((-6 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * ((-x) + 2 * (-x)) * (y + 2 * y) * (x + 2 * (-y)) =
      ((0 : ℤ) : ℂ) * x^4 + (((-18 : ℤ) : ℂ) * (x^3*y) + (((45 : ℤ) : ℂ) * (x^2*y^2) + (((-18 : ℤ) : ℂ) * (x*y^3) + (((0 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * (y + 2 * (-x)) * (x + 2 * y) * ((-x) + 2 * (-y)) =
      ((4 : ℤ) : ℂ) * x^4 + (((12 : ℤ) : ℂ) * (x^3*y) + (((1 : ℤ) : ℂ) * (x^2*y^2) + (((-12 : ℤ) : ℂ) * (x*y^3) + (((4 : ℤ) : ℂ) * y^4))))
    push_cast
    ring
  · change ((-y) + 2 * x) * (y + 2 * (-x)) * ((-x) + 2 * y) * (x + 2 * (-y)) =
      ((4 : ℤ) : ℂ) * x^4 + (((-20 : ℤ) : ℂ) * (x^3*y) + (((33 : ℤ) : ℂ) * (x^2*y^2) + (((-20 : ℤ) : ℂ) * (x*y^3) + (((4 : ℤ) : ℂ) * y^4))))
    push_cast
    ring

private def lawCertificate : LiftedSimplexCertificate (Fin 4) Label (Fin 5) Cell Facet Term where
  index := fourPermEquiv
  vertex := vertex
  denominator := denominator
  bary := bary
  liftValue := liftValue
  neighbor := neighbor
  face := face
  aScale := aScale
  bScale := bScale
  cScale := cScale
  slack := slack
  facetDen := facetDen
  term := term
  den_pos := den_pos
  facetDen_pos := facetDen_pos
  term_nonneg := term_nonneg
  scales_ok := scales_ok
  transition := transition
  bary_mass := bary_mass
  minor_decomposition := minor_decomposition

private theorem row_match (x y : ℂ) (t : Cell) (p : Label) :
    let F := fun q => matchingProduct (antipodalQuadruple x y)
      (fun i => 2 * antipodalQuadruple x y i) (fourPerm q)
    ∑ j, (bary t j p : ℂ) * F (vertex t j) = (denominator t : ℂ) * F p := by
  dsimp only
  simp_rw [product_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 1
  exact_mod_cast reconstruct t p k

/-- At each unitary a single simplex gives a common law for all complex axes. -/
theorem exists_doubled_law (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ (σ : Fin 5 → FourPerm) (w : Fin 5 → ℝ), (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ x y : ℂ, ∑ j, (w j : ℂ) * matchingProduct (antipodalQuadruple x y)
        (fun i => 2 * antipodalQuadruple x y i) (σ j) =
          determinantValue (antipodalQuadruple x y) (fun i => 2 * antipodalQuadruple x y i) U := by
  obtain ⟨t,w,hw,hs,hr⟩ := lawCertificate.exists_law U hU
  refine ⟨fun j => fourPerm (vertex t j), w, hw, hs, ?_⟩
  intro x y
  let F := fun p => matchingProduct (antipodalQuadruple x y)
    (fun i => 2 * antipodalQuadruple x y i) (fourPerm p)
  exact (hr F (fun p => row_match x y t p)).trans
    ((Equiv.sum_comp fourPermEquiv _).trans (real_signed_determinant _ _ U hU))

end
end DoubleAntipodalCertificate

/-- Doubling both antipodal pairs gives MOC for arbitrary complex axes and every unitary. -/
theorem holds_four_doubled_antipodal (x y : ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ)
    (hU : IsUnitary U) : Holds (antipodalQuadruple x y) (fun i => 2 * antipodalQuadruple x y i) U := by
  obtain ⟨σ, w, hw, hsum, h⟩ := DoubleAntipodalCertificate.exists_doubled_law U hU
  unfold Holds
  refine mem_convexHull_of_exists_fintype w _ hw hsum (fun j => ⟨σ j, rfl⟩) ?_
  simpa only [Complex.real_smul] using h x y

end MOC
