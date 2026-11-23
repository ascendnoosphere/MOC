import MOC.FiveSharedAnchorsCertificate
import MOC.CommonWeights
import MOC.LiftedSimplex

/-! Four shared signed eigenvalues have harmonic cross ratio.
The two remaining complex eigenvalues vary independently. -/

open BigOperators Matrix

namespace MOC.FiveSharedAnchors

set_option maxRecDepth 32000
set_option maxHeartbeats 12000000

noncomputable section

/-- The first four marks are 0, 2, 3 and 6. -/
def left (x : ℂ) : Fin 5 → ℂ := Function.update (fun i => (firstMarks i : ℂ)) 4 x

/-- The first four entries are the negatives of the shared marks. -/
def right (y : ℂ) : Fin 5 → ℂ := Function.update (fun i => (secondMarks i : ℂ)) 4 y

private def basis (x y : ℂ) : Fin 5 → ℂ :=
  ![0, (1-x)*(1-y), (1-x)*y, x*(1-y), x*y]

private theorem corner_eq (p : Label) (x y : ℤ) :
    (corner p x y : ℂ) = matchingProduct (left x) (right y) p := by
  simp only [corner, matchingProduct, Int.cast_prod, Int.cast_add]
  apply Finset.prod_congr rfl
  intro j _
  have update_cast (v : Fin 5 → ℤ) (t : ℤ) (k : Fin 5) :
      (Function.update v 4 t k : ℂ) = Function.update (fun l => (v l : ℂ)) 4 (t : ℂ) k := by
    by_cases hk : k = 4
    · subst k
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hk]
  simp only [left, right, update_cast]

private theorem swap_product (a b : Fin 5 → ℂ) (p : Label) :
    matchingProduct b a p.symm = matchingProduct a b p := by
  rw [matchingProduct_inverse]
  simp [matchingProduct, add_comm]

private theorem product_eq (x y : ℂ) (p : Label) :
    matchingProduct (left x) (right y) p =
      ∑ k, (point p k : ℂ) * basis x y k := by
  have hu (v : ℂ) : matchingProduct (left x) (right v) p =
      matchingProduct (left 0) (right v) p +
      (matchingProduct (left 1) (right v) p - matchingProduct (left 0) (right v) p) * x := by
    have h := matching_update_interp (right v) (fun i => (firstMarks i : ℂ)) 4 p.symm x
    change matchingProduct (right v) (left x) p.symm =
      matchingProduct (right v) (left 0) p.symm +
      (matchingProduct (right v) (left 1) p.symm -
        matchingProduct (right v) (left 0) p.symm) * x at h
    simpa only [swap_product] using h
  have hy := matching_update_interp (left x) (fun i => (secondMarks i : ℂ)) 4 p y
  change matchingProduct (left x) (right y) p = matchingProduct (left x) (right 0) p +
    (matchingProduct (left x) (right 1) p - matchingProduct (left x) (right 0) p) * y at hy
  rw [hy, hu 0, hu 1]
  simp [Fin.sum_univ_succ, point, basis, corner_eq]
  ring

private def certificate : LiftedSimplexCertificate (Fin 5) Label (Fin 5) Cell Facet Term where
  index := Equiv.refl Label
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
    let F := fun q => matchingProduct (left x)
      (right y) q
    ∑ j, (bary t j p : ℂ) * F (vertex t j) = (denominator t : ℂ) * F p := by
  dsimp only
  simp_rw [product_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 1
  exact_mod_cast reconstruct t p k

/-- One probability law works for every pair of free entries at a fixed unitary. -/
theorem exists_common_law (U : Matrix (Fin 5) (Fin 5) ℂ) (hU : IsUnitary U) :
    ∃ (σ : Fin 5 → Label) (w : Fin 5 → ℝ), (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ x y : ℂ, ∑ j, (w j : ℂ) * matchingProduct (left x)
        (right y) (σ j) =
          determinantValue (left x) (right y) U := by
  obtain ⟨t, w, hw, hs, h⟩ := certificate.exists_law U hU
  refine ⟨vertex t, w, hw, hs, ?_⟩
  intro x y
  exact (h (matchingProduct (left x) (right y)) (row_match x y t)).trans
    (real_signed_determinant (left x) (right y) U hU)

/-- Four shared harmonic marks give the determinant hull inclusion for all
relative unitaries and all choices of the last two eigenvalues. -/
theorem holds (x y : ℂ) (U : Matrix (Fin 5) (Fin 5) ℂ)
    (hU : IsUnitary U) : Holds (left x) (right y) U := by
  obtain ⟨σ, w, hw, hsum, h⟩ := exists_common_law U hU
  unfold Holds
  refine mem_convexHull_of_exists_fintype w _ hw hsum (fun j => ⟨σ j, rfl⟩) ?_
  simpa only [Complex.real_smul] using h x y

end
end MOC.FiveSharedAnchors
