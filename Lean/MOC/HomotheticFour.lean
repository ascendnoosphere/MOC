import MOC.HomotheticFourCertificate

/-! A common law for homothetic pairs of antipodal spectra of order four. -/

open BigOperators Matrix

namespace MOC.HomotheticFour

/-- Two pairs of opposite complex values. -/
def spectrum (x y : ℂ) : Fin 4 → ℂ := ![x, -x, y, -y]

private def monomial (x y t : ℂ) : Fin 7 → ℂ :=
  ![x^2*y^2*(1+t^4), (x^4+y^4)*t^2, x^3*y*t+x*y^3*t^3,
    (x^3*y+x*y^3)*t^2, x^3*y*t^3+x*y^3*t, x^2*y^2*(t+t^3), x^2*y^2*t^2]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem product_eq (x y t : ℂ) (p : Label) :
    matchingProduct (spectrum x y) (fun i => t * spectrum x y i) (fourPerm p) =
      ∑ k, (coord p k : ℂ) * monomial x y t k := by
  fin_cases p <;> simp only [matchingProduct, Fin.prod_univ_four, Fin.sum_univ_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  · change (x + t * x) * ((-x) + t * (-x)) * (y + t * y) * ((-y) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((0 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((0 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((4 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((6 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (x + t * x) * ((-x) + t * (-x)) * ((-y) + t * y) * (y + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((0 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((0 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (x + t * x) * (y + t * (-x)) * ((-x) + t * y) * ((-y) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((-2 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((2 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (x + t * x) * (y + t * (-x)) * ((-y) + t * y) * ((-x) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (x + t * x) * ((-y) + t * (-x)) * ((-x) + t * y) * (y + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (x + t * x) * ((-y) + t * (-x)) * (y + t * y) * ((-x) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((2 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((2 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-x) + t * x) * (x + t * (-x)) * (y + t * y) * ((-y) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((0 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((0 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-x) + t * x) * (x + t * (-x)) * ((-y) + t * y) * (y + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((0 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((0 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((-4 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((6 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-x) + t * x) * (y + t * (-x)) * (x + t * y) * ((-y) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-x) + t * x) * (y + t * (-x)) * ((-y) + t * y) * (x + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((2 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((-2 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-x) + t * x) * ((-y) + t * (-x)) * (x + t * y) * (y + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((-2 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((-2 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-x) + t * x) * ((-y) + t * (-x)) * (y + t * y) * (x + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (y + t * x) * (x + t * (-x)) * ((-x) + t * y) * ((-y) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (y + t * x) * (x + t * (-x)) * ((-y) + t * y) * ((-x) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((-2 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((-2 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (y + t * x) * ((-x) + t * (-x)) * (x + t * y) * ((-y) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((2 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((2 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (y + t * x) * ((-x) + t * (-x)) * ((-y) + t * y) * (x + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (y + t * x) * ((-y) + t * (-x)) * (x + t * y) * ((-x) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((1 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((2 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((2 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((4 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change (y + t * x) * ((-y) + t * (-x)) * ((-x) + t * y) * (x + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((1 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((2 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-2 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-4 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-y) + t * x) * (x + t * (-x)) * ((-x) + t * y) * (y + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((2 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((-2 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-y) + t * x) * (x + t * (-x)) * (y + t * y) * ((-x) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-y) + t * x) * ((-x) + t * (-x)) * (x + t * y) * (y + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-y) + t * x) * ((-x) + t * (-x)) * (y + t * y) * (x + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((0 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((-2 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-1 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((2 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((2 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-y) + t * x) * (y + t * (-x)) * (x + t * y) * ((-x) + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((1 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-2 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((2 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((-4 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring
  · change ((-y) + t * x) * (y + t * (-x)) * ((-x) + t * y) * (x + t * (-y)) =
      ((1 : ℤ) : ℂ) * (x^2*y^2*(1+t^4)) + (((1 : ℤ) : ℂ) * ((x^4+y^4)*t^2) + (((-2 : ℤ) : ℂ) * (x^3*y*t+x*y^3*t^3) + (((0 : ℤ) : ℂ) * ((x^3*y+x*y^3)*t^2) + (((-2 : ℤ) : ℂ) * (x^3*y*t^3+x*y^3*t) + (((0 : ℤ) : ℂ) * (x^2*y^2*(t+t^3)) + (((4 : ℤ) : ℂ) * (x^2*y^2*t^2)))))))
    push_cast
    ring

private theorem row_match (x y t : ℂ) (k : Cell) (p : Label) :
    let F := fun q => matchingProduct (spectrum x y) (fun i => t * spectrum x y i) (fourPerm q)
    ∑ j, (geometry.bary k j p : ℂ) * F (vertex k j) =
      (geometry.denominator k : ℂ) * F p := by
  dsimp only
  simp_rw [product_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  congr 1
  exact_mod_cast reconstruct k p j

/-- At most seven matching products suffice. One probability law applies
to all complex axes and all complex scale factors. -/
theorem exists_homothetic_law (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    ∃ (σ : Fin 7 → FourPerm) (w : Fin 7 → ℝ), (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
      ∀ x y t : ℂ, ∑ j, (w j : ℂ) * matchingProduct (spectrum x y) (fun i => t * spectrum x y i)
        (σ j) = determinantValue (spectrum x y) (fun i => t * spectrum x y i) U := by
  obtain ⟨k,w,hw,hs,hr⟩ := LiftedSimplexCertificate.exists_law_of_nonneg geometry U hU
    (boundary_nonneg U hU)
  refine ⟨fun j => fourPerm (vertex k j), w, hw, hs, ?_⟩
  intro x y t
  let F := fun p => matchingProduct (spectrum x y) (fun i => t * spectrum x y i) (fourPerm p)
  exact (hr F (fun p => row_match x y t k p)).trans
    ((Equiv.sum_comp fourPermEquiv _).trans (real_signed_determinant _ _ U hU))

theorem holds_homothetic (x y t : ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (spectrum x y) (fun i => t * spectrum x y i) U := by
  obtain ⟨σ,w,hw,hs,h⟩ := exists_homothetic_law U hU
  unfold Holds
  refine mem_convexHull_of_exists_fintype w _ hw hs (fun j => ⟨σ j, rfl⟩) ?_
  simpa only [Complex.real_smul] using h x y t

/-- Opposite translations place the two centers at any pair of opposite points. -/
theorem holds_translated_homothetic (x y t c : ℂ)
    (U : Matrix (Fin 4) (Fin 4) ℂ) (hU : IsUnitary U) :
    Holds (fun i => spectrum x y i + c) (fun i => t * spectrum x y i - c) U :=
  (holds_shift_iff _ _ hU c).mpr (holds_homothetic x y t U hU)

end MOC.HomotheticFour
