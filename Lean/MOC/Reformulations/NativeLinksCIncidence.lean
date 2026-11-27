import MOC.Claim
import Mathlib.LinearAlgebra.Matrix.Block

/-! For incidence algebras, a relative position that preserves triangular form has exactly a
matching product as determinant. This is a structural triangular proof,
not a claim about arbitrary nonnormal conjugates or a proof of MOC. -/

open BigOperators Matrix
namespace MOC.Reformulations

/-- Native triangular incidence-algebra comparison. The conjugated matrix
is denoted by `C`; the hypotheses are the exact properties of that
conjugate used, so this also applies when no conjugator is specified. -/
theorem incidenceTriangle_det_mem_matchingHull {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.BlockTriangular id) (hC : C.BlockTriangular id)
    (π : Equiv.Perm (Fin n)) (hdiag : ∀ i, C i i = B (π i) (π i)) :
    (A+C).det ∈ convexHull ℝ
      (Set.range (matchingProduct (fun i => A i i) (fun j => B j j))) := by
  apply subset_convexHull ℝ _
  refine ⟨π.symm, ?_⟩
  rw [Matrix.det_of_upperTriangular (hA.add hC)]
  calc
    matchingProduct (fun i => A i i) (fun j => B j j) π.symm =
        ∏ i, (A i i + B (π i) (π i)) := by
      unfold matchingProduct
      simpa using (Equiv.prod_comp π (fun j => A (π.symm j) (π.symm j) + B j j)).symm
    _ = ∏ i, (A+C) i i := by simp [Matrix.add_apply, hdiag]

end MOC.Reformulations
