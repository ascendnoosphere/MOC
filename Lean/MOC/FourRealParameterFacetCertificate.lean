import MOC.FourRealParameterCellData

set_option Elab.async false

open BigOperators Matrix Polynomial
open scoped Polynomial MOC.RealParameterCertificate.Univariate
open MOC.RealParameterCertificate (Univariate)

namespace MOC.FourRealParameterCellCertificate

set_option maxRecDepth 20000 in
set_option maxHeartbeats 24000000 in
theorem compactFacetValid_true (f : Fin 107) : compactFacetValid f = true := by
  fin_cases f <;> decide +kernel

theorem compactFacet_check (x : ℝ) (f : Fin 107) (p : Equiv.Perm (Fin 4)) :
    cellEval x (compactFacetPolynomial (compactFacet f.val) p) =
      cellEval x (compactFacetMinorPolynomial (compactFacet f.val) p) := by
  obtain ⟨j, hj⟩ := fourPerm_surjective p.symm
  have hp : p = (fourPerm j).symm := by rw [hj, Equiv.symm_symm]
  rw [hp]
  have h : checkAll (fun j : Fin 24 =>
    Univariate.same (compactFacetPolynomial (compactFacet f.val) (fourPerm j).symm)
      (compactFacetMinorPolynomial (compactFacet f.val) (fourPerm j).symm)) = true :=
    compactFacetValid_true f
  exact Univariate.eval_eq x (checkAll_at h j)

end MOC.FourRealParameterCellCertificate
