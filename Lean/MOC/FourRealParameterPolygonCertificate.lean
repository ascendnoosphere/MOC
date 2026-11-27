import MOC.FourRealParameterCellData

set_option Elab.async false

open BigOperators Matrix Polynomial
open scoped Polynomial MOC.RealParameterCertificate.Univariate
open MOC.RealParameterCertificate (Univariate)

namespace MOC.FourRealParameterCellCertificate

set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem compactPolygon_check (k : Fin 89) :
    let p := compactPolygon k.val
    0 < p.size ∧ ∀ i : Fin p.size,
      p.next (p.prev i) = i ∧ p.facets i < 107 ∧
      (compactFacet (p.facets i)).left = p.label i ∧
      (compactFacet (p.facets i)).right = p.label (p.next i) ∧
      0 < (p.turns i).content ∧ (p.turns i).squared = [] ∧
      Univariate.same (compactTurnPolynomial p i)
        (cellWeightPolynomial compactFactorData (p.turns i)) = true := by
  fin_cases k <;> decide +kernel

end MOC.FourRealParameterCellCertificate
