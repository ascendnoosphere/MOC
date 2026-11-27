import MOC.FourRealParameterCellData

set_option Elab.async false

open BigOperators Matrix Polynomial
open scoped Polynomial MOC.RealParameterCertificate.Univariate
open MOC.RealParameterCertificate (Univariate)

namespace MOC.FourRealParameterCellCertificate

set_option maxRecDepth 20000 in
set_option maxHeartbeats 9000000 in
theorem compactBandSignFrom0 (i : Fin 44) (negative : Bool) :
    compactBandSignValid ⟨i.val + 0, by have := i.isLt; omega⟩ negative = true := by
  fin_cases i <;> cases negative <;> decide +kernel

end MOC.FourRealParameterCellCertificate
