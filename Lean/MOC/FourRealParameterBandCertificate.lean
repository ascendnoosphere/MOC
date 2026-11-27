import MOC.FourRealParameterCellData

set_option Elab.async false

open BigOperators Matrix Polynomial
open scoped Polynomial MOC.RealParameterCertificate.Univariate
open MOC.RealParameterCertificate (Univariate)

namespace MOC.FourRealParameterCellCertificate

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem compactBand_check (i : Fin 173) (negative : Bool) :
    let b := compactBandData i
    0 < b.den ∧ b.chart negative < 89 ∧ ∃ j, factorQuartic compactFactorData b.guard j ≠ 0 := by
  fin_cases i <;> cases negative <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem compactBands_adjacent (i : Fin 172) :
    (compactBandData i.castSucc).right = (compactBandData i.succ).left := by
  fin_cases i <;> decide +kernel

theorem compactBand_zero : (compactBandData 0).left = 0 := by decide +kernel

theorem compactBand_one : (compactBandData 172).right = 1 := by decide +kernel

end MOC.FourRealParameterCellCertificate
