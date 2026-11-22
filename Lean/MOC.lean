import MOC.Claim
import MOC.CollinearKernelSupport
import MOC.DiskBoundary
import MOC.ExtendedCases
import MOC.FourCentralSymmetry
import MOC.FourCommonShift
import MOC.FourEquilateral
import MOC.Geometry
import MOC.HermitianByNormalGeneral
import MOC.HermitianLineCertificate
import MOC.HermitianSpectralLine
import MOC.HouseholderSupport
import MOC.IdentityPadding
import MOC.NormalSupportMaximum
import MOC.Obstruction
import MOC.OppositePair
import MOC.OppositePairNormal
import MOC.PolydiskContact
import MOC.RankTwoOverlap
import MOC.SparseRow
import MOC.SpectralAffineContact
import MOC.ThreeValues
import MOC.WeightedDiamondCensus

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut checked : CollectAxioms.State := {}
  for (name, declaration) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`MOC).isPrefixOf env.allImportedModuleNames[idx.toNat]! do continue
    -- Code generation adds unsafe auxiliary declarations to the imported environment.
    if declaration.isUnsafe then continue
    count := count + 1
    let (_, next) := ((CollectAxioms.collect name).run env).run checked
    let extra := next.axioms.filter fun a => !allowed.contains a
    unless extra.isEmpty do
      throwError "{name} depends on unapproved axioms {extra}"
    checked := next
  if count == 0 then
    throwError "The MOC axiom audit found no declarations"
  logInfo m!"Checked {count} safe MOC declarations against the standard Lean axioms"
