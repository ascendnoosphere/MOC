import MOC.AffineContactStep
import MOC.AnchorMinorGram
import MOC.Claim
import MOC.CollinearKernelSupport
import MOC.CommonLawTransport
import MOC.ContactCurveGeometry
import MOC.ContactCurveStep
import MOC.ContactIteration
import MOC.ContactTransfer
import MOC.ContactWeightPositivity
import MOC.DisjointContactRectangle
import MOC.DiskBoundary
import MOC.ExtendedCases
import MOC.FiniteCurvePlaneImage
import MOC.FiveMatchingLaw
import MOC.FourCommonShift
import MOC.FourContactCertificate
import MOC.FourEquilateral
import MOC.FourNonrealReduction
import MOC.FourQuaternionMinor
import MOC.FullSupportReduction
import MOC.GeneralContactReduction
import MOC.Geometry
import MOC.HermitianByNormalFour
import MOC.HermitianByNormalGeneral
import MOC.HermitianSpectralLine
import MOC.HermitianStationarySwap
import MOC.HomotheticMinorFacet
import MOC.HouseholderSupport
import MOC.IdentityPadding
import MOC.LexicographicScores
import MOC.MarkedPadding
import MOC.MatchingProfileClosed
import MOC.MatchingRectangleSupport
import MOC.MobiusStationarity
import MOC.NestedContactObjective
import MOC.NormalSupportMaximum
import MOC.Obstruction
import MOC.OppositePair
import MOC.OppositePairNormal
import MOC.OrderFiveContact
import MOC.OrderFivePairMarkers
import MOC.OrderFourIndependent
import MOC.OrderFourReflectionTest
import MOC.OrderFourSecondVariation
import MOC.Pencil
import MOC.PolydiskContact
import MOC.PositiveWeightMargin
import MOC.ProjectiveTransport
import MOC.RankTwoOverlap
import MOC.RealizableContactConsequences
import MOC.RealizableContactKernels
import MOC.Reformulations
import MOC.SchurEntryObstruction
import MOC.SchurQuadraticSupport
import MOC.Source
import MOC.SparseRow
import MOC.StationaryFullSupport
import MOC.SpectralAffineContact
import MOC.SpectralMinorDecomposition
import MOC.SpectralZeroPadding
import MOC.SubsetMarkerTest
import MOC.ThreeValues
import MOC.Transfer
import MOC.TripleFibreContact
import MOC.TrianglePairContacts
import MOC.TriangleRectangleContact
import MOC.TwoCircleCover
import MOC.TwoFreeRealAnchors
import MOC.WeightedDiamondAdjacency
import MOC.WeightedMinor

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
