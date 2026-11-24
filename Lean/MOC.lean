import MOC.AffineContactStep
import MOC.AffineContactCurve
import MOC.BalancedContactReduction
import MOC.AnchorMinorGram
import MOC.Claim
import MOC.CollinearKernelSupport
import MOC.CommonLawTransport
import MOC.ConnectedContactStep
import MOC.ContactCrossRatios
import MOC.ContactCurveGeometry
import MOC.ContactCurveStep
import MOC.ContactFibreGluing
import MOC.ContactIteration
import MOC.ContactSubsetObstruction
import MOC.ContactTransfer
import MOC.ContactWeightPositivity
import MOC.DisjointContactRectangle
import MOC.DiskBoundary
import MOC.ExtendedCases
import MOC.FiniteCurveClosure
import MOC.FiniteCurveCofiniteImage
import MOC.FiniteCurveConnected
import MOC.FiniteCurveFiberSeparation
import MOC.FiniteCurveBranchValues
import MOC.FiniteCurveAffineConnected
import MOC.FiniteCurveGrowth
import MOC.FiniteCurvePlaneImage
import MOC.FiniteCurvePrimitiveCoordinate
import MOC.FiniteCurveProperProjection
import MOC.FiniteCurveRootCover
import MOC.FiveMatchingLaw
import MOC.FiveParityCorrection
import MOC.FourCommonShift
import MOC.FourContactCertificate
import MOC.FourEquilateral
import MOC.FourNonrealReduction
import MOC.FourParityCorrection
import MOC.FourQuaternionMinor
import MOC.FourZeroDiagonal
import MOC.FullSupportReduction
import MOC.FullFlagLaw
import MOC.GaussianCayley
import MOC.GlobalContactSlice
import MOC.GroupedPencil
import MOC.GeneralContactReduction
import MOC.Geometry
import MOC.HermitianByNormalFour
import MOC.HermitianByNormalGeneral
import MOC.HermitianSpectralLine
import MOC.HermitianStationarySwap
import MOC.HomotheticMinorFacet
import MOC.HouseholderSupport
import MOC.IdentityPadding
import MOC.KrullHeightChain
import MOC.LexicographicScores
import MOC.MarkedPadding
import MOC.MatchingProfileClosed
import MOC.MatchingRectangleSupport
import MOC.MobiusStationarity
import MOC.PolynomialEvaluationHeight
import MOC.PositiveTwoOutlierBlock
import MOC.SpectralTwoOutlierComparison
import MOC.TwoOutlierChainObstruction
import MOC.TwoOutlierMinorCertificate
import MOC.NestedContactObjective
import MOC.NestedRectangleObstruction
import MOC.NormalSupportMaximum
import MOC.Obstruction
import MOC.OppositePair
import MOC.OppositePairNormal
import MOC.OrderFiveContact
import MOC.OrderFiveCommonLawObstruction
import MOC.OrderFivePairCost
import MOC.OrderFivePairMarkers
import MOC.OrderFiveSparseGeometry
import MOC.OrderFiveZeroCorner
import MOC.OrderFourGivens
import MOC.OrderFourFlatPlanes
import MOC.OrderFourColumnReflections
import MOC.OrderFourIndependent
import MOC.PhaseHessianReduction
import MOC.OrderFourReflectionTest
import MOC.OrderFourReflectionResidue
import MOC.OrderFourSecondVariation
import MOC.PairAssignmentObstruction
import MOC.Pencil
import MOC.PairRayleigh
import MOC.PolydiskContact
import MOC.PositiveWeightMargin
import MOC.ProjectiveTransport
import MOC.ProofRoutes
import MOC.ProfileDimension
import MOC.QuaternionParitySharp
import MOC.QuaternionBinaryBasis
import MOC.QuaternionIntrinsic
import MOC.QuaternionIdenticalSpectra
import MOC.QuaternionMixerParity
import MOC.QuaternionBinaryNormalize
import MOC.RankTwoOverlap
import MOC.RadialExternalCertificates
import MOC.RealizableContactConsequences
import MOC.RealizableContactKernels
import MOC.ReciprocalConjugateSupport
import MOC.Reformulations
import MOC.SchurEntryObstruction
import MOC.SchurQuadraticSupport
import MOC.SixContactBridge
import MOC.Source
import MOC.SparseRow
import MOC.SparseSpectralCollision
import MOC.SpectralAffineContact
import MOC.SpectralGramNeighborhood
import MOC.SpectralMinorDecomposition
import MOC.SpectralZeroPadding
import MOC.StationaryFullSupport
import MOC.StationaryDenseCross
import MOC.SubsetAssignmentSupport
import MOC.SubsetMarkerTest
import MOC.ThreeValues
import MOC.Transfer
import MOC.TrianglePairContacts
import MOC.TriangleRectangleContact
import MOC.TripleFibreAmbient
import MOC.TripleFibreContact
import MOC.TropicalSupport
import MOC.TwoCircleCover
import MOC.TwoFreeRealAnchors
import MOC.WeightedDiamondAdjacency
import MOC.WeightedMinor
import MOC.ZeroHeightTriangleClosure

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
