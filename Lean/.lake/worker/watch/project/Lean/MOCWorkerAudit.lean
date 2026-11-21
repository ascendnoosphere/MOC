import MOC
import MOC.AlgebraicContact
import MOC.AnchorObstruction
import MOC.AnchoredChart
import MOC.BalancedStrongSupport
import MOC.Blocks
import MOC.CircleSpectra
import MOC.Claim
import MOC.Collinear
import MOC.CommonCommutant
import MOC.ContactCensus
import MOC.ContactRectangle
import MOC.ContactTransfer
import MOC.Core
import MOC.DruryNonreal
import MOC.DruryResolvent
import MOC.Extremal
import MOC.FourCoincidence
import MOC.FourContactCertificate
import MOC.FourContactCones
import MOC.FourEffectDecomposition
import MOC.FourMatchingHessian
import MOC.FourMatchingRelations
import MOC.FourMinorTransport
import MOC.FourRealification
import MOC.Geometry
import MOC.Hermitian
import MOC.Householder
import MOC.HouseholderFour
import MOC.HouseholderPacking
import MOC.HouseholderSupport
import MOC.Interlacing
import MOC.Jacobi
import MOC.MatchingQuartet
import MOC.MixedBound
import MOC.MobiusOrbitMinimum
import MOC.MobiusStationarity
import MOC.NestedValues
import MOC.NonnormalExtrema
import MOC.Normal
import MOC.NormalOrbit
import MOC.Obstruction
import MOC.Pencil
import MOC.PhaseMove
import MOC.PoleCompression
import MOC.RankSum
import MOC.RankTwoOverlap
import MOC.Realification
import MOC.SchurEntryObstruction
import MOC.SchurPhase
import MOC.SchurPivot
import MOC.SchurQuadraticSupport
import MOC.Singular
import MOC.Small
import MOC.Source
import MOC.SparseRow
import MOC.SpectralGap
import MOC.SpectralKKT
import MOC.SpectralMobius
import MOC.SpectralPerturbation
import MOC.SpectralSecondVariation
import MOC.SpectralStationarity
import MOC.StationaryPhaseGraph
import MOC.StrongSupport
import MOC.SubsetContraction
import MOC.Support
import MOC.SupportBlocks
import MOC.Transfer
import MOC.TwoExceptions
import MOC.TwoFrame
import MOC.TwoValues
import MOC.Variational
import MOC.WeightedMinor
import MOC.Weights
import MOC.Wielandt
import MOC.ZeroHeight

open BigOperators Matrix

example : MOC.MOCIsTrue ↔
    ∀ (n : ℕ) (a b : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ),
      (U * Uᴴ = 1 ∧ Uᴴ * U = 1) →
        (diagonal a + U * diagonal b * Uᴴ).det ∈ convexHull ℝ
          (Set.range (fun σ : Equiv.Perm (Fin n) => ∏ j, (a (σ j) + b j))) :=
  Iff.rfl

open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let declarations := env.constants.toList.filter fun (name, decl) =>
    if let some idx := env.getModuleIdxFor? name then
      (`MOC).isPrefixOf env.allImportedModuleNames[idx.toNat]! && !decl.isUnsafe
    else false
  if declarations.isEmpty then
    throwError "The MOC worker audit found no declarations"
  let audit := ((declarations.forM fun (name, _) => CollectAxioms.collect name).run env).run {}
  let extra := audit.2.axioms.filter (fun a => !allowed.contains a)
  unless extra.isEmpty do
    for (name, _) in declarations do
      let unapproved := (← collectAxioms name).filter fun a => !allowed.contains a
      unless unapproved.isEmpty do
        throwError "{name} depends on unapproved axioms {unapproved}"
    throwError "Unapproved axioms in MOC audit: {extra}"
  for (name, decl) in declarations do
    let type := decl.type
    if type.isConstOf ``MOC.MOCIsTrue ||
        (type.isForall && type.bindingDomain!.isConstOf ``Nat) then
      if ← liftTermElabM (isDefEq type (mkConst ``MOC.MOCIsTrue)) then
        logInfo m!"MOC_WORKER_UNRESTRICTED_VERIFIED {name} {← collectAxioms name}"
  logInfo m!"MOC_WORKER_AUDITED {declarations.length} safe declarations"
