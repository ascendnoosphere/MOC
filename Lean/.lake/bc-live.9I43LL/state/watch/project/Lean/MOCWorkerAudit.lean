import MOC
import MOC.Blocks
import MOC.Claim
import MOC.Core
import MOC.Geometry
import MOC.Obstruction
import MOC.UnqueuedFixture
import MOC.Weights
import MOC.WorkflowSmoke

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
