import MOC
import MOC.Blocks
import MOC.Claim
import MOC.ContactRectangle
import MOC.Core
import MOC.Geometry
import MOC.Jacobi
import MOC.MixedBound
import MOC.Normal
import MOC.Obstruction
import MOC.PhaseMove
import MOC.RankSum
import MOC.Realification
import MOC.Small
import MOC.Source
import MOC.Support
import MOC.Transfer
import MOC.TwoValues
import MOC.Weights

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
  let mut count := 0
  for (name, decl) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`MOC).isPrefixOf env.allImportedModuleNames[idx.toNat]! do continue
    if decl.isUnsafe then continue
    count := count + 1
    let axioms ← collectAxioms name
    let extra := axioms.filter fun a => !allowed.contains a
    unless extra.isEmpty do
      throwError "{name} depends on unapproved axioms {extra}"
    let type := decl.type
    if type.isConstOf ``MOC.MOCIsTrue ||
        (type.isForall && type.bindingDomain!.isConstOf ``Nat) then
      if ← liftTermElabM (isDefEq type (mkConst ``MOC.MOCIsTrue)) then
        logInfo m!"MOC_WORKER_UNRESTRICTED_VERIFIED {name} {axioms}"
  if count == 0 then
    throwError "The MOC worker audit found no declarations"
  logInfo m!"MOC_WORKER_AUDITED {count} safe declarations"
