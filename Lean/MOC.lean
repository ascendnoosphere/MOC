import MOC.Claim
import MOC.Geometry
import MOC.Obstruction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, declaration) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless (`MOC).isPrefixOf env.allImportedModuleNames[idx.toNat]! do continue
    -- Code generation adds unsafe auxiliary declarations to the imported environment.
    if declaration.isUnsafe then continue
    count := count + 1
    let extra := (← collectAxioms name).filter fun a => !allowed.contains a
    unless extra.isEmpty do
      throwError "{name} depends on unapproved axioms {extra}"
  if count == 0 then
    throwError "The MOC axiom audit found no declarations"
  logInfo m!"Checked {count} safe MOC declarations against the standard Lean axioms"
