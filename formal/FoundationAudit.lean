import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-- Fail the build on any axiom other than the three permitted Lean foundations. -/
elab "assert_foundations " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unapproved axiom in {name}: {ax}"
  logInfo m!"Foundation audit passed: {name}; axioms: {axioms.toList}"
