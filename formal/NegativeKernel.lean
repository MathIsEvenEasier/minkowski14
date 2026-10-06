import Lean
open Lean Elab Command

-- The ordinary declaration checker must reject a proof of the wrong proposition.
-- This file is an expected-failure control and is never imported by the result.
run_cmd liftCoreM <| addDecl <| Declaration.thmDecl {
  name := `Minkowski14RejectedKernelControl
  levelParams := []
  type := mkConst ``False
  value := mkConst ``True.intro
}
