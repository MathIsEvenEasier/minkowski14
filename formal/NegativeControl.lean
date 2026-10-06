import Coordinates
open Minkowski14
-- This file MUST fail to compile. A changed coordinate is not silently accepted.
example : Coordinate.sub ⟨1,0,0,0,0,0⟩ ⟨0,0,0,0,0,0⟩ =
    (⟨2,0,0,0,0,0⟩ : Minkowski14.Coordinate) := by
  decide
