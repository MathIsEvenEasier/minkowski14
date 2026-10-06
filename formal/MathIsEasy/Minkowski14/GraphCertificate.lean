import MathIsEasy.Minkowski14.GraphEncoding
import MathIsEasy.Minkowski14LRAT.Chunk042

/-!
# The certified non-four-colourability theorem for the final finite graph

The chunked bridge proves that every proper colouring satisfies the exact
DIMACS context checked by LRAT.  Applying the kernel-checked empty-clause
derivation then gives the graph-theoretic theorem below.
-/

namespace MathIsEasy.Minkowski14.FinalGraph

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open MathIsEasy.Minkowski14LRAT

/-- The exact 1540-vertex graph has no proper four-colouring. -/
theorem notFourColourable : ¬ FourColourable edges := by
  rintro ⟨colouring, hproper⟩
  have hsatisfiesEncoding := properColouring_satisfies_encodingCtx hproper
  have hsatisfiesCtx :
      (colouringValuation (normaliseColouring root colouring)).satisfies_fmla ctx := by
    rw [lratCtx_eq_encodingCtx]
    exact hsatisfiesEncoding
  exact fourColouringCNFUnsatisfiable _ hsatisfiesCtx

end MathIsEasy.Minkowski14.FinalGraph
