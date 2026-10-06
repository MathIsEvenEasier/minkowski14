import MathIsEasy.Minkowski14.ColouringBridge

namespace MathIsEasy.Minkowski14.FinalGraph.EncodingData

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def rootCNFChunk : Sat.Fmla := [
  [.pos 3036]
]

theorem rootCNFChunk_eq : rootCNFChunk = [rootClause 759] := by
  rfl

end MathIsEasy.Minkowski14.FinalGraph.EncodingData
