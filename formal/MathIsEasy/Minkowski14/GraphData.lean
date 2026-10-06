import MathIsEasy.Minkowski14.GraphData.Chunk001
import MathIsEasy.Minkowski14.GraphData.Chunk002
import MathIsEasy.Minkowski14.GraphData.Chunk003
import MathIsEasy.Minkowski14.GraphData.Chunk004
import MathIsEasy.Minkowski14.GraphData.Chunk005
import MathIsEasy.Minkowski14.GraphData.Chunk006
import MathIsEasy.Minkowski14.GraphData.Chunk007
import MathIsEasy.Minkowski14.GraphData.Chunk008
import MathIsEasy.Minkowski14.GraphData.Chunk009
import MathIsEasy.Minkowski14.GraphData.Chunk010
import MathIsEasy.Minkowski14.GraphData.Chunk011
import MathIsEasy.Minkowski14.GraphData.Chunk012
import MathIsEasy.Minkowski14.GraphData.Chunk013
import MathIsEasy.Minkowski14.GraphData.Chunk014
import MathIsEasy.Minkowski14.GraphData.Chunk015
import MathIsEasy.Minkowski14.GraphData.Chunk016
import MathIsEasy.Minkowski14.GraphData.Chunk017
import MathIsEasy.Minkowski14.GraphData.Chunk018
import MathIsEasy.Minkowski14.GraphData.Chunk019
import MathIsEasy.Minkowski14.GraphData.Chunk020
import MathIsEasy.Minkowski14.GraphData.Chunk021
import MathIsEasy.Minkowski14.GraphData.Chunk022
import MathIsEasy.Minkowski14.GraphData.Chunk023
import MathIsEasy.Minkowski14.GraphData.Chunk024
import MathIsEasy.Minkowski14.GraphData.Chunk025
import MathIsEasy.Minkowski14.GraphData.Chunk026
import MathIsEasy.Minkowski14.GraphData.Chunk027
import MathIsEasy.Minkowski14.GraphData.Chunk028

namespace MathIsEasy.Minkowski14.FinalGraph

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Data

def vertexCount : Nat := 1540
def root : Nat := 759

def edgeChunks : List (List Edge) := [
  edgeChunk001,
  edgeChunk002,
  edgeChunk003,
  edgeChunk004,
  edgeChunk005,
  edgeChunk006,
  edgeChunk007,
  edgeChunk008,
  edgeChunk009,
  edgeChunk010,
  edgeChunk011,
  edgeChunk012,
  edgeChunk013,
  edgeChunk014,
  edgeChunk015,
  edgeChunk016,
  edgeChunk017,
  edgeChunk018,
  edgeChunk019,
  edgeChunk020,
  edgeChunk021,
  edgeChunk022,
  edgeChunk023,
  edgeChunk024,
  edgeChunk025,
  edgeChunk026,
  edgeChunk027,
  edgeChunk028
]

def edges : List Edge := edgeChunks.flatten

theorem edges_length : edges.length = 13755 := by rfl

theorem edge_mem_edges {chunk : List Edge} {edge : Edge}
    (hchunk : chunk ∈ edgeChunks) (hedge : edge ∈ chunk) :
    edge ∈ edges := by
  simp only [edges, List.mem_flatten]
  exact ⟨chunk, hchunk, hedge⟩

end MathIsEasy.Minkowski14.FinalGraph
