import MathIsEasy.Minkowski14.GraphData
import MathIsEasy.Minkowski14LRAT.Base
import MathIsEasy.Minkowski14.GraphEncoding.Vertex001
import MathIsEasy.Minkowski14.GraphEncoding.Vertex002
import MathIsEasy.Minkowski14.GraphEncoding.Vertex003
import MathIsEasy.Minkowski14.GraphEncoding.Vertex004
import MathIsEasy.Minkowski14.GraphEncoding.Vertex005
import MathIsEasy.Minkowski14.GraphEncoding.Vertex006
import MathIsEasy.Minkowski14.GraphEncoding.Vertex007
import MathIsEasy.Minkowski14.GraphEncoding.Vertex008
import MathIsEasy.Minkowski14.GraphEncoding.Vertex009
import MathIsEasy.Minkowski14.GraphEncoding.Vertex010
import MathIsEasy.Minkowski14.GraphEncoding.Vertex011
import MathIsEasy.Minkowski14.GraphEncoding.Vertex012
import MathIsEasy.Minkowski14.GraphEncoding.Vertex013
import MathIsEasy.Minkowski14.GraphEncoding.Vertex014
import MathIsEasy.Minkowski14.GraphEncoding.Vertex015
import MathIsEasy.Minkowski14.GraphEncoding.Vertex016
import MathIsEasy.Minkowski14.GraphEncoding.Edge001
import MathIsEasy.Minkowski14.GraphEncoding.Edge002
import MathIsEasy.Minkowski14.GraphEncoding.Edge003
import MathIsEasy.Minkowski14.GraphEncoding.Edge004
import MathIsEasy.Minkowski14.GraphEncoding.Edge005
import MathIsEasy.Minkowski14.GraphEncoding.Edge006
import MathIsEasy.Minkowski14.GraphEncoding.Edge007
import MathIsEasy.Minkowski14.GraphEncoding.Edge008
import MathIsEasy.Minkowski14.GraphEncoding.Edge009
import MathIsEasy.Minkowski14.GraphEncoding.Edge010
import MathIsEasy.Minkowski14.GraphEncoding.Edge011
import MathIsEasy.Minkowski14.GraphEncoding.Edge012
import MathIsEasy.Minkowski14.GraphEncoding.Edge013
import MathIsEasy.Minkowski14.GraphEncoding.Edge014
import MathIsEasy.Minkowski14.GraphEncoding.Edge015
import MathIsEasy.Minkowski14.GraphEncoding.Edge016
import MathIsEasy.Minkowski14.GraphEncoding.Edge017
import MathIsEasy.Minkowski14.GraphEncoding.Edge018
import MathIsEasy.Minkowski14.GraphEncoding.Edge019
import MathIsEasy.Minkowski14.GraphEncoding.Edge020
import MathIsEasy.Minkowski14.GraphEncoding.Edge021
import MathIsEasy.Minkowski14.GraphEncoding.Edge022
import MathIsEasy.Minkowski14.GraphEncoding.Edge023
import MathIsEasy.Minkowski14.GraphEncoding.Edge024
import MathIsEasy.Minkowski14.GraphEncoding.Edge025
import MathIsEasy.Minkowski14.GraphEncoding.Edge026
import MathIsEasy.Minkowski14.GraphEncoding.Edge027
import MathIsEasy.Minkowski14.GraphEncoding.Edge028
import MathIsEasy.Minkowski14.GraphEncoding.Root

namespace MathIsEasy.Minkowski14.FinalGraph

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Data EncodingData MathIsEasy.Minkowski14LRAT

def encodingChunks : List Sat.Fmla := [
  vertexCNFChunk001,
  vertexCNFChunk002,
  vertexCNFChunk003,
  vertexCNFChunk004,
  vertexCNFChunk005,
  vertexCNFChunk006,
  vertexCNFChunk007,
  vertexCNFChunk008,
  vertexCNFChunk009,
  vertexCNFChunk010,
  vertexCNFChunk011,
  vertexCNFChunk012,
  vertexCNFChunk013,
  vertexCNFChunk014,
  vertexCNFChunk015,
  vertexCNFChunk016,
  edgeCNFChunk001,
  edgeCNFChunk002,
  edgeCNFChunk003,
  edgeCNFChunk004,
  edgeCNFChunk005,
  edgeCNFChunk006,
  edgeCNFChunk007,
  edgeCNFChunk008,
  edgeCNFChunk009,
  edgeCNFChunk010,
  edgeCNFChunk011,
  edgeCNFChunk012,
  edgeCNFChunk013,
  edgeCNFChunk014,
  edgeCNFChunk015,
  edgeCNFChunk016,
  edgeCNFChunk017,
  edgeCNFChunk018,
  edgeCNFChunk019,
  edgeCNFChunk020,
  edgeCNFChunk021,
  edgeCNFChunk022,
  edgeCNFChunk023,
  edgeCNFChunk024,
  edgeCNFChunk025,
  edgeCNFChunk026,
  edgeCNFChunk027,
  edgeCNFChunk028,
  rootCNFChunk
]

def encodingCtx : Sat.Fmla := encodingChunks.flatten

/-- The LRAT context is the chunked standard graph encoding. -/
theorem lratCtx_eq_encodingCtx : ctx = encodingCtx := by
  rfl

theorem properColouring_satisfies_encodingCtx {colouring : Colouring}
    (hproper : ProperOn edges colouring) :
    (colouringValuation (normaliseColouring root colouring)).satisfies_fmla
      encodingCtx := by
  have hproperChunk : ∀ chunk ∈ edgeChunks, ProperOn chunk colouring := by
    intro chunk hchunk edge hedge
    exact hproper edge (edge_mem_edges hchunk hedge)
  apply satisfies_fmla_flatten
  intro chunk hchunk
  simp only [encodingChunks, List.mem_cons, List.not_mem_nil, or_false] at hchunk
  rcases hchunk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [vertexCNFChunk001_eq]
    exact satisfies_vertexBlockClauses _ 0 100
  · rw [vertexCNFChunk002_eq]
    exact satisfies_vertexBlockClauses _ 100 100
  · rw [vertexCNFChunk003_eq]
    exact satisfies_vertexBlockClauses _ 200 100
  · rw [vertexCNFChunk004_eq]
    exact satisfies_vertexBlockClauses _ 300 100
  · rw [vertexCNFChunk005_eq]
    exact satisfies_vertexBlockClauses _ 400 100
  · rw [vertexCNFChunk006_eq]
    exact satisfies_vertexBlockClauses _ 500 100
  · rw [vertexCNFChunk007_eq]
    exact satisfies_vertexBlockClauses _ 600 100
  · rw [vertexCNFChunk008_eq]
    exact satisfies_vertexBlockClauses _ 700 100
  · rw [vertexCNFChunk009_eq]
    exact satisfies_vertexBlockClauses _ 800 100
  · rw [vertexCNFChunk010_eq]
    exact satisfies_vertexBlockClauses _ 900 100
  · rw [vertexCNFChunk011_eq]
    exact satisfies_vertexBlockClauses _ 1000 100
  · rw [vertexCNFChunk012_eq]
    exact satisfies_vertexBlockClauses _ 1100 100
  · rw [vertexCNFChunk013_eq]
    exact satisfies_vertexBlockClauses _ 1200 100
  · rw [vertexCNFChunk014_eq]
    exact satisfies_vertexBlockClauses _ 1300 100
  · rw [vertexCNFChunk015_eq]
    exact satisfies_vertexBlockClauses _ 1400 100
  · rw [vertexCNFChunk016_eq]
    exact satisfies_vertexBlockClauses _ 1500 40
  · rw [edgeCNFChunk001_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk001 (by simp [edgeChunks])
  · rw [edgeCNFChunk002_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk002 (by simp [edgeChunks])
  · rw [edgeCNFChunk003_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk003 (by simp [edgeChunks])
  · rw [edgeCNFChunk004_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk004 (by simp [edgeChunks])
  · rw [edgeCNFChunk005_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk005 (by simp [edgeChunks])
  · rw [edgeCNFChunk006_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk006 (by simp [edgeChunks])
  · rw [edgeCNFChunk007_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk007 (by simp [edgeChunks])
  · rw [edgeCNFChunk008_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk008 (by simp [edgeChunks])
  · rw [edgeCNFChunk009_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk009 (by simp [edgeChunks])
  · rw [edgeCNFChunk010_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk010 (by simp [edgeChunks])
  · rw [edgeCNFChunk011_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk011 (by simp [edgeChunks])
  · rw [edgeCNFChunk012_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk012 (by simp [edgeChunks])
  · rw [edgeCNFChunk013_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk013 (by simp [edgeChunks])
  · rw [edgeCNFChunk014_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk014 (by simp [edgeChunks])
  · rw [edgeCNFChunk015_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk015 (by simp [edgeChunks])
  · rw [edgeCNFChunk016_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk016 (by simp [edgeChunks])
  · rw [edgeCNFChunk017_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk017 (by simp [edgeChunks])
  · rw [edgeCNFChunk018_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk018 (by simp [edgeChunks])
  · rw [edgeCNFChunk019_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk019 (by simp [edgeChunks])
  · rw [edgeCNFChunk020_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk020 (by simp [edgeChunks])
  · rw [edgeCNFChunk021_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk021 (by simp [edgeChunks])
  · rw [edgeCNFChunk022_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk022 (by simp [edgeChunks])
  · rw [edgeCNFChunk023_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk023 (by simp [edgeChunks])
  · rw [edgeCNFChunk024_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk024 (by simp [edgeChunks])
  · rw [edgeCNFChunk025_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk025 (by simp [edgeChunks])
  · rw [edgeCNFChunk026_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk026 (by simp [edgeChunks])
  · rw [edgeCNFChunk027_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk027 (by simp [edgeChunks])
  · rw [edgeCNFChunk028_eq]
    apply normalisedColouring_satisfies_edgeListClauses
    exact hproperChunk edgeChunk028 (by simp [edgeChunks])
  · rw [rootCNFChunk_eq]
    exact normalisedColouring_satisfies_rootFormula root colouring

end MathIsEasy.Minkowski14.FinalGraph
