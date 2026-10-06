import Geometry.Chunk001
import Geometry.Chunk002
import Geometry.Chunk003
import Geometry.Chunk004
import Geometry.Chunk005
import Geometry.Chunk006
import Geometry.Chunk007
import Geometry.Chunk008
import Geometry.Chunk009
import Geometry.Chunk010
import Geometry.Chunk011
import Geometry.Chunk012
import Geometry.Chunk013
import Geometry.Chunk014
import Geometry.Chunk015
import Geometry.Chunk016
import Geometry.Chunk017
import Geometry.Chunk018
import Geometry.Chunk019
import Geometry.Chunk020
import Geometry.Chunk021
import Geometry.Chunk022
import Geometry.Chunk023
import Geometry.Chunk024
import Geometry.Chunk025
import Geometry.Chunk026
import Geometry.Chunk027
import Geometry.Chunk028
import MathIsEasy.Minkowski14.GraphData

namespace Minkowski14

open MathIsEasy.Minkowski14.FinalGraph

/-- Every listed graph edge has unit length in the regular fourteen-gon norm. -/
theorem edges_unit (u v : Nat) (h : (u,v) ∈ edges) :
    polygonNorm (point u - point v) = 1 := by
  obtain ⟨es, hes, he⟩ := List.mem_flatten.mp h
  simp only [edgeChunks, List.mem_cons, List.not_mem_nil, or_false] at hes
  rcases hes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Geometry001.edge_unit u v he
  · exact Geometry002.edge_unit u v he
  · exact Geometry003.edge_unit u v he
  · exact Geometry004.edge_unit u v he
  · exact Geometry005.edge_unit u v he
  · exact Geometry006.edge_unit u v he
  · exact Geometry007.edge_unit u v he
  · exact Geometry008.edge_unit u v he
  · exact Geometry009.edge_unit u v he
  · exact Geometry010.edge_unit u v he
  · exact Geometry011.edge_unit u v he
  · exact Geometry012.edge_unit u v he
  · exact Geometry013.edge_unit u v he
  · exact Geometry014.edge_unit u v he
  · exact Geometry015.edge_unit u v he
  · exact Geometry016.edge_unit u v he
  · exact Geometry017.edge_unit u v he
  · exact Geometry018.edge_unit u v he
  · exact Geometry019.edge_unit u v he
  · exact Geometry020.edge_unit u v he
  · exact Geometry021.edge_unit u v he
  · exact Geometry022.edge_unit u v he
  · exact Geometry023.edge_unit u v he
  · exact Geometry024.edge_unit u v he
  · exact Geometry025.edge_unit u v he
  · exact Geometry026.edge_unit u v he
  · exact Geometry027.edge_unit u v he
  · exact Geometry028.edge_unit u v he

end Minkowski14
