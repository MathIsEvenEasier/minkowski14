import Embedding
import Plane

namespace Minkowski14

/-- A verified finite unit-distance obstruction rules out a plane four-colouring. -/
theorem finite_obstruction_transfer
    (obstruction : ¬ MathIsEasy.Minkowski14.FourColourable
      MathIsEasy.Minkowski14.FinalGraph.edges)
    (c : ℂ → Fin 4) :
    ∃ x y : ℂ, polygonNorm (x-y) = 1 ∧ c x = c y := by
  by_contra h
  apply obstruction
  refine ⟨fun n => c (point n), ?_⟩
  intro e he hcolour
  exact h ⟨point e.1, point e.2, edges_unit e.1 e.2 he, hcolour⟩

end Minkowski14
