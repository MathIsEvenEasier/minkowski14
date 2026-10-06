import ColouringTransfer
import MathIsEasy.Minkowski14.GraphCertificate

namespace Minkowski14

/-- No four-colouring of the entire plane separates all pairs at polygon unit distance. -/
theorem no_four_colouring (c : ℂ → Fin 4) :
    ∃ x y : ℂ, polygonNorm (x-y) = 1 ∧ c x = c y :=
  finite_obstruction_transfer MathIsEasy.Minkowski14.FinalGraph.notFourColourable c

/-- The unconditional result expressed using the actual normed-plane metric. -/
theorem plane_no_four_colouring (c : Plane → Fin 4) :
    ∃ x y : Plane, dist x y = 1 ∧ c x = c y := by
  obtain ⟨x,y,hd,hc⟩ := no_four_colouring c
  exact ⟨x,y,(plane_distance x y).trans hd,hc⟩

/-- Every finite proper colouring of this normed plane uses at least five colours. -/
theorem at_least_five_colours {n : Nat} (c : Plane → Fin n)
    (proper : ∀ x y : Plane, dist x y = 1 → c x ≠ c y) : 5 ≤ n := by
  by_contra h
  have hn : n ≤ 4 := by omega
  obtain ⟨x,y,hd,hc⟩ := plane_no_four_colouring (fun x => Fin.castLE hn (c x))
  exact proper x y hd (Fin.ext (congrArg (fun z : Fin 4 => z.val) hc))

end Minkowski14
