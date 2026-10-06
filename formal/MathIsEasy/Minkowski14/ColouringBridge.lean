import Mathlib.Tactic
import Mathlib.Tactic.Sat.FromLRAT

/-!
# The graph-colouring-to-CNF bridge

This file contains the theorem-level part of the bridge between a finite graph
and the LRAT-certified DIMACS formula. It is independent of the particular
1540-vertex graph: any proper four-colouring produces a valuation satisfying
the standard CNF, including the colour-symmetry clause. Consequently, a proof
that this CNF entails the empty clause rules out every proper four-colouring.
-/

namespace MathIsEasy.Minkowski14

abbrev Colour := Fin 4
abbrev Edge := Nat × Nat
abbrev Colouring := Nat → Colour

/-- The DIMACS variable for a vertex-colour pair, using zero-based SAT indices. -/
def satVariable (vertex : Nat) (colour : Colour) : Nat :=
  4 * vertex + colour.val

/-- Turn a four-colouring into the corresponding propositional valuation. -/
def colouringValuation (colouring : Colouring) : Sat.Valuation :=
  fun index ↦
    colouring (index / 4) =
      ⟨index % 4, Nat.mod_lt _ (by decide)⟩

@[simp]
theorem colouringValuation_satVariable (colouring : Colouring) (vertex : Nat)
    (colour : Colour) :
    colouringValuation colouring (satVariable vertex colour) ↔
      colouring vertex = colour := by
  have hdiv : (4 * vertex + colour.val) / 4 = vertex := by omega
  have hmod : (4 * vertex + colour.val) % 4 = colour.val := by omega
  simp only [colouringValuation, satVariable, hdiv, hmod]

/-- The clause saying that `vertex` has at least one of four colours. -/
def atLeastOneClause (vertex : Nat) : Sat.Clause :=
  [
    .pos (satVariable vertex 0),
    .pos (satVariable vertex 1),
    .pos (satVariable vertex 2),
    .pos (satVariable vertex 3)
  ]

/-- A clause forbidding two colours at one vertex. -/
def atMostOneClause (vertex : Nat) (first second : Colour) : Sat.Clause :=
  [.neg (satVariable vertex first), .neg (satVariable vertex second)]

/-- The seven standard exactly-one-colour clauses for one vertex. -/
def vertexClauses (vertex : Nat) : Sat.Fmla :=
  [
    atLeastOneClause vertex,
    atMostOneClause vertex 0 1,
    atMostOneClause vertex 0 2,
    atMostOneClause vertex 0 3,
    atMostOneClause vertex 1 2,
    atMostOneClause vertex 1 3,
    atMostOneClause vertex 2 3
  ]

/-- A clause forbidding one colour on both endpoints of an edge. -/
def edgeClause (edge : Edge) (colour : Colour) : Sat.Clause :=
  [
    .neg (satVariable edge.1 colour),
    .neg (satVariable edge.2 colour)
  ]

/-- The four clauses associated with one edge. -/
def edgeClauses (edge : Edge) : Sat.Fmla :=
  [edgeClause edge 0, edgeClause edge 1, edgeClause edge 2, edgeClause edge 3]

/-- The colouring clauses for a consecutive block of vertex indices. -/
def vertexBlockClauses (start count : Nat) : Sat.Fmla :=
  (List.range count).flatMap (fun offset ↦ vertexClauses (start + offset))

/-- The colouring clauses for a list of edges. -/
def edgeListClauses (edges : List Edge) : Sat.Fmla :=
  edges.flatMap edgeClauses

/-- Fixing one vertex to colour zero removes the global colour symmetry. -/
def rootClause (root : Nat) : Sat.Clause :=
  [.pos (satVariable root 0)]

/-- The exact clause ordering used by the Python DIMACS generator. -/
def fourColourCNF (vertexCount : Nat) (edges : List Edge) (root : Nat) : Sat.Fmla :=
  (List.range vertexCount).flatMap vertexClauses ++
    edges.flatMap edgeClauses ++ [rootClause root]

/-- A proper colouring separates the endpoints of every listed edge. -/
def ProperOn (edges : List Edge) (colouring : Colouring) : Prop :=
  ∀ edge ∈ edges, colouring edge.1 ≠ colouring edge.2

def FourColourable (edges : List Edge) : Prop :=
  ∃ colouring, ProperOn edges colouring

/-- Swap the root's colour with zero. This preserves properness and satisfies
the symmetry-breaking unit clause. -/
def normaliseColouring (root : Nat) (colouring : Colouring) : Colouring :=
  fun vertex ↦ Equiv.swap (colouring root) 0 (colouring vertex)

@[simp]
theorem normaliseColouring_root (root : Nat) (colouring : Colouring) :
    normaliseColouring root colouring root = 0 := by
  simp [normaliseColouring]

theorem normaliseColouring_ne {root first second : Nat} {colouring : Colouring}
    (h : colouring first ≠ colouring second) :
    normaliseColouring root colouring first ≠
      normaliseColouring root colouring second := by
  intro heq
  apply h
  exact (Equiv.swap (colouring root) 0).injective heq

theorem satisfies_atLeastOneClause (colouring : Colouring) (vertex : Nat) :
    (colouringValuation colouring).satisfies (atLeastOneClause vertex) := by
  change
    (¬ colouringValuation colouring (satVariable vertex 0)) →
    (¬ colouringValuation colouring (satVariable vertex 1)) →
    (¬ colouringValuation colouring (satVariable vertex 2)) →
    (¬ colouringValuation colouring (satVariable vertex 3)) → False
  intro h0 h1 h2 h3
  have hvalue :
      (colouring vertex).val = 0 ∨
      (colouring vertex).val = 1 ∨
      (colouring vertex).val = 2 ∨
      (colouring vertex).val = 3 := by
    omega
  rcases hvalue with hvalue | hvalue | hvalue | hvalue
  · have hcolour : colouring vertex = 0 := by
      apply Fin.ext
      exact hvalue
    exact h0 ((colouringValuation_satVariable colouring vertex 0).2 hcolour)
  · have hcolour : colouring vertex = 1 := by
      apply Fin.ext
      exact hvalue
    exact h1 ((colouringValuation_satVariable colouring vertex 1).2 hcolour)
  · have hcolour : colouring vertex = 2 := by
      apply Fin.ext
      exact hvalue
    exact h2 ((colouringValuation_satVariable colouring vertex 2).2 hcolour)
  · have hcolour : colouring vertex = 3 := by
      apply Fin.ext
      exact hvalue
    exact h3 ((colouringValuation_satVariable colouring vertex 3).2 hcolour)

theorem satisfies_atMostOneClause (colouring : Colouring) (vertex : Nat)
    (first second : Colour) (hne : first ≠ second) :
    (colouringValuation colouring).satisfies
      (atMostOneClause vertex first second) := by
  change
    colouringValuation colouring (satVariable vertex first) →
    colouringValuation colouring (satVariable vertex second) → False
  intro hfirst hsecond
  apply hne
  exact ((colouringValuation_satVariable colouring vertex first).1 hfirst).symm.trans
    ((colouringValuation_satVariable colouring vertex second).1 hsecond)

theorem satisfies_vertexClauses (colouring : Colouring) (vertex : Nat) :
    (colouringValuation colouring).satisfies_fmla (vertexClauses vertex) := by
  refine ⟨fun clause hclause ↦ ?_⟩
  simp only [vertexClauses, List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact satisfies_atLeastOneClause colouring vertex
  all_goals
    apply satisfies_atMostOneClause
    decide

theorem satisfies_edgeClause {colouring : Colouring} {edge : Edge}
    (hproper : colouring edge.1 ≠ colouring edge.2) (colour : Colour) :
    (colouringValuation colouring).satisfies (edgeClause edge colour) := by
  change
    colouringValuation colouring (satVariable edge.1 colour) →
    colouringValuation colouring (satVariable edge.2 colour) → False
  intro hfirst hsecond
  apply hproper
  exact ((colouringValuation_satVariable colouring edge.1 colour).1 hfirst).trans
    ((colouringValuation_satVariable colouring edge.2 colour).1 hsecond).symm

theorem satisfies_edgeClauses {colouring : Colouring} {edge : Edge}
    (hproper : colouring edge.1 ≠ colouring edge.2) :
    (colouringValuation colouring).satisfies_fmla (edgeClauses edge) := by
  refine ⟨fun clause hclause ↦ ?_⟩
  simp only [edgeClauses, List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with rfl | rfl | rfl | rfl
  all_goals exact satisfies_edgeClause hproper _

theorem satisfies_vertexBlockClauses (colouring : Colouring) (start count : Nat) :
    (colouringValuation colouring).satisfies_fmla
      (vertexBlockClauses start count) := by
  refine ⟨fun clause hclause ↦ ?_⟩
  simp only [vertexBlockClauses, List.mem_flatMap] at hclause
  obtain ⟨offset, _, hclause⟩ := hclause
  exact (satisfies_vertexClauses colouring (start + offset)).prop clause hclause

theorem satisfies_edgeListClauses {colouring : Colouring} {edges : List Edge}
    (hproper : ProperOn edges colouring) :
    (colouringValuation colouring).satisfies_fmla (edgeListClauses edges) := by
  refine ⟨fun clause hclause ↦ ?_⟩
  simp only [edgeListClauses, List.mem_flatMap] at hclause
  obtain ⟨edge, hedge, hclause⟩ := hclause
  exact (satisfies_edgeClauses (hproper edge hedge)).prop clause hclause

theorem normalisedColouring_satisfies_edgeListClauses (root : Nat)
    {colouring : Colouring} {edges : List Edge}
    (hproper : ProperOn edges colouring) :
    (colouringValuation (normaliseColouring root colouring)).satisfies_fmla
      (edgeListClauses edges) := by
  apply satisfies_edgeListClauses
  intro edge hedge
  exact normaliseColouring_ne (hproper edge hedge)

theorem satisfies_rootClause {colouring : Colouring} {root : Nat}
    (hroot : colouring root = 0) :
    (colouringValuation colouring).satisfies (rootClause root) := by
  change (¬ colouringValuation colouring (satVariable root 0)) → False
  intro hfalse
  exact hfalse ((colouringValuation_satVariable colouring root 0).2 hroot)

theorem normalisedColouring_satisfies_rootFormula (root : Nat)
    (colouring : Colouring) :
    (colouringValuation (normaliseColouring root colouring)).satisfies_fmla
      [rootClause root] := by
  refine ⟨fun clause hclause ↦ ?_⟩
  simp only [List.mem_singleton] at hclause
  subst clause
  exact satisfies_rootClause (normaliseColouring_root root colouring)

theorem satisfies_fmla_flatten {valuation : Sat.Valuation}
    {chunks : List Sat.Fmla}
    (hchunks : ∀ chunk ∈ chunks, valuation.satisfies_fmla chunk) :
    valuation.satisfies_fmla chunks.flatten := by
  refine ⟨fun clause hclause ↦ ?_⟩
  simp only [List.mem_flatten] at hclause
  obtain ⟨chunk, hchunk, hclause⟩ := hclause
  exact (hchunks chunk hchunk).prop clause hclause

/-- Every proper graph colouring gives a satisfying valuation for the complete
four-colouring CNF, even with its root-colour symmetry break. -/
theorem properColouring_satisfies_fourColourCNF {vertexCount root : Nat}
    {edges : List Edge} {colouring : Colouring}
    (hproper : ProperOn edges colouring) :
    (colouringValuation (normaliseColouring root colouring)).satisfies_fmla
      (fourColourCNF vertexCount edges root) := by
  let normalised := normaliseColouring root colouring
  refine ⟨fun clause hclause ↦ ?_⟩
  simp only [fourColourCNF, List.mem_append, List.mem_flatMap,
    List.mem_range, List.mem_singleton] at hclause
  rcases hclause with (hvertex | hedge) | hroot
  · obtain ⟨vertex, _, hclause⟩ := hvertex
    exact (satisfies_vertexClauses normalised vertex).prop clause hclause
  · obtain ⟨edge, hedge, hclause⟩ := hedge
    have hne : normalised edge.1 ≠ normalised edge.2 :=
      normaliseColouring_ne (hproper edge hedge)
    exact (satisfies_edgeClauses hne).prop clause hclause
  · subst clause
    exact satisfies_rootClause (normaliseColouring_root root colouring)

/-- If the standard graph-colouring CNF entails the empty clause, the graph
has no proper four-colouring. -/
theorem not_fourColourable_of_unsat {ctx : Sat.Fmla} {vertexCount root : Nat}
    {edges : List Edge}
    (hctx : ctx = fourColourCNF vertexCount edges root)
    (hunsat : Sat.Fmla.proof ctx Sat.Clause.nil) :
    ¬ FourColourable edges := by
  rintro ⟨colouring, hproper⟩
  have hsatisfies := properColouring_satisfies_fourColourCNF
    (vertexCount := vertexCount) (root := root) hproper
  have hctxSatisfies :
      (colouringValuation (normaliseColouring root colouring)).satisfies_fmla ctx := by
    simpa only [hctx] using hsatisfies
  exact hunsat _ hctxSatisfies

end MathIsEasy.Minkowski14
