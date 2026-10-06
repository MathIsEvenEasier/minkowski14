At least five colours for the regular fourteen-gon plane
=======================================================

Let P14 be the convex hull of the complex fourteenth roots of unity, and
let the plane carry the norm with closed unit ball P14. Every colouring
of the plane with four colours has two points at distance one with the
same colour. In symbols, chi(R^2, P14) >= 5.

Interactive explanation: https://mathiseveneasier.github.io/minkowski14/

The complete statement is checked in Lean, including construction of the
normed real plane, identification of its unit ball, the unit-edge geometry,
the finite colouring obstruction and the transfer to the entire plane.
This is a research announcement for external review; no priority claim is
made. Whether five colours suffice for the whole plane remains open.

Start here
----------

* `RESULT.rst <RESULT.rst>`_: the mathematical argument and its relation to prior work.
* `docs/ <docs/>`_: interactive unit ball, actual edge witnesses, colouring constraints
  and a conceptual dependency map with links to formal sources.
* `formal/Final.lean <formal/Final.lean>`_: the unconditional theorem at_least_five_colours.
* `formal/Plane.lean <formal/Plane.lean>`_: plane_dimension, plane_unit_ball and plane_distance.
* `evidence/verification-final.json <evidence/verification-final.json>`_: compiler evidence, source hashes,
  final axiom audit and negative controls.
* `REPRODUCE.rst <REPRODUCE.rst>`_: file layout, lightweight integrity checks and full replay.
* `review/README.rst <review/README.rst>`_: a focused checklist for mathematical review.

Proof in brief
--------------

The archived construction supplies an abstract graph with 1,540 vertices
and 13,755 edges, together with coordinates in Z[zeta], zeta = exp(pi*i/7).
For every listed edge, Lean verifies an identity of the form

  point(u) - point(v) = zeta^j * ((1-t) + t*zeta),   0 <= t <= 1.

The geometric lemmas show that this is a point on a side of the unit ball,
so the edge has norm one. A 42-part LRAT refutation, connected formally to
the graph's four-colouring formula, rules out every four-colouring of the
graph. Any proper four-colouring of the plane would restrict to one of the
graph, yielding a contradiction.

The Boolean encoding has 6,160 variables and 65,801 clauses. All listed
edges are covered. Completeness of the edge list and global injectivity of
the coordinate map are unnecessary for this implication.

Verification and scope
----------------------

Lean 4.34.0; mathlib 5ed2965256430c3649e86755f9576b54eca72435.
All 162 project modules in the rebuild plan passed. The final theorem,
unit-ball theorem and dimension theorem depend only on propext,
Classical.choice and Quot.sound. Project proof code contains no custom
axioms, sorry, unsafe, native_decide or kernel bypasses. A valid small
SAT control passed; three deliberately invalid controls were rejected.

The geometry generator reproduced all 31 generated files byte for byte.
These computations supply witnesses, not additional logical assumptions.
The browser uses numerical approximations solely for illustrations.

The Lean result is the lower bound five. Gehér's published upper bound six
is background, not a theorem formalized here. Combined with that result,
5 <= chi(R^2,P14) <= 6. Neither a five-colouring of the plane nor a lower
bound six is claimed.

Provenance and acknowledgments
-------------------------------

The graph, original CNF/LRAT data and finite graph-to-CNF bridge were
recovered from an earlier AI-assisted research archive. This release adds
a new complete geometric proof, removes the SAT importer's five unsafe
term-evaluation calls, and rebuilds the entire finite certificate and
final theorem. The original archive was not modified.

Prepared by MathIsEvenEasier with OpenAI Codex (GPT-6 Astra). The model
completed the geometric formalization, rebuilt and audited the proof, and
prepared the exposition and verification tooling under human direction.
Independent expert review is pending.

Research inspired by @xamualexander, Dr. Samuel Allen Alexander. Still there.

References
----------

* Geoffrey Exoo, David Fisher and Dan Ismailescu, The chromatic number of
  the Minkowski plane -- the regular polygon case (2021),
  https://arxiv.org/abs/2108.12861 . Lower bounds of five for the regular
  8-, 10- and 12-gon norms.
* Panna Gehér, Note on the chromatic number of Minkowski planes: the regular
  polygon case (2023), https://arxiv.org/abs/2301.13695 . An upper bound of
  six for even regular polygons with at most 22 vertices.

Public source build
-------------------

The manually dispatched Azure workflow compiles the displayed commit and
prints the final theorem and its axioms. See PUBLIC-CI.rst for the resource
limits, source provenance, logs and reproduction procedure.

https://github.com/MathIsEvenEasier/minkowski14/actions/workflows/lean.yml
