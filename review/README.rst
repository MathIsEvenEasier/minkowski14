Suggested review path
======================

Begin with RESULT.rst and formal/Final.lean. The claim is the lower bound
five for the real plane with regular fourteen-gon unit ball. It is not
a determination of the exact chromatic number.

1. Statement and geometry: inspect Plane.lean, especially the real dimension,
   unit-ball equality and metric. Confirm that the root is exp(pi*i/7),
   not an unidentified conjugate of an algebraic number.
2. Side lemma: inspect Facet.rotated_side_unit, the supporting functional,
   and Parameters.parameter_bounds for all 29 parameter triples.
3. Edge correspondence: inspect Coordinates, Positions, the Geometry chunks
   and Embedding. Confirm that the verified geometric edge lists are the
   same lists consumed by the finite graph certificate.
4. Colouring semantics: inspect GraphEncoding and GraphCertificate. Check
   exactly-one constraints, edge constraints and the anchor-colour
   normalization. Inspect the LRAT importer and its use of safe addDecl.
5. Global conclusion: inspect ColouringTransfer and Final. The restriction
   of a colouring requires only verified unit edges; global coordinate
   injectivity and completeness of the edge list are not assumptions.
6. Verification evidence: match source hashes, read the final axiom output,
   and inspect the rejected controls. Compiler failures from earlier
   development are retained and distinguished from final successful checks.
7. Prior work: compare the fourteen-gon statement with Exoo--Fisher--
   Ismailescu (2021), Gehér (2023) and any subsequent work. Priority is not
   asserted; corrections and matching prior results are welcome.

This checklist is prepared by the authoring agent. It does not constitute
an independent external mathematical review.
