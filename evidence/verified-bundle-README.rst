Regular fourteen-gon Minkowski plane: complete Lean formalization
================================================================

Status: verified in Azure on 2026-10-06. All 162 project modules in the
rebuild plan compiled successfully, including the complete geometry,
13,755 edge certificates, all 42 LRAT parts and the final unconditional
theorem. The final report is verification-final.json. All resources of
both verification jobs have been deleted, with confirmations retained.

Target
------

Let P be the convex hull in the complex plane of all roots of z^14 = 1.
Equip the plane with the Minkowski functional of P. Every map from this
plane to four colours has a monochromatic pair at distance one.
Equivalently, its unit-distance graph needs at least five colours.

The final Lean theorem is Minkowski14.at_least_five_colours in Final.lean.
It states that for any natural number n and any colouring c : Plane -> Fin n
that assigns different colours to every pair at distance one, 5 <= n.
The accompanying theorems plane_dimension and plane_unit_ball identify
the space as a real plane with the required regular fourteen-gon unit ball.

The formalization explicitly constructs a normed real vector space whose
closed unit ball is P. It does not assume a geometric interpretation of an
abstract algebraic root, or assume that a Python edge checker is correct.

Proof structure
---------------

* Algebra.lean defines zeta = exp(pi * i / 7), proves its primitive order,
  and derives the exact cubic and rational bounds for rho = 2 cos(2 pi/7).
* Polygon.lean proves that the convex hull is compact, balanced and
  absorbent, and that its gauge is positive definite with exactly this
  unit ball.
* Facet.lean constructs a supporting linear functional. Every point of
  every rotated polygon side is proved to have gauge one.
* Coordinates.lean proves that arithmetic on six integer coefficients
  agrees with evaluation at the geometric root zeta.
* Parameters.lean, Positions.lean and Geometry/Chunk*.lean check the
  finite geometric witnesses for the graph's 13,755 listed edges.
* MathIsEasy/Minkowski14/GraphCertificate.lean rebuilds the finite graph's
  non-four-colourability from its CNF encoding and LRAT proof.
* Plane.lean supplies the actual normed-space and metric instances.
* Final.lean pulls any colouring of the plane back along the verified
  coordinate map and applies the finite graph contradiction.

The colouring argument only requires unit length for listed edges.
Global injectivity of the coordinate map and completeness of the edge
list are not needed for this lower bound and are not being assumed.
This project does not formalize an upper bound of six colours.

Trust boundary
--------------

The project proof code contains no custom axioms, admissions, unsafe
commands, native_decide calls or compiler-trust axioms. The final theorem,
dimension theorem and unit-ball theorem each depend on exactly the three
standard Lean foundations propext, Classical.choice and Quot.sound.
FoundationAudit.lean rejects any other axiom; Audit.lean applies this check
and prints dependencies of the intermediate results.

A small valid SAT proof was accepted. Three negative controls were
rejected: a false coordinate equality, an invalid LRAT refutation of a
satisfiable formula, and a proof expression with the wrong type submitted
through the normal declaration API. These are intentionally failing tests
and are not imported by the mathematical result.

The LRAT reader uses ordinary file IO on literal paths and constructs proof
expressions checked by the Lean kernel. It does not evaluate arbitrary
Lean terms to obtain file contents. The exact-geometry generator supplies
integer witnesses; kernel reduction and generic soundness lemmas verify
those witnesses. Neither generator's output is accepted as an axiom.

Lean and mathlib themselves include implementation code and metaprograms.
The trust claim concerns project proof construction and the final theorem's
axiom dependencies, not an assertion that Lean or mathlib's implementation
contains no unsafe code anywhere.

Reproducibility and provenance
------------------------------

Toolchain: Lean 4.34.0.
Mathlib: 5ed2965256430c3649e86755f9576b54eca72435.

The graph data, original CNF/LRAT artefacts, and finite colouring bridge
come from the user's archive at projects/minkowski14. The geometry is a
new proof chain. The SAT importer has been rewritten to remove the five
unsafe term-evaluation calls, and the entire finite proof has been rebuilt.
The archive itself is left unchanged.

The geometry generator was rerun independently in Azure and reproduced
all 31 generated files byte for byte. The report matches every project
module's source hash to the successful compiler records and returned
sources. The three final modules were checked in a separate bounded
invocation inside the same job after the initial per-process memory cap
proved too small. That successful invocation is recorded in
extended-audit.json. Earlier failed attempts are retained in the raw logs;
they are not counted as successful verification.

The main job had a 24 GiB whole-process-tree memory cap, no swap, a
115-minute service timeout and an independent cloud deletion deadline.
Individual Lean invocations in the final audit had an 18,000 MiB cap and
a 240-second timeout. Both cloud jobs were removed after results were
retrieved. The generic development-session report describes transport
completion; verification-final.json assembles the mathematical checks.

Source package
--------------

lean-source.tgz contains the proof sources, graph/CNF/LRAT data, generator,
rebuild driver, pinned versions and verification reports. It contains no
compiled project proofs, cloud credentials or cloud run directories.
lean-source.tgz.sha256 identifies the archive, and the included
proof-source-manifest.json lists individual file hashes.

To reproduce the build, prepare an Azure Linux job with the pinned Lean
toolchain and a mathlib checkout at the commit above, including its normal
dependency cache. Extract the source package into that checkout. Project
sources are at the archive root; certificate inputs are under artifacts/.
Run ``python3 rebuild.py --plan-only`` to inspect the dependency order.
Run ``python3 rebuild.py`` inside the bounded job to rebuild all project
modules and execute the expected-failure controls. The driver checks the
toolchain and mathlib revision, requires the job marker
/run/mathiseasy-azure-verified and a cgroup memory cap no greater than
24 GiB. The Azure launcher must provide the job timeout and independent
deletion guard; the marker alone does not provide those safeguards.

The supplied driver's dependency plan was validated in Azure. The recorded
successful verification used the development worker and final-audit helper,
not an end-to-end invocation of this convenience driver. No full Lean
build or proof audit was run on the local workstation.

Formalization work: OpenAI Codex (GPT-6 Astra).

All substantial verification runs take place in Azure with a whole-job
memory limit, a time limit and an independent cloud deletion guard.
Local work is limited to source editing, packaging and light checks.
Azure logs, input hashes, compiler results and deletion confirmations are
retained below formal/azure/runs and formal/full-azure/runs. Private cloud
credentials in run directories are not publication materials.
