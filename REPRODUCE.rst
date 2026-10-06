Reproduce and inspect the proof
===============================

Lightweight checks
------------------

From the repository root::

    python3 scripts/verify_packet.py
    node --test scripts/visual_math.test.mjs

The first command checks source hashes, the decompressed LRAT hash, graph
counts, exact transcription of browser data and local source links. It
performs no Lean compilation. The second checks the numerical functions
used solely in the explanatory page. Neither is a substitute for Lean.

Proof source layout
-------------------

formal/ contains the complete project Lean source tree. Inputs are in
formal/artifacts/: the graph JSON, four-colouring CNF and gzip-compressed
LRAT proof. The authoritative decompressed LRAT
hash is in evidence/proof-source-manifest.json. Decompress before replay::

    gzip -dk formal/artifacts/minkowski14_final_4color.lrat.gz

The source package's original manifest uses paths relative to formal/
for Lean modules and artifacts. Publication prose and the browser are
separate from those immutable proof sources.

Pinned environment
------------------

* Lean 4.34.0 (formal/lean-toolchain).
* mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
* Normal mathlib dependency caches for that toolchain; no precompiled
  project result is required.

The convenience driver expects a mathlib checkout at that commit, with
the contents of formal/ copied into the checkout root and the LRAT file
decompressed. From the prepared checkout::

    python3 rebuild.py --plan-only
    python3 rebuild.py

The plan rebuilds all 162 project modules in dependency order and then
checks three intentional failures. The public GitHub Actions run
linked in README.rst executed the driver end to end from the displayed
commit. Its compiler records and final axiom output are preserved in
evidence/public-ci-2026-10-06/. Earlier development records remain below.

For this project's authoring environment, substantial compilation and
proof audits run only in Azure. The driver enforces a prepared-job marker
(/run/mathiseasy-azure-verified) and a cgroup memory limit at most 24 GiB.
The operator must supply a whole-job timeout and independent resource
cleanup. Creating the marker is not a resource-control mechanism.
The recorded main job used a 24 GiB cap, no swap, a 115-minute timeout
and an independent cloud deletion guard. Final Lean invocations used
an 18,000 MiB cap and a 240-second per-module timeout.

Inspect the recorded evidence
----------------------------

* verification-final.json matches all 162 source hashes to successful
  compiler records and returned source files.
* sat-build.json records the complete finite-certificate rebuild.
* development-history.json retains successful and failed development
  attempts; a failed attempt is not counted as successful verification.
* extended-audit.json records the successful joined final theorem and
  foundation audit after increasing the initial per-process memory cap.
* generation-reproduction.json records byte-for-byte reproduction of all
  31 generated files.
* cleanup-report.json and geometry-cleanup-report.json confirm deletion
  of both verification jobs' resources.

All of these files are under evidence/. The full final report is the
mathematical verification record, not merely a transport-success flag.
No new cloud job is launched by the website or lightweight checks.

Trust boundary
--------------

The proof uses the ordinary Lean kernel. The final theorem, dimension
and unit-ball identification depend only on propext, Classical.choice
and Quot.sound. The checked FoundationAudit command rejects other axioms.
The theorem does not trust a solver's UNSAT label, a Python checker, browser
numerics, or a generator: it checks supplied proof expressions and exact
geometric witnesses.

The project source has no custom axioms, admissions, unsafe declarations,
native_decide or compiler-trust axiom. This is not a claim that Lean and
mathlib's implementation contains no unsafe metaprogramming internally.
No audit by a separate kernel reimplementation is claimed.

PositiveControlSAT.lean must pass. NegativeControl.lean,
NegativeControlSAT.lean and NegativeKernel.lean must fail with their
specified diagnostics. They test, respectively, a false coordinate
identity, a false refutation and a proof expression of the wrong type.
The negative files are not imports of the mathematical result.
