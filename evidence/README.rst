Verification evidence
=====================

Start with `verification-final.json <verification-final.json>`_. It joins
successful compiler records with exact hashes of the final project sources,
records the final axiom audit, and confirms deletion of both cloud jobs.

* `extended-audit.json <extended-audit.json>`_: successful final theorem,
  foundation checker and audit, after the joined proof required a larger
  per-process memory cap.
* `sat-build.json <sat-build.json>`_: complete finite certificate rebuild.
* `development-history.json <development-history.json>`_: development
  requests, successful modules and earlier failures, retained for transparency.
* `generation-reproduction.json <generation-reproduction.json>`_: the
  generator reproduced all 31 files byte for byte.
* `rebuild-plan.json <rebuild-plan.json>`_: the 162 project modules and
  three expected-failure controls.
* `proof-source-manifest.json <proof-source-manifest.json>`_: hashes from
  the verified source bundle. Proof paths are now below ../formal/; the
  LRAT hash is of the decompressed file.
* `cleanup-report.json <cleanup-report.json>`_ and
  `geometry-cleanup-report.json <geometry-cleanup-report.json>`_: confirmed
  resource deletion for both verification jobs.

verified-bundle-README.rst preserves the documentation accompanying the
original verified local source bundle. References in that archived text to
Azure run directories concern the authoring workspace. Current public
instructions and file layout are in `../REPRODUCE.rst <../REPRODUCE.rst>`_.

The evidence is a record of actual checks, not independent expert review.
The original compiler logs intentionally retain failed development attempts;
only matching successful final sources count towards VERIFIED.
