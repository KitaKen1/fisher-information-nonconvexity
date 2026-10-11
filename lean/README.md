# Complete Lean proof

Lean `v4.35.0-rc3`, with Mathlib `1b5006ca00888f8aaafa8939b28787d423e44bba` and
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) `e0c8f0ae12afc2358eb2e0a0798ab94303bd213d`.

- [Fisher41/Defs.lean](Fisher41/Defs.lean), [Fisher41/Density.lean](Fisher41/Density.lean),
  [Fisher41/Statement.lean](Fisher41/Statement.lean): definitions, the explicit density, and the
  final propositions (the trusted statement).
- [Fisher41/Main/Paper.lean](Fisher41/Main/Paper.lean): `Fisher41.paperTheorem1`, the full
  statement for the explicit density: $`D(f)<-10^{-44}`$, $`C^2`$ on $`(0,\infty)`$,
  $`I''<0`$ near $`0`$, and non-convexity.
  [Fisher41/Main/Theorems.lean](Fisher41/Main/Theorems.lean): `pdfMain`, `fisherSecondDerivNeg`,
  `fisherNonconvex`.
- [Fisher41/FC/Statement.lean](Fisher41/FC/Statement.lean): definitions copied from the
  FC-style statement. [Fisher41/FC/Main.lean](Fisher41/FC/Main.lean):
  `Arxiv.«2605.18081».fisherInformationConvexity`.
- `Numerics/`, `Static/`, `Heat/` and `Fixed/` contain the certificate, the static estimates,
  the heat-flow analysis and the explicit constants.

```bash
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

Scripts:
- `scripts/build_audit.py`, run from the repository root, builds both proof versions, checks
  the final axioms, and compares the definitions and statements with the FC-style file.
  Set `FC_DIR` to also compile the FC-style file with the Formal Conjectures linters. If that
  checkout's packages are not built, also set `FC_DEPS_DIR` to a built project pinning the same
  dependency revisions. Results go to `evidence/build.log` and `evidence/build_results.json`.
- `scripts/make_lean4web.py` regenerates the standalone file.
- `scripts/fill_links.py REPOSITORY_URL FULL_COMMIT_SHA` fills the proof and Lean4Web links after
  publication.
- `scripts/gen_cells.py data/partition_293.json 30 -5000000000000000000` regenerates
  `Fisher41/Numerics/Cells/`.
- `scripts/build_dag.py N` builds the modules in dependency order with at most `N` concurrent
  jobs.
