# Statement in the format of Formal Conjectures

[FisherInformationConvexity.lean](FisherInformationConvexity.lean) states Problem (iii) of
[Zou, Fan, Gao and Wang (2026), Section 7.3](https://arxiv.org/abs/2605.18081): is the Fisher
information of the Gaussian heat flow always convex in time? Both statements have a negative
answer. The intended location is `FormalConjectures/Arxiv/2605.18081/FisherInformationConvexity.lean`.

- **Main target:** `Arxiv.«2605.18081».fisherInformationConvexity`, for the admissible densities
  `IsAdmissible` of the paper (positive Schwartz probability densities with finite
  $`\mathcal I,\mathcal Q,\mathcal D`$ and $`\mathcal Q>0`$).
- **Variant:** `Arxiv.«2605.18081».fisherInformationConvexity.variants.smooth`, for the broader
  class `IsWeaklyAdmissible`: smooth positive probability densities with finite Fisher
  information. It is `IsAdmissible` with smoothness in place of the Schwartz condition and
  without the conditions on $`\mathcal Q`$ and $`\mathcal D`$.
- **Definitions:** `heatFlow`, `fisherInformation`, `negLogHess`, `IsAdmissible` and
  `IsWeaklyAdmissible` are copied verbatim in
  [Fisher41/FC/Statement.lean](../lean/Fisher41/FC/Statement.lean). The complete proof in
  [Fisher41/FC/Main.lean](../lean/Fisher41/FC/Main.lean) relates them to the project's definitions.
- **Proof links:** both statements use `by sorry`, with `formal_proof` links to the complete Lean
  proofs. Run `fill_links.py` with a public commit to pin these links and the Lean4Web link.

`python3 lean/scripts/build_audit.py` checks that the definitions and both statements agree with
the complete proof and with the Lean4Web file. With `FC_DIR` set, it also compiles this file
against Formal Conjectures with the Formal Conjectures linters.
