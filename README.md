# Lean proof that Fisher information along the heat flow is not convex

The convexity conjecture for Fisher information along the heat flow, Problem (iii) of
[Zou, Fan, Gao and Wang (2026), Section 7.3](https://arxiv.org/abs/2605.18081), is the following.

> **Conjecture.** For every $`d\ge1`$ and every admissible density $`f`$ on $`\mathbb R^d`$, the
> function
>
> ```math
> I_f(t)=\int_{\mathbb R^d}|\nabla\log P_tf|^2\,P_tf\,dx
> ```
>
> is convex on $`(0,\infty)`$. Here $`P_tf=f*\gamma_t`$, where $`\gamma_t`$ is the centered
> Gaussian density of covariance $`t\,\mathrm{Id}`$. The admissible densities are the positive
> Schwartz probability densities with finite $`\mathcal I,\mathcal Q,\mathcal D`$ and
> $`\mathcal Q>0`$ (Section 7 of the paper).

This repository presents a complete Lean proof that the answer to this conjecture is negative, by a
counterexample.

Note that the counterexample satisfies all the conditions of the conjecture above. Hence it also
disproves the variant statement, whose conditions are weaker (see the
[Appendix](#appendix-the-original-statement-and-a-variant-statement)).

**Main contribution.**

1. **Formal Conjectures statement.**
2. **Lean proof of the answer.**

**Subcontribution** (see the [Appendix](#appendix-the-original-statement-and-a-variant-statement)):

1. **Lean proof of a variant statement.**

**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/) (Lean **v4.35.0-rc3**).

## Formal Conjectures target

[FClikelean/FisherInformationConvexity.lean](FClikelean/FisherInformationConvexity.lean) states the
conjecture with `category research solved, AMS 35 60`.
[Fisher41/FC/Main.lean](lean/Fisher41/FC/Main.lean) proves both theorems below, with the same
definitions.

### Target theorem

```lean
theorem fisherInformationConvexity :
    answer(False) ↔
      ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsAdmissible f →
        ConvexOn ℝ (Set.Ioi 0) (fun t => fisherInformation (heatFlow f t))
```

`IsAdmissible f` is the admissible class of the paper: `f` is a positive Schwartz function with
`∫ f = 1`, the integrands of $`\mathcal I,\mathcal Q,\mathcal D`$ are integrable, and
$`\mathcal Q[f]>0`$.

### Variant theorem (weaker conditions)

```lean
theorem fisherInformationConvexity.variants.smooth :
    answer(False) ↔
      ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsWeaklyAdmissible f →
        ConvexOn ℝ (Set.Ioi 0) (fun t => fisherInformation (heatFlow f t))
```

`IsWeaklyAdmissible f` weakens `IsAdmissible f`: `f` is smooth and positive, `∫ f = 1`, and the
Fisher information is finite. The Schwartz condition becomes smoothness, and the conditions on
$`\mathcal Q`$ and $`\mathcal D`$ are dropped. The answer is still negative.

## Mathematical explanation (AI generated)

This sketch follows the Lean proof.

**Setting.** The counterexample is the following explicit density on $`\mathbb R^{41}`$
([Density.lean](lean/Fisher41/Density.lean)):

```math
u(s)=\tfrac43\log\bigl(1+e^{15-2s-s^2}\bigr),\quad \widetilde u(s)=\eta(s/16)\,u(s),\quad
w(x)=\widetilde u(|x|^2/2),
```

```math
U(x)=\sum_{z\in\mathbb Z^{41}}w(x-20z),\quad q=e^U,\quad
f=Z^{-1}q\,\gamma_{R^2},\quad Z=\int q\,\gamma_{R^2},\quad R=10^{40}.
```

Here $`\eta(v)=b(2-v)/(b(2-v)+b(v-1))`$ with $`b(a)=e^{-1/a}`$ for $`a>0`$ and $`b(a)=0`$
otherwise. For positive $`p`$, put

```math
H_p=-\nabla^2\log p,\qquad K_p=\sum_{i,j,k}(\partial_kH_{ij})^2+2\operatorname{tr}(H_p^3),
\qquad D(p)=\int pK_p .
```

Steps 1–4 show $`D(f)<0`$, and step 5 shows $`I_f''(t)=D(P_tf)`$ for $`t>0`$.

**1. A negative radial integral.** For a radial density $`p=e^{v(|x|^2/2)}`$ in dimension $`d`$,
the tensor contractions reduce to a cubic polynomial in $`v',v'',v'''`$:
$`K_p(x)=K_d(s;-v',v'',v''')`$ at $`s=|x|^2/2`$
([RadialTensor.lean](lean/Fisher41/Static/RadialTensor.lean); `Kd` in
[Defs.lean](lean/Fisher41/Defs.lean)). Put

```math
J=\int_0^8 r^{40}e^{u(r^2/2)}K_{41}\bigl(r^2/2;-u',u'',u'''\bigr)\,dr .
```

The bound $`J\le-5\cdot10^{18}`$ is checked as follows
([Numerics/](lean/Fisher41/Numerics/), [Cells/](lean/Fisher41/Numerics/Cells/)):
- **Arithmetic.** Integer interval arithmetic at scale $`2^{160}`$ propagates second-order
  jets. It covers exponentials, cube roots checked by witnesses, and the logistic function.
- **Quadrature.** The midpoint rule is used with a second-derivative remainder bound, on an
  adaptive dyadic partition of $`[0,8]`$ into 293 cells.
- **Checking.** Every cell inequality is checked by `decide +kernel`.

**2. Cutoff.** Derivative bounds for $`\eta`$ and for the tail of $`u`$ on $`[16,32]`$ show
$`J_{\mathrm{cut}}\le J+16`$, where $`J_{\mathrm{cut}}`$ uses $`\widetilde u`$
([Cutoff.lean](lean/Fisher41/Static/Cutoff.lean), [Profile.lean](lean/Fisher41/Static/Profile.lean)).

**3. Periodization.** The bumps $`w(\cdot-20z)`$ have disjoint supports in balls of radius 8.
Polar integration over the cell $`[-10,10]^{41}`$ gives

```math
\int_{[-10,10]^{41}}qK_q=\omega\,J_{\mathrm{cut}},\qquad \omega=41\,|B_1|\ge10^{-8},
```

with $`|B_1|=2^{21}\pi^{20}/41!!`$ and $`\pi>3`$
([Periodic.lean](lean/Fisher41/Static/Periodic.lean), [DBound.lean](lean/Fisher41/Fixed/DBound.lean)).

**4. Gaussian envelope.** $`H_f=H_q+R^{-2}\mathrm{Id}`$ gives

```math
Z\,D(f)=\mathbb E\,(qK_q)(G_R)+\tfrac{6}{R^2}\,\mathbb E\,(q\,|H_q|^2)(G_R)
+\tfrac{6}{R^4}\,\mathbb E\,(q\operatorname{tr}H_q)(G_R)+\tfrac{82}{R^6}\,Z ,
```

where $`G_R\sim\gamma_{R^2}`$ ([Envelope.lean](lean/Fisher41/Static/Envelope.lean)). For a
continuous $`20`$-periodic $`g`$ with $`|g|\le M`$, Gaussian averaging without Fourier analysis
gives $`|\mathbb E\,g(G_R)-\langle g\rangle_{\mathrm{cell}}|\le8\cdot41\cdot M\cdot20^2/R^2`$
([AveragingND.lean](lean/Fisher41/Static/AveragingND.lean)). The constants are:
- crude bounds $`10^{27}`$, $`10^{25}`$, $`10^{18}`$ and $`10^{11}`$ for the four periodic
  functions;
- $`1\le Z<2`$.

Together these give $`Z\,D(f)\le-2.27\cdot10^{-43}+1.3\cdot10^{-48}`$, hence
$`D(f)<-10^{-43}`$ ([DensityNeg.lean](lean/Fisher41/Static/DensityNeg.lean),
[DBound.lean](lean/Fisher41/Fixed/DBound.lean)).

**5. Heat flow.** Write $`f=c\,q\,\gamma_T`$ with $`1\le q\le Q`$ and bounded derivatives of
$`q`$. Then every derivative of $`P_tf`$ up to order 4, and every ratio
$`\partial^\alpha P_tf/P_tf`$, has polynomial-times-Gaussian bounds, uniformly in $`t`$
([Domination.lean](lean/Fisher41/Heat/Domination.lean),
[DensityFlow.lean](lean/Fisher41/Heat/DensityFlow.lean)). The pointwise divergence identities
for $`\partial_t\rho=\tfrac12\Delta\rho`$ ([Identities.lean](lean/Fisher41/Heat/Identities.lean))
are

```math
\partial_t\bigl(\rho|\nabla\log\rho|^2\bigr)=-\rho\,|\nabla^2\log\rho|^2+\operatorname{div}(\cdots),\qquad
\partial_t\bigl(\rho\,|\nabla^2\log\rho|^2\bigr)=-\rho K_\rho+\operatorname{div}(\cdots).
```

Differentiation under the integral sign and integration by parts then give $`I'=-Q`$ and
$`Q'=-D(P_tf)`$ for $`t>0`$ ([Derivatives.lean](lean/Fisher41/Heat/Derivatives.lean)).
Dominated convergence gives two more facts:
- $`D(P_tf)\to D(f)`$ as $`t\to0^+`$ ([Limit.lean](lean/Fisher41/Heat/Limit.lean));
- $`t\mapsto D(P_tf)`$ is continuous on $`(0,\infty)`$
  ([Continuity.lean](lean/Fisher41/Heat/Continuity.lean)).

Hence $`I''=D(P_tf)`$ is continuous, and $`I''<0`$ near $`0`$. A function whose second derivative
is negative on an interval is not convex there.

**In Lean.** The main shortcuts are:
- certificate checking instead of symbolic evaluation;
- crude constants with large margins;
- Gaussian averaging by an elementary $`L^\infty`$ argument;
- existence of $`\varepsilon`$ by continuity, rather than an explicit time.

The 293 numerical cells take most of the build time.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.35.0-rc3` | Complete proof: Mathlib `1b5006ca`, Tau Ceti `e0c8f0ae` |
| [lean4web/](lean4web/) | `v4.35.0-rc3` | Complete proof in one Mathlib-only file, including the parts of Tau Ceti it uses |
| [FClikelean/](FClikelean/) | FC `v4.33.1` | Formal Conjectures statement |
| [PDF/](PDF/) | — | Manuscript, with an OpenTimestamps proof (`.ots`) |
| [certificate/](certificate/), [verify/](verify/) | — | Python interval certificate for the manuscript, and the scripts that regenerate it |

Inside [lean/Fisher41/](lean/Fisher41/):

| Path | Content |
|---|---|
| `Defs.lean`, `Density.lean`, `Statement.lean` | Definitions and final propositions (the trusted statement) |
| `Numerics/` | Interval arithmetic, its soundness, and the 293 kernel-checked cells (`Cells/`) |
| `Static/` | Radial tensor identities, cutoff, periodization, Gaussian averaging, envelope correction |
| `Heat/` | Gaussian heat flow, domination, divergence identities, derivatives, limit and continuity |
| `Fixed/` | Explicit constants for $`R=10^{40}`$ |
| `Main/`, `FC/` | Assembly of the final theorems and the Formal Conjectures target |

The project has 57 modules: about 9,800 hand-written lines, plus about 1,100 lines of generated cells.
[gen_cells.py](lean/scripts/gen_cells.py) regenerates the cells from
[partition_293.json](lean/data/partition_293.json).

## Verification

```bash
cd lean
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

The final theorems depend only on `[propext, Classical.choice, Quot.sound]`. The full audit
(`python3 lean/scripts/build_audit.py`) records its results in [lean/evidence/](lean/evidence/).

The interval certificate in [certificate/](certificate/) is independent of the Lean proof. To
regenerate it with Python 3 (standard library only), run from the repository root:

```bash
python3 -B verify/verify_integral.py
python3 -B verify/check_constants.py
```

## Status boundary

Proved here, for the explicit density $`f`$ on $`\mathbb R^{41}`$ with $`R=10^{40}`$:

```text
f is an admissible density in the sense of the paper: a positive Schwartz probability density
with finite I, Q, D and Q > 0.
D(f) < -10^-44 (in fact < -10^-43).
I_f(t) is finite for every t > 0 and twice continuously differentiable on (0, ∞).
I_f''(t) < 0 for all 0 < t < ε, for some ε > 0; hence I_f is not convex on (0, ∞).
```

The following are not claimed or not formalized:
- **Choice of ε.** The value of $`\varepsilon`$ is obtained by continuity, not computed.
- **Scope.** The proof says nothing about the smallest counterexample dimension, about low
  dimensions, or about priority.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced
by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol,
and Claude Code using Claude Opus 5.5.

## References

- [ZFGW26] J. Zou, L. Fan, J. Gao and J. Wang,
  [A Hexagonal Counterexample to Log-Convexity of Fisher Information Along the Heat Flow](https://arxiv.org/abs/2605.18081),
  arXiv:2605.18081 (2026), Sections 2 and 7.2–7.3.
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (revision `e0c8f0ae`, Apache 2.0): heat
  kernel and convolution lemmas. The proof depends on Tau Ceti, and the Lean4Web file includes
  the parts it uses.
- [Mathlib](https://github.com/leanprover-community/mathlib4).
- [Formal Conjectures contribution guide](https://github.com/google-deepmind/formal-conjectures/blob/7fa51437bb6717db269e4f5449b2845085c7f545/CONTRIBUTING.md),
  at the commit used to check the statement file.

## Appendix: the original statement and a variant statement

| Condition on $`f`$ | Original | Variant |
|---|---|---|
| Regularity | Schwartz | smooth |
| $`f>0`$ | yes | yes |
| $`\int f=1`$ | yes | yes |
| $`\mathcal I[f]<\infty`$ | yes | yes |
| $`\mathcal Q[f]<\infty`$ | yes | — |
| $`\mathcal D[f]<\infty`$ | yes | — |
| $`\mathcal Q[f]>0`$ | yes | — |

### Natural language comparison: original statement vs variant statement

The original statement is the following.

> For every $`d\ge1`$ and every positive Schwartz probability density $`f`$ on $`\mathbb R^d`$
> with $`\mathcal I[f],\mathcal Q[f],\mathcal D[f]<\infty`$ and $`\mathcal Q[f]>0`$, the function
> $`I_f`$ is convex on $`(0,\infty)`$.

The variant statement is the following.

> For every $`d\ge1`$ and every smooth positive probability density $`f`$ on $`\mathbb R^d`$ with
> $`\mathcal I[f]<\infty`$, the function $`I_f`$ is convex on $`(0,\infty)`$.

Here $`H=-\nabla^2\log f`$, $`\mathcal I[f]=\int|\nabla\log f|^2f`$,
$`\mathcal Q[f]=\int\operatorname{tr}(H^2)f`$ and
$`\mathcal D[f]=\int(|\nabla H|^2+2\operatorname{tr}H^3)f`$.

The variant has no conditions on $`\mathcal Q[f]`$ and $`\mathcal D[f]`$, and it asks for
smoothness instead of the Schwartz condition. So its conditions are weaker, and every density
allowed in the original statement is also allowed in the variant. That is, if the original
statement is false, then the variant is also false: a counterexample to the original statement
is also a counterexample to the variant. This repository shows that the original statement is
false, so the variant is false as well.

### Lean comparison: original statement vs variant statement

The original statement is `Arxiv.«2605.18081».fisherInformationConvexity` and the variant is
`Arxiv.«2605.18081».fisherInformationConvexity.variants.smooth`
([Fisher41/FC/Main.lean](lean/Fisher41/FC/Main.lean)). As shown in the
[Formal Conjectures target](#formal-conjectures-target), the two theorems differ only in the
condition on `f`. The seven conjuncts of `IsAdmissible` are the rows of the table, in order, and
the four conjuncts of `IsWeaklyAdmissible` are its first four rows. Here `negLogHess f i j x` is
$`H_{ij}(x)`$.

```lean
def IsAdmissible {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  (∃ φ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ), ⇑φ = f) ∧ (∀ x, 0 < f x) ∧ ∫ x, f x = 1 ∧
    Integrable (fun x => ‖fderiv ℝ (fun y => log (f y)) x‖ ^ 2 * f x) ∧
    Integrable (fun x => (∑ i, ∑ j, negLogHess f i j x ^ 2) * f x) ∧
    Integrable (fun x => ((∑ i, ∑ j, ∑ k,
        fderiv ℝ (negLogHess f i j) x (EuclideanSpace.single k 1) ^ 2) +
      2 * ∑ i, ∑ j, ∑ k, negLogHess f i j x * negLogHess f j k x * negLogHess f k i x) * f x) ∧
    0 < ∫ x, (∑ i, ∑ j, negLogHess f i j x ^ 2) * f x

def IsWeaklyAdmissible {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ x, 0 < f x) ∧ ∫ x, f x = 1 ∧
    Integrable (fun x => ‖fderiv ℝ (fun y => log (f y)) x‖ ^ 2 * f x)
```

The Lean proof of the original statement uses the explicit density `fPDF` on $`\mathbb R^{41}`$
and proves that it satisfies `IsAdmissible` (`fPDF_isAdmissible`).
