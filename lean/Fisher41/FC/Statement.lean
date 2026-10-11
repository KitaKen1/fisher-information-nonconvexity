/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Definitions copied from `FClikelean/FisherInformationConvexity.lean`

The definitions below are copied verbatim from the Formal Conjectures statement file (checked by
`scripts/build_audit.py`). `Fisher41/FC/Main.lean` relates them to the project's definitions.
-/

open MeasureTheory Real
open scoped ContDiff SchwartzMap

namespace Arxiv.«2605.18081»

/-- The heat flow $f * \gamma_t$, where $\gamma_t$ is the Gaussian density of variance $t$. -/
noncomputable def heatFlow {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ y, f y * ((2 * π * t) ^ (-(d : ℝ) / 2) * exp (-‖x - y‖ ^ 2 / (2 * t)))

/-- The Fisher information $\int |\nabla \log \rho|^2 \rho$. -/
noncomputable def fisherInformation {d : ℕ} (ρ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∫ x, ‖fderiv ℝ (fun y => log (ρ y)) x‖ ^ 2 * ρ x

/-- The entries $H_{ij} = -\partial_i \partial_j \log f$ of the negative log-Hessian. -/
noncomputable def negLogHess {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (i j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -fderiv ℝ (fun y => fderiv ℝ (fun z => log (f z)) y (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single j 1)

/-- The admissible densities of [ZFGW26, Section 7]: positive Schwartz probability densities with
$\mathcal{I}[f], \mathcal{Q}[f], \mathcal{D}[f] < \infty$ and $\mathcal{Q}[f] > 0$, where
$\mathcal{Q}[f] = \int \operatorname{tr}(H^2) f$ and
$\mathcal{D}[f] = \int (|\nabla H|^2 + 2 \operatorname{tr} H^3) f$. -/
def IsAdmissible {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  (∃ φ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ), ⇑φ = f) ∧ (∀ x, 0 < f x) ∧ ∫ x, f x = 1 ∧
    Integrable (fun x => ‖fderiv ℝ (fun y => log (f y)) x‖ ^ 2 * f x) ∧
    Integrable (fun x => (∑ i, ∑ j, negLogHess f i j x ^ 2) * f x) ∧
    Integrable (fun x => ((∑ i, ∑ j, ∑ k,
        fderiv ℝ (negLogHess f i j) x (EuclideanSpace.single k 1) ^ 2) +
      2 * ∑ i, ∑ j, ∑ k, negLogHess f i j x * negLogHess f j k x * negLogHess f k i x) * f x) ∧
    0 < ∫ x, (∑ i, ∑ j, negLogHess f i j x ^ 2) * f x

/-- The class of the variant: smooth positive probability densities with finite Fisher
information. Compared with `IsAdmissible`, the Schwartz condition is replaced by smoothness, and
the conditions on $\mathcal{Q}$ and $\mathcal{D}$ are dropped. -/
def IsWeaklyAdmissible {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ x, 0 < f x) ∧ ∫ x, f x = 1 ∧
    Integrable (fun x => ‖fderiv ℝ (fun y => log (f y)) x‖ ^ 2 * f x)

end Arxiv.«2605.18081»
