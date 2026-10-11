/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.FC.Admissible
import Fisher41.Main.Theorems

/-!
# The Formal Conjectures targets

The statements of `FClikelean/FisherInformationConvexity.lean`, over the same definitions
(`Fisher41/FC/Statement.lean`), here proved: the answer is `False` in both cases.

* `fisherInformationConvexity`: admissible densities in the sense of Zou–Fan–Gao–Wang; witnessed
  by the manuscript's density `Fisher41.fPDF`, which is admissible (`fPDF_isAdmissible`).
* `fisherInformationConvexity.variants.smooth`: smooth positive probability densities with
  finite Fisher information.
-/

open MeasureTheory Real
open scoped ContDiff

/-- Formal Conjectures' `answer(False)` elaborates to `False`; this identity macro preserves
that type. -/
macro "answer(" t:term ")" : term => pure t

namespace Arxiv.«2605.18081»

/-- The statement's Fisher information along the heat flow is the project's one. -/
theorem fisherInformation_heatFlow_eq {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    (fun t => fisherInformation (heatFlow f t)) = fun t => Fisher41.fisher (Fisher41.heat f t) := by
  funext t
  rw [fisherInformation_eq, heatFlow_eq]

/-- **Formal Conjectures target**: the Fisher information along the heat flow is not convex for
every admissible density. -/
theorem fisherInformationConvexity :
    answer(False) ↔
      ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsAdmissible f →
        ConvexOn ℝ (Set.Ioi 0) (fun t => fisherInformation (heatFlow f t)) := by
  refine ⟨False.elim, fun h => ?_⟩
  have hc := h 41 Fisher41.fPDF fPDF_isAdmissible
  rw [fisherInformation_heatFlow_eq] at hc
  exact Fisher41.pdfMain.2.2 hc

/-- **Formal Conjectures target (variant)**: the Fisher information along the heat flow is not
convex for every smooth positive probability density with finite Fisher information. -/
theorem fisherInformationConvexity.variants.smooth :
    answer(False) ↔
      ∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), IsWeaklyAdmissible f →
        ConvexOn ℝ (Set.Ioi 0) (fun t => fisherInformation (heatFlow f t)) := by
  refine ⟨False.elim, fun h => ?_⟩
  obtain ⟨f, hf, hnc⟩ := Fisher41.fisherNonconvex
  have hfi : Integrable (fun x => ‖fderiv ℝ (fun y => log (f y)) x‖ ^ 2 * f x) := by
    rw [fisherIntegrand_eq]
    exact hf.fisher_integrable
  have hc := h 41 f ⟨hf.smooth, hf.pos, hf.mass_one, hfi⟩
  rw [fisherInformation_heatFlow_eq] at hc
  exact hnc hc

end Arxiv.«2605.18081»
