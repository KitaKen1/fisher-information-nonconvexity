/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Defs
import Fisher41.Density

/-!
# The target statements (Challenge file)

These `Prop`s are the trusted interface: the final theorems are stated as proofs of exactly
these propositions, so the statement cannot drift while proofs are developed.
Review this file together with `Fisher41/Defs.lean` and `Fisher41/Density.lean`.
-/

open MeasureTheory

namespace Fisher41

/-- **Headline.** Some admissible density on `ℝ⁴¹` has non-convex Fisher information along the
Gaussian heat flow. -/
def FisherNonconvex : Prop :=
  ∃ f : E 41 → ℝ, Admissible f ∧ ¬ ConvexOn ℝ (Set.Ioi 0) (fun t => fisher (heat f t))

/-- **Strong form.** Genuine integrability at every positive time, and actual first and second
derivatives of the Fisher information that are negative on some `(0, ε)`. -/
def FisherSecondDerivNeg : Prop :=
  ∃ f : E 41 → ℝ, Admissible f ∧
    (∀ t : ℝ, 0 < t → Integrable (fisherDensity (heat f t))) ∧
    ∃ ε > 0, ∃ I₁ I₂ : ℝ → ℝ, ∀ t ∈ Set.Ioo 0 ε,
      HasDerivAt (fun s => fisher (heat f s)) (I₁ t) t ∧
      HasDerivAt I₁ (I₂ t) t ∧ I₂ t < 0

/-- **The manuscript's density** (`R = 10^40`): admissible, `D(f) < -10⁻⁴⁴`, and non-convex
Fisher information along the heat flow. -/
def PDFMain : Prop :=
  Admissible fPDF ∧ Dfun fPDF < -(10 : ℝ) ^ (-44 : ℤ) ∧
    ¬ ConvexOn ℝ (Set.Ioi 0) (fun t => fisher (heat fPDF t))

/-- **Theorem 1 of the manuscript.** For the explicit density `f` (`R = 10^40`): `f` is
admissible and `D(f) < -10⁻⁴⁴`; the Fisher information is finite at every positive time; the
map `I(t) = fisher (heat f t)` is twice continuously differentiable on `(0, ∞)`; there is
`ε > 0` with `I''(t) < 0` for `0 < t < ε`; in particular `I` is not convex on `(0, ∞)`. -/
def PaperTheorem1 : Prop :=
  Admissible fPDF ∧ Dfun fPDF < -(10 : ℝ) ^ (-44 : ℤ) ∧
    (∀ t : ℝ, 0 < t → Integrable (fisherDensity (heat fPDF t))) ∧
    ContDiffOn ℝ 2 (fun t => fisher (heat fPDF t)) (Set.Ioi 0) ∧
    (∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε, deriv (deriv fun s => fisher (heat fPDF s)) t < 0) ∧
    ¬ ConvexOn ℝ (Set.Ioi 0) (fun t => fisher (heat fPDF t))

end Fisher41
