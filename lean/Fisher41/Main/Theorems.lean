/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Statement
import Fisher41.Main.FlowHyp
import Fisher41.Main.Assembly
import Fisher41.Heat.Derivatives
import Fisher41.Fixed.DBound

/-!
# The main theorems

* `fisherSecondDerivNeg`, `fisherNonconvex`: for some `R` (from the qualitative static
  argument, independent of the explicit constants), the density `f_R` has Fisher information
  with a negative second derivative near `0`; hence it is not convex along the heat flow.
* `pdfMain`: the manuscript's density (`R = 10^40`) is admissible, `D(f) < -10⁻⁴⁴`, and its
  Fisher information is not convex along the heat flow.
-/

open MeasureTheory Real

noncomputable section

namespace Fisher41

/-- For every `f_R` with `D(f_R) < 0`: finite Fisher information at all positive times, and
actual first and second time derivatives with the second one negative on some `(0, ε)`. -/
theorem fR_secondDerivNeg {R : ℝ} (hR : 0 < R) (hD : Dfun (fR R) < 0) :
    (∀ t : ℝ, 0 < t → Integrable (fisherDensity (heat (fR R) t))) ∧
    ∃ ε > 0, ∃ I₁ I₂ : ℝ → ℝ, ∀ t ∈ Set.Ioo 0 ε,
      HasDerivAt (fun s => fisher (heat (fR R) s)) (I₁ t) t ∧
      HasDerivAt I₁ (I₂ t) t ∧ I₂ t < 0 := by
  obtain ⟨Q, H⟩ := exists_densityFlowHyp_fR hR
  exact ⟨fun t ht => H.integrable_fisherDensity_flow ht,
    exists_deriv2_neg_of_identities H hD
      (Qf := fun s => ∫ x, heat (fR R) s x *
        ∑ i, ∑ j, (pd (pd (fun z => Real.log (heat (fR R) s z)) i) j x) ^ 2)
      (fun t ht => H.hasDerivAt_fisher_flow ht) (fun t ht => H.hasDerivAt_hessFisher_flow ht)⟩

/-- **Strong form** (`FisherSecondDerivNeg`). -/
theorem fisherSecondDerivNeg : FisherSecondDerivNeg := by
  obtain ⟨R, hR, hD⟩ := exists_Dfun_fR_neg
  exact ⟨fR R, admissible_fR hR, fR_secondDerivNeg hR hD⟩

/-- **Headline** (`FisherNonconvex`): some admissible density on `ℝ⁴¹` has non-convex Fisher
information along the Gaussian heat flow. -/
theorem fisherNonconvex : FisherNonconvex := by
  obtain ⟨f, hf, -, ε, hε, I₁, I₂, h⟩ := fisherSecondDerivNeg
  exact ⟨f, hf, not_convexOn_Ioi_of_deriv2_neg hε h⟩

/-- `R = 10^40` is positive. -/
theorem Rstd_pos : 0 < Rstd := by norm_num [Rstd]

/-- `D(f) < 0` for the manuscript's density. -/
theorem Dfun_fPDF_neg : Dfun fPDF < 0 := by
  have h : (0 : ℝ) < (10 : ℝ) ^ (-44 : ℤ) := by positivity
  linarith [Dfun_fPDF_lt]

/-- **The manuscript's density** (`PDFMain`): admissible, `D(f) < -10⁻⁴⁴`, and non-convex
Fisher information along the heat flow. -/
theorem pdfMain : PDFMain := by
  obtain ⟨-, ε, hε, I₁, I₂, h⟩ := fR_secondDerivNeg Rstd_pos Dfun_fPDF_neg
  exact ⟨admissible_fR Rstd_pos, Dfun_fPDF_lt, not_convexOn_Ioi_of_deriv2_neg hε h⟩

end Fisher41
