/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Main.Theorems
import Fisher41.Heat.Continuity

/-!
# Theorem 1 of the manuscript

`paperTheorem1`: for the manuscript's density (`R = 10^40`), `D(f) < -10⁻⁴⁴`; the Fisher
information is finite at every positive time and `C²` on `(0, ∞)` with `I'' = D(P_t f)`; hence
`I'' < 0` on some `(0, ε)`, and `I` is not convex on `(0, ∞)`.
-/

open MeasureTheory Real

noncomputable section

namespace Fisher41

/-- **Theorem 1 of the manuscript** (`PaperTheorem1`). -/
theorem paperTheorem1 : PaperTheorem1 := by
  obtain ⟨Q, H⟩ := exists_densityFlowHyp_fR Rstd_pos
  obtain ⟨hC2, hI2⟩ := contDiffOn_two_of_identities
    (I := fun s => fisher (heat fPDF s))
    (Qf := fun s => ∫ x, heat fPDF s x *
      ∑ i, ∑ j, (pd (pd (fun z => Real.log (heat fPDF s z)) i) j x) ^ 2)
    (Dt := fun s => Dfun (heat fPDF s))
    (fun t ht => H.hasDerivAt_fisher_flow ht) (fun t ht => H.hasDerivAt_hessFisher_flow ht)
    H.continuousOn_Dfun_flow
  obtain ⟨ε, hε, hneg⟩ := H.exists_Dfun_flow_neg Dfun_fPDF_neg
  refine ⟨admissible_fR Rstd_pos, Dfun_fPDF_lt, fun t ht => H.integrable_fisherDensity_flow ht,
    hC2, ⟨ε, hε, fun t ht => ?_⟩, pdfMain.2.2⟩
  rw [hI2 t ht.1]
  exact hneg t ht

end Fisher41
