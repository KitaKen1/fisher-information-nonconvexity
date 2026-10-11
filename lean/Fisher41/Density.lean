/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Defs
import Fisher41.Static.Cutoff
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The explicit density of the manuscript (part of the trusted statement)

`V(s) = 15 - 2s - s²`, `u(s) = (4/3) log(1 + e^{V(s)})`, `ũ(s) = η(s/16) u(s)`,
`w(x) = ũ(|x|²/2)`, `U(x) = Σ_{z ∈ ℤ⁴¹} w(x - 20 z)` (a locally finite sum, written with
`finsum`), `q = e^U`, `R = 10^40`, `Z = ∫ q γ_{R²}`, `f = q γ_{R²} / Z`.
The Gaussian subscript is the **variance**, so the envelope is `gaussian 41 (R^2)`.
-/

open MeasureTheory Real

noncomputable section

namespace Fisher41

/-- `V(s) = 15 - 2s - s²`. -/
def Vfun (s : ℝ) : ℝ := 15 - 2 * s - s ^ 2

/-- The radial log-profile `u(s) = (4/3) log(1 + e^{V(s)})`. -/
def uprof (s : ℝ) : ℝ := (4 / 3) * Real.log (1 + Real.exp (Vfun s))

/-- The cut-off profile `ũ(s) = η(s/16) u(s)`, supported in `s ≤ 32`. -/
def ucut (s : ℝ) : ℝ := eta (s / 16) * uprof s

/-- One bump `w(x) = ũ(|x|²/2)`, supported in the closed ball of radius 8. -/
def bump (x : E 41) : ℝ := ucut (‖x‖ ^ 2 / 2)

/-- The lattice point `20 z`. -/
def latt (z : Fin 41 → ℤ) : E 41 := WithLp.toLp 2 (fun i => 20 * (z i : ℝ))

/-- The periodic log-density `U(x) = Σ_z w(x - 20 z)` (finitely many nonzero terms). -/
def Uper (x : E 41) : ℝ := ∑ᶠ z : Fin 41 → ℤ, bump (x - latt z)

/-- The periodic density `q = e^U ≥ 1`. -/
def qper (x : E 41) : ℝ := Real.exp (Uper x)

/-- The Gaussian standard deviation `R = 10^40`. -/
def Rstd : ℝ := 10 ^ 40

/-- Normalized density with envelope of standard deviation `R`. -/
def fR (R : ℝ) (x : E 41) : ℝ :=
  qper x * gaussian 41 (R ^ 2) x / ∫ y, qper y * gaussian 41 (R ^ 2) y

/-- The density of the manuscript: `f = q γ_{R²} / Z` with `R = 10^40`. -/
def fPDF : E 41 → ℝ := fR Rstd

end Fisher41
