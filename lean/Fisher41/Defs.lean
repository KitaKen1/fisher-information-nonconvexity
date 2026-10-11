/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Basic definitions (part of the trusted statement)

Everything the final theorem mentions is defined here, deliberately in elementary terms:

* `E d` is `EuclideanSpace ℝ (Fin d)` (Euclidean norm, Lebesgue volume);
* `gaussian d t` is the Gaussian density of **variance** `t`, so the heat flow
  `heat f t = f * gaussian d t` solves `∂ₜ = ½ Δ`;
* derivatives are coordinate partial derivatives `pd` (Fréchet derivative applied to the
  standard basis vector), and tensor norms/traces are finite sums;
* `fisher ρ = ∫ ρ |∇ log ρ|²`, `Dfun ρ = ∫ ρ K_ρ` with
  `K = Σ (∂ₖHᵢⱼ)² + 2 Σ HᵢⱼHⱼₖHₖᵢ` and `H = -∇² log ρ`.

Lean integrals and derivatives are total; the theorems therefore carry the needed
integrability and differentiability statements explicitly.
-/

open MeasureTheory Real
open scoped ContDiff

noncomputable section

namespace Fisher41

/-- Euclidean space of dimension `d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Gaussian density with **variance** `t`: `(2πt)^(-d/2) exp(-|x|²/(2t))`. -/
def gaussian (d : ℕ) (t : ℝ) (x : E d) : ℝ :=
  (2 * π * t) ^ (-(d : ℝ) / 2) * exp (-‖x‖ ^ 2 / (2 * t))

/-- Heat flow `P_t f = f * γ_t` (meaningful for `t > 0`). -/
def heat {d : ℕ} (f : E d → ℝ) (t : ℝ) (x : E d) : ℝ :=
  ∫ y, f y * gaussian d t (x - y)

/-- Coordinate partial derivative `∂ᵢ g`. -/
def pd {d : ℕ} (g : E d → ℝ) (i : Fin d) (x : E d) : ℝ :=
  fderiv ℝ g x (EuclideanSpace.single i 1)

/-- Fisher information integrand `ρ |∇ log ρ|²`. -/
def fisherDensity {d : ℕ} (ρ : E d → ℝ) (x : E d) : ℝ :=
  ρ x * ∑ i, (pd (fun y => log (ρ y)) i x) ^ 2

/-- Fisher information `∫ ρ |∇ log ρ|²`. -/
def fisher {d : ℕ} (ρ : E d → ℝ) : ℝ := ∫ x, fisherDensity ρ x

/-- `Hᵢⱼ = -∂ⱼ∂ᵢ log ρ`. -/
def negHess {d : ℕ} (ρ : E d → ℝ) (i j : Fin d) (x : E d) : ℝ :=
  -pd (pd (fun y => log (ρ y)) i) j x

/-- `K_ρ = Σᵢⱼₖ (∂ₖHᵢⱼ)² + 2 Σᵢⱼₖ HᵢⱼHⱼₖHₖᵢ`. -/
def kernelK {d : ℕ} (ρ : E d → ℝ) (x : E d) : ℝ :=
  (∑ i, ∑ j, ∑ k, (pd (negHess ρ i j) k x) ^ 2) +
    2 * ∑ i, ∑ j, ∑ k, negHess ρ i j x * negHess ρ j k x * negHess ρ k i x

/-- `D(ρ) = ∫ ρ K_ρ`. -/
def Dfun {d : ℕ} (ρ : E d → ℝ) : ℝ := ∫ x, ρ x * kernelK ρ x

/-- Admissible initial density: positive, smooth (`∞`, *not* `⊤` = analytic),
integrable with mass one, and with integrable Fisher integrand. -/
structure Admissible {d : ℕ} (f : E d → ℝ) : Prop where
  pos : ∀ x, 0 < f x
  smooth : ContDiff ℝ ∞ f
  integrable : Integrable f
  mass_one : ∫ x, f x = 1
  fisher_integrable : Integrable (fisherDensity f)

/-- The radial kernel: for `p = exp (u (|x|²/2))` in dimension `d`, with `a = -u'`,
`B = u''`, `C = u'''` at `s = |x|²/2`, one has `K_p = Kd d s a B C`. -/
def Kd (d : ℕ) (s a B C : ℝ) : ℝ :=
  8 * s ^ 3 * C ^ 2 + 24 * s ^ 2 * B * C + 6 * ((d : ℝ) + 2) * s * B ^ 2 +
    2 * (((d : ℝ) - 1) * a ^ 3 + (a - 2 * s * B) ^ 3)

end Fisher41
