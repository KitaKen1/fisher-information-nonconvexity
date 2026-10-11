/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Defs
import Fisher41.Heat.PointwiseAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Field
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

/-!
# Pointwise divergence identities along the heat flow

Let `ρ : ℝ → E d → ℝ` be positive for times near `t`, smooth at time `t`, and assume that `ρ`
and its spatial derivatives solve the heat equation `∂ₜ = ½ Δ` at `(t, x)`. Write `v = log ρ t`,
`w = ∇v`, `A = ∇²v`, `T = ∇³v`. This file proves the analytic versions of `Fisher41.p1_core`
and `Fisher41.p2_core`:

* `Fisher41.hasDerivAt_fisherDensity` (P1):
  `∂ₜ (ρ |∇ log ρ|²) = Σᵢ ∂ᵢ Vᵢ - ρ |A|²` with `Vᵢ = ρ (|w|² wᵢ / 2 + Σⱼ Aᵢⱼ wⱼ)`;
* `Fisher41.hasDerivAt_rho_mul_sum_sq_hess` (P2):
  `∂ₜ (ρ |∇² log ρ|²) = Σₖ ∂ₖ Wₖ - ρ K_ρ` with `Wₖ = ρ (|A|² wₖ / 2 + Σᵢⱼ Aᵢⱼ Tᵢⱼₖ)`;
* `Fisher41.kernelK_eq_sum`: `K_ρ = Σ T² - 2 tr A³`, from `negHess ρ = -A`.

## Hypotheses

P1 only needs the heat equation for `ρ` and `∇ρ` at `(t, x)` and positivity of `ρ s` for `s`
near `t`: the identity `∂ᵢ log g = ∂ᵢ g / g` holds for *every* positive `g`, differentiable or
not (`Fisher41.Identities.logW_eq_div`), so no regularity at times `s ≠ t` is required.

P2 also needs the heat equation for `∇²ρ` at `(t, x)` and that `ρ s` is `C²` at `x` for `s`
near `t` (hypothesis `hreg`). The latter cannot be dropped: if `ρ s` is not twice
differentiable at `x`, then `∂ⱼ∂ᵢ log ρ s` at `x` is a junk value that is not determined by
`ρ s`, `∇ρ s`, `∇²ρ s` at `x`, and one can build a positive `ρ`, smooth at time `t`, satisfying
all the other hypotheses, for which `s ↦ ρ s x |∇² log ρ s|²(x)` is discontinuous at `t`.

## Implementation

* `Fisher41.Identities.IsLogJet ρ w A T Q` records `∂ρ = ρ w`, `∂w = A`, `∂A = T`, `∂T = Q`,
  the symmetry of `A` and the differentiability of `ρ, w, A, T`. From it, the derivatives of
  `ρ` up to order four are expressed through `w, A, T, Q`, and the divergences of the two fluxes
  are computed. The logarithmic derivatives of a smooth positive function form such a jet
  (`Fisher41.Identities.isLogJet_log`).
* The time derivatives of `w` and `A` at `(t, x)` follow from the heat equation by the quotient
  rule (`Fisher41.Identities.hasDerivAt_logW`, `Fisher41.Identities.hasDerivAt_logA`).
* The identities are closed with `Fisher41.p1_core_of_symm` and `Fisher41.p2_core_of_symm`.
-/

open scoped Topology ContDiff

noncomputable section

namespace Fisher41

namespace Identities

variable {d : ℕ}

/-! ### Calculus rules for the coordinate partial derivative `pd` -/

/-- Dividing a differentiable function on `E d` by a constant (a `fun_prop` rule). -/
@[fun_prop]
theorem differentiableAt_div_const {f : E d → ℝ} {x : E d} (hf : DifferentiableAt ℝ f x)
    (c : ℝ) : DifferentiableAt ℝ (fun y => f y / c) x := by
  simpa only [div_eq_mul_inv] using hf.mul_const c⁻¹

/-- Sum rule for `pd`. -/
theorem pd_add {f g : E d → ℝ} {x : E d} {i : Fin d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : pd (fun y => f y + g y) i x = pd f i x + pd g i x := by
  simp only [pd, fderiv_fun_add hf hg, _root_.add_apply]

/-- Product rule for `pd`. -/
theorem pd_mul {f g : E d → ℝ} {x : E d} {i : Fin d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  simp only [pd, fderiv_fun_mul hf hg, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- `pd` commutes with finite sums. -/
theorem pd_sum {ι : Type*} (s : Finset ι) {f : ι → E d → ℝ} {x : E d} {i : Fin d}
    (hf : ∀ k ∈ s, DifferentiableAt ℝ (f k) x) :
    pd (fun y => ∑ k ∈ s, f k y) i x = ∑ k ∈ s, pd (f k) i x := by
  simp only [pd, fderiv_fun_sum hf, _root_.sum_apply]

/-- `pd` of a quotient by a constant. -/
theorem pd_div_const {f : E d → ℝ} {x : E d} {i : Fin d} (hf : DifferentiableAt ℝ f x)
    (c : ℝ) : pd (fun y => f y / c) i x = pd f i x / c := by
  rw [show (fun y => f y / c) = fun y => f y * c⁻¹ from funext fun y => div_eq_mul_inv _ _]
  simp only [pd, fderiv_mul_const hf, _root_.smul_apply, smul_eq_mul]
  ring

/-- `pd` of a square. -/
theorem pd_sq {f : E d → ℝ} {x : E d} {i : Fin d} (hf : DifferentiableAt ℝ f x) :
    pd (fun y => f y ^ 2) i x = 2 * f x * pd f i x := by
  rw [show (fun y => f y ^ 2) = fun y => f y * f y from funext fun y => sq (f y), pd_mul hf hf]
  ring

/-- `pd` of a negation; no differentiability is needed. -/
theorem pd_neg (f : E d → ℝ) (i : Fin d) (x : E d) : pd (fun y => -f y) i x = -pd f i x := by
  simp only [pd, fderiv_fun_neg, _root_.neg_apply]

/-- `pd` of a reciprocal. -/
theorem pd_inv {g : E d → ℝ} {x : E d} {i : Fin d} (hg : DifferentiableAt ℝ g x)
    (hx : g x ≠ 0) : pd (fun y => (g y)⁻¹) i x = -pd g i x / g x ^ 2 := by
  have h : HasFDerivAt (fun y => (g y)⁻¹) ((-(g x ^ 2)⁻¹) • fderiv ℝ g x) x :=
    (hasDerivAt_inv hx).comp_hasFDerivAt x hg.hasFDerivAt
  simp only [pd, h.fderiv, _root_.smul_apply, smul_eq_mul]
  ring

/-- Quotient rule for `pd`. -/
theorem pd_div {f g : E d → ℝ} {x : E d} {i : Fin d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hx : g x ≠ 0) :
    pd (fun y => f y / g y) i x = (pd f i x * g x - f x * pd g i x) / g x ^ 2 := by
  rw [show (fun y => f y / g y) = fun y => f y * (g y)⁻¹ from
    funext fun y => div_eq_mul_inv _ _, pd_mul hf (hg.fun_inv hx), pd_inv hg hx]
  field

/-- Partial derivatives of smooth functions are smooth. -/
theorem contDiff_pd {f : E d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ContDiff ℝ ∞ (pd f i) := by
  show ContDiff ℝ ∞ fun y => fderiv ℝ f y (EuclideanSpace.single i 1)
  exact (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

/-- Smooth functions are differentiable. -/
theorem differentiable_of_contDiff {f : E d → ℝ} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ f :=
  (contDiff_infty_iff_fderiv.1 hf).1

/-- A second partial derivative is a value of the second Fréchet derivative. -/
theorem pd_pd_eq_fderiv {f : E d → ℝ} {y : E d} (hf : DifferentiableAt ℝ (fderiv ℝ f) y)
    (i j : Fin d) :
    pd (pd f i) j y =
      fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  have h : HasFDerivAt (fun z => fderiv ℝ f z (EuclideanSpace.single i (1 : ℝ)))
      ((fderiv ℝ (fderiv ℝ f) y).flip (EuclideanSpace.single i 1)) y := by
    simpa using
      hf.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) y)
  have e : pd f i = fun z => fderiv ℝ f z (EuclideanSpace.single i (1 : ℝ)) := rfl
  rw [pd, e, h.fderiv, ContinuousLinearMap.flip_apply]

/-- Schwarz's theorem in coordinates: second partial derivatives of a smooth function
commute. -/
theorem pd_pd_comm {f : E d → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin d) :
    pd (pd f i) j = pd (pd f j) i := by
  funext y
  have h2 : ContDiff ℝ 2 f := contDiff_infty.1 hf 2
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (contDiff_infty_iff_fderiv.1 (contDiff_infty_iff_fderiv.1 hf).2).1 y
  rw [pd_pd_eq_fderiv hd i j, pd_pd_eq_fderiv hd j i]
  exact (h2.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-! ### Logarithmic derivatives -/

/-- The first logarithmic derivative `∂ᵢ log g`. -/
def logW (g : E d → ℝ) (i : Fin d) : E d → ℝ := pd (fun z => Real.log (g z)) i

/-- The second logarithmic derivative `∂ⱼ∂ᵢ log g`. -/
def logA (g : E d → ℝ) (i j : Fin d) : E d → ℝ := pd (logW g i) j

/-- The third logarithmic derivative `∂ₖ∂ⱼ∂ᵢ log g`. -/
def logT (g : E d → ℝ) (i j k : Fin d) : E d → ℝ := pd (logA g i j) k

/-- The fourth logarithmic derivative `∂ₗ∂ₖ∂ⱼ∂ᵢ log g`. -/
def logQ (g : E d → ℝ) (i j k l : Fin d) : E d → ℝ := pd (logT g i j k) l

/-- For a positive function, `∂ᵢ log g = ∂ᵢ g / g` holds at every point, whether or not `g` is
differentiable there (if it is not, then neither is `log g`, and both sides vanish). -/
theorem logW_eq_div {g : E d → ℝ} (hpos : ∀ y, 0 < g y) (i : Fin d) (y : E d) :
    logW g i y = pd g i y / g y := by
  by_cases hg : DifferentiableAt ℝ g y
  · simp only [logW, pd]
    rw [(hg.hasFDerivAt.log (hpos y).ne').fderiv, _root_.smul_apply, smul_eq_mul,
      inv_mul_eq_div]
  · have hl : ¬DifferentiableAt ℝ (fun z => Real.log (g z)) y := fun hl => hg <| by
      have h := hl.exp
      rwa [show (fun z => Real.exp (Real.log (g z))) = g from
        funext fun z => Real.exp_log (hpos z)] at h
    simp only [logW, pd, fderiv_zero_of_not_differentiableAt hg,
      fderiv_zero_of_not_differentiableAt hl, _root_.zero_apply, zero_div]

/-- If `g > 0` is `C²` at `x`, then `∂ⱼ∂ᵢ log g = (∂ⱼ∂ᵢ g · g - ∂ᵢ g ∂ⱼ g) / g²` at `x`. -/
theorem logA_eq_div {g : E d → ℝ} {x : E d} (hpos : ∀ y, 0 < g y) (hg : ContDiffAt ℝ 2 g x)
    (i j : Fin d) :
    logA g i j x = (pd (pd g i) j x * g x - pd g i x * pd g j x) / g x ^ 2 := by
  have hw : logW g i = fun y => pd g i y / g y := funext (logW_eq_div hpos i)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hgi : DifferentiableAt ℝ (pd g i) x := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
    show DifferentiableAt ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) x
    exact (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  rw [logA, hw, pd_div hgi hgd (hpos x).ne']

/-! ### Abstract jets of logarithmic derivatives -/

/-- `IsLogJet ρ w A T Q` says that `w, A, T, Q` behave like the first four derivatives of
`log ρ`: everywhere `∂ᵢρ = ρ wᵢ`, `∂ⱼwᵢ = Aᵢⱼ`, `∂ₖAᵢⱼ = Tᵢⱼₖ` and `∂ₗTᵢⱼₖ = Qᵢⱼₖₗ`, the
matrix `A` is symmetric, and `ρ, w, A, T` are differentiable. -/
structure IsLogJet (ρ : E d → ℝ) (w : Fin d → E d → ℝ) (A : Fin d → Fin d → E d → ℝ)
    (T : Fin d → Fin d → Fin d → E d → ℝ) (Q : Fin d → Fin d → Fin d → Fin d → E d → ℝ) :
    Prop where
  /-- `ρ` is differentiable. -/
  diff_rho : Differentiable ℝ ρ
  /-- Each `wᵢ` is differentiable. -/
  diff_w : ∀ i, Differentiable ℝ (w i)
  /-- Each `Aᵢⱼ` is differentiable. -/
  diff_A : ∀ i j, Differentiable ℝ (A i j)
  /-- Each `Tᵢⱼₖ` is differentiable. -/
  diff_T : ∀ i j k, Differentiable ℝ (T i j k)
  /-- `∂ᵢρ = ρ wᵢ`. -/
  pd_rho : ∀ i y, pd ρ i y = ρ y * w i y
  /-- `∂ⱼwᵢ = Aᵢⱼ`. -/
  pd_w : ∀ i j y, pd (w i) j y = A i j y
  /-- `∂ₖAᵢⱼ = Tᵢⱼₖ`. -/
  pd_A : ∀ i j k y, pd (A i j) k y = T i j k y
  /-- `∂ₗTᵢⱼₖ = Qᵢⱼₖₗ`. -/
  pd_T : ∀ i j k l y, pd (T i j k) l y = Q i j k l y
  /-- `A` is symmetric. -/
  symm : ∀ i j, A i j = A j i

namespace IsLogJet

variable {ρ : E d → ℝ} {w : Fin d → E d → ℝ} {A : Fin d → Fin d → E d → ℝ}
  {T : Fin d → Fin d → Fin d → E d → ℝ} {Q : Fin d → Fin d → Fin d → Fin d → E d → ℝ}

/-- `T` is symmetric in its first two indices. -/
theorem symm_T (J : IsLogJet ρ w A T Q) (i j k : Fin d) (y : E d) :
    T i j k y = T j i k y := by
  rw [← J.pd_A i j k y, ← J.pd_A j i k y, J.symm i j]

/-- `∂ⱼ∂ᵢρ = ρ (Aᵢⱼ + wᵢwⱼ)`. -/
theorem pd_pd_rho (J : IsLogJet ρ w A T Q) (i j : Fin d) (y : E d) :
    pd (pd ρ i) j y = ρ y * (A i j y + w i y * w j y) := by
  rw [show pd ρ i = fun z => ρ z * w i z from funext (J.pd_rho i),
    pd_mul (J.diff_rho y) (J.diff_w i y), J.pd_rho j y, J.pd_w i j y]
  ring

/-- `∂ₖ∂ⱼ∂ᵢρ = ρ (wₖ (Aᵢⱼ + wᵢwⱼ) + Tᵢⱼₖ + Aᵢₖwⱼ + wᵢAⱼₖ)`. -/
theorem pd_pd_pd_rho (J : IsLogJet ρ w A T Q) (i j k : Fin d) (y : E d) :
    pd (pd (pd ρ i) j) k y = ρ y * (w k y * (A i j y + w i y * w j y)
      + (T i j k y + (A i k y * w j y + w i y * A j k y))) := by
  have hρ := J.diff_rho
  have hw := J.diff_w
  have hA := J.diff_A
  rw [show pd (pd ρ i) j = fun z => ρ z * (A i j z + w i z * w j z) from
    funext (J.pd_pd_rho i j)]
  simp (disch := fun_prop) only [pd_mul, pd_add, J.pd_rho, J.pd_w, J.pd_A]
  ring

/-- The fourth derivative `∂ₗ∂ₖ∂ⱼ∂ᵢρ` in terms of `w, A, T, Q`. -/
theorem pd_pd_pd_pd_rho (J : IsLogJet ρ w A T Q) (i j k l : Fin d) (y : E d) :
    pd (pd (pd (pd ρ i) j) k) l y = ρ y * (w l y * (w k y * (A i j y + w i y * w j y)
      + (T i j k y + (A i k y * w j y + w i y * A j k y)))
      + (A k l y * (A i j y + w i y * w j y)
        + w k y * (T i j l y + (A i l y * w j y + w i y * A j l y))
        + (Q i j k l y + (T i k l y * w j y + A i k y * A j l y
          + (A i l y * A j k y + w i y * T j k l y))))) := by
  have hρ := J.diff_rho
  have hw := J.diff_w
  have hA := J.diff_A
  have hT := J.diff_T
  rw [show pd (pd (pd ρ i) j) k = fun z => ρ z * (w k z * (A i j z + w i z * w j z)
      + (T i j k z + (A i k z * w j z + w i z * A j k z))) from funext (J.pd_pd_pd_rho i j k)]
  simp (disch := fun_prop) only [pd_mul, pd_add, J.pd_rho, J.pd_w, J.pd_A, J.pd_T]
  ring

/-- `½ Σₖ ∂ₖ∂ₖρ = ρ (tr A + |w|²) / 2`. -/
theorem half_sum_pd2 (J : IsLogJet ρ w A T Q) (x : E d) :
    (1 / 2) * ∑ k, pd (pd ρ k) k x = ρ x * ((∑ k, A k k x) + ∑ k, w k x ^ 2) / 2 := by
  have hk : ∀ k, pd (pd ρ k) k x = ρ x * A k k x + ρ x * w k x ^ 2 := fun k => by
    rw [J.pd_pd_rho k k x]
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- `½ Σₖ ∂ₖ∂ₖ∂ᵢρ = ρ (2 Σₖ wₖAₖᵢ + wᵢ (|w|² + tr A) + Σₖ Tᵢₖₖ) / 2`. -/
theorem half_sum_pd3 (J : IsLogJet ρ w A T Q) (i : Fin d) (x : E d) :
    (1 / 2) * ∑ k, pd (pd (pd ρ i) k) k x =
      ρ x * (2 * ∑ k, w k x * A k i x + w i x * ((∑ k, w k x ^ 2) + ∑ k, A k k x)
        + ∑ k, T i k k x) / 2 := by
  have hk : ∀ k, pd (pd (pd ρ i) k) k x = 2 * ρ x * (w k x * A k i x)
      + ρ x * w i x * w k x ^ 2 + ρ x * w i x * A k k x + ρ x * T i k k x := by
    intro k
    rw [J.pd_pd_pd_rho i k k x, J.symm k i]
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- `½ Σₖ ∂ₖ∂ₖ∂ⱼ∂ᵢρ` in terms of `w, A, T, Q`. -/
theorem half_sum_pd4 (J : IsLogJet ρ w A T Q) (i j : Fin d) (x : E d) :
    (1 / 2) * ∑ k, pd (pd (pd (pd ρ i) j) k) k x =
      ρ x * (((∑ k, w k x ^ 2) + ∑ k, A k k x) * (A i j x + w i x * w j x)
        + 2 * ∑ k, (A i k x * A j k x + w k x * T i j k x)
        + 2 * w j x * ∑ k, w k x * A k i x + 2 * w i x * ∑ k, w k x * A k j x
        + ∑ k, Q i j k k x + w j x * ∑ k, T i k k x + w i x * ∑ k, T j k k x) / 2 := by
  have hk : ∀ k, pd (pd (pd (pd ρ i) j) k) k x =
      ρ x * (A i j x + w i x * w j x) * w k x ^ 2
        + ρ x * (A i j x + w i x * w j x) * A k k x
        + 2 * ρ x * (A i k x * A j k x + w k x * T i j k x)
        + 2 * ρ x * w j x * (w k x * A k i x) + 2 * ρ x * w i x * (w k x * A k j x)
        + ρ x * Q i j k k x + ρ x * w j x * T i k k x + ρ x * w i x * T j k k x := by
    intro k
    rw [J.pd_pd_pd_pd_rho i j k k x, J.symm k i, J.symm k j]
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Divergence of the flux of P1: `∂ᵢ (ρ (|w|² wᵢ / 2 + Σⱼ Aᵢⱼ wⱼ))`. -/
theorem pd_fluxP1 (J : IsLogJet ρ w A T Q) (i : Fin d) (x : E d) :
    pd (fun y => ρ y * ((∑ k, w k y ^ 2) * w i y / 2 + ∑ j, A i j y * w j y)) i x =
      ρ x * w i x * ((∑ k, w k x ^ 2) * w i x / 2 + ∑ j, A i j x * w j x)
        + ρ x * ((∑ k, w k x * A k i x) * w i x + (∑ k, w k x ^ 2) * A i i x / 2
          + ∑ j, (T i j i x * w j x + A i j x * A j i x)) := by
  have hρ := J.diff_rho
  have hw := J.diff_w
  have hA := J.diff_A
  simp (disch := fun_prop) only [pd_mul, pd_add, pd_div_const, pd_sum, pd_sq, J.pd_rho, J.pd_w,
    J.pd_A]
  have h2 : ∑ k, 2 * w k x * A k i x = 2 * ∑ k, w k x * A k i x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  linear_combination (ρ x * w i x / 2) * h2

/-- Divergence of the flux of P2: `∂ₖ (ρ (|A|² wₖ / 2 + Σᵢⱼ Aᵢⱼ Tᵢⱼₖ))`. -/
theorem pd_fluxP2 (J : IsLogJet ρ w A T Q) (k : Fin d) (x : E d) :
    pd (fun y => ρ y * ((∑ i, ∑ j, A i j y ^ 2) * w k y / 2
        + ∑ i, ∑ j, A i j y * T i j k y)) k x =
      ρ x * w k x * ((∑ i, ∑ j, A i j x ^ 2) * w k x / 2 + ∑ i, ∑ j, A i j x * T i j k x)
        + ρ x * ((∑ i, ∑ j, A i j x * T i j k x) * w k x
          + (∑ i, ∑ j, A i j x ^ 2) * A k k x / 2
          + ∑ i, ∑ j, (T i j k x ^ 2 + A i j x * Q i j k k x)) := by
  have hρ := J.diff_rho
  have hw := J.diff_w
  have hA := J.diff_A
  have hT := J.diff_T
  simp (disch := fun_prop) only [pd_mul, pd_add, pd_div_const, pd_sum, pd_sq, J.pd_rho, J.pd_w,
    J.pd_A, J.pd_T]
  have h1 : ∑ i, ∑ j, 2 * A i j x * T i j k x = 2 * ∑ i, ∑ j, A i j x * T i j k x := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ∑ j, (T i j k x * T i j k x + A i j x * Q i j k k x)
      = ∑ i, ∑ j, (T i j k x ^ 2 + A i j x * Q i j k k x) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  linear_combination (ρ x * w k x / 2) * h1 + ρ x * h2

end IsLogJet

/-- The logarithmic derivatives of a smooth positive function form a log-jet. -/
theorem isLogJet_log {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ y, 0 < g y) :
    IsLogJet g (logW g) (logA g) (logT g) (logQ g) := by
  have hv : ContDiff ℝ ∞ (fun z => Real.log (g z)) := hg.log fun y => (hpos y).ne'
  have hw : ∀ i, ContDiff ℝ ∞ (logW g i) := fun i => contDiff_pd hv i
  have hA : ∀ i j, ContDiff ℝ ∞ (logA g i j) := fun i j => contDiff_pd (hw i) j
  have hT : ∀ i j k, ContDiff ℝ ∞ (logT g i j k) := fun i j k => contDiff_pd (hA i j) k
  exact
    { diff_rho := differentiable_of_contDiff hg
      diff_w := fun i => differentiable_of_contDiff (hw i)
      diff_A := fun i j => differentiable_of_contDiff (hA i j)
      diff_T := fun i j k => differentiable_of_contDiff (hT i j k)
      pd_rho := fun i y => by rw [logW_eq_div hpos i y, mul_div_cancel₀ _ (hpos y).ne']
      pd_w := fun _ _ _ => rfl
      pd_A := fun _ _ _ _ => rfl
      pd_T := fun _ _ _ _ _ => rfl
      symm := fun i j => pd_pd_comm hv i j }

/-- The bridge `K_g = Σ (∂ₖ∂ⱼ∂ᵢ log g)² - 2 tr (∇² log g)³`, in terms of `logT` and `logA`. -/
theorem kernelK_eq_log (g : E d → ℝ) (x : E d) :
    kernelK g x = ∑ i, ∑ j, ∑ k, logT g i j k x ^ 2
      - 2 * ∑ i, ∑ j, ∑ k, logA g i j x * logA g j k x * logA g k i x := by
  have h1 : ∀ i j k, pd (negHess g i j) k x = -logT g i j k x := fun i j k =>
    pd_neg (logA g i j) k x
  have h2 : ∀ i j, negHess g i j x = -logA g i j x := fun _ _ => rfl
  simp only [kernelK, h1, h2, neg_sq, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib]
  ring

/-! ### Time derivatives along the heat flow -/

/-- Time derivative of `r · Σᵢ fᵢ²`. -/
theorem hasDerivAt_mul_sum_sq {ι : Type*} (u : Finset ι) {r : ℝ → ℝ} {r' t : ℝ}
    {f : ℝ → ι → ℝ} {f' : ι → ℝ} (hr : HasDerivAt r r' t)
    (hf : ∀ i ∈ u, HasDerivAt (fun s => f s i) (f' i) t) :
    HasDerivAt (fun s => r s * ∑ i ∈ u, f s i ^ 2)
      (r' * ∑ i ∈ u, f t i ^ 2 + 2 * r t * ∑ i ∈ u, f t i * f' i) t := by
  have hsq : ∀ i ∈ u, HasDerivAt (fun s => f s i ^ 2) (2 * f t i * f' i) t := by
    intro i hi
    convert (hf i hi).fun_pow 2 using 1
    norm_num
  convert hr.fun_mul (HasDerivAt.fun_sum hsq) using 2
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Time derivative of `r · Σᵢ Σⱼ fᵢⱼ²`. -/
theorem hasDerivAt_mul_sum_sum_sq {ι κ : Type*} (u : Finset ι) (v : Finset κ) {r : ℝ → ℝ}
    {r' t : ℝ} {f : ℝ → ι → κ → ℝ} {f' : ι → κ → ℝ} (hr : HasDerivAt r r' t)
    (hf : ∀ i ∈ u, ∀ j ∈ v, HasDerivAt (fun s => f s i j) (f' i j) t) :
    HasDerivAt (fun s => r s * ∑ i ∈ u, ∑ j ∈ v, f s i j ^ 2)
      (r' * ∑ i ∈ u, ∑ j ∈ v, f t i j ^ 2 + 2 * r t * ∑ i ∈ u, ∑ j ∈ v, f t i j * f' i j) t := by
  have hsq : ∀ i ∈ u, ∀ j ∈ v, HasDerivAt (fun s => f s i j ^ 2) (2 * f t i j * f' i j) t := by
    intro i hi j hj
    convert (hf i hi j hj).fun_pow 2 using 1
    norm_num
  convert hr.fun_mul (HasDerivAt.fun_sum fun i hi => HasDerivAt.fun_sum (hsq i hi)) using 2
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Along the heat flow, `∂ₜρ = ρ (tr A + |w|²) / 2` at `(t, x)`. -/
theorem hasDerivAt_rho {ρ : ℝ → E d → ℝ} {t : ℝ} {x : E d}
    (J : IsLogJet (ρ t) (logW (ρ t)) (logA (ρ t)) (logT (ρ t)) (logQ (ρ t)))
    (hρ : HasDerivAt (fun s => ρ s x) ((1 / 2) * ∑ k, pd (pd (ρ t) k) k x) t) :
    HasDerivAt (fun s => ρ s x)
      (ρ t x * ((∑ k, logA (ρ t) k k x) + ∑ k, logW (ρ t) k x ^ 2) / 2) t :=
  hρ.congr_deriv (J.half_sum_pd2 x)

/-- Along the heat flow, `∂ₜwᵢ = (Σₖ Tᵢₖₖ + 2 Σₖ wₖAₖᵢ) / 2` at `(t, x)`. Only positivity is
needed at times `s ≠ t`. -/
theorem hasDerivAt_logW {ρ : ℝ → E d → ℝ} {t : ℝ} {x : E d}
    (J : IsLogJet (ρ t) (logW (ρ t)) (logA (ρ t)) (logT (ρ t)) (logQ (ρ t)))
    (hpos : ∀ᶠ s in 𝓝 t, ∀ y, 0 < ρ s y)
    (hρ : HasDerivAt (fun s => ρ s x) ((1 / 2) * ∑ k, pd (pd (ρ t) k) k x) t) (i : Fin d)
    (hρ₁ : HasDerivAt (fun s => pd (ρ s) i x)
      ((1 / 2) * ∑ k, pd (pd (pd (ρ t) i) k) k x) t) :
    HasDerivAt (fun s => logW (ρ s) i x)
      (((∑ k, logT (ρ t) i k k x) + 2 * ∑ k, logW (ρ t) k x * logA (ρ t) k i x) / 2) t := by
  have hr0 : ρ t x ≠ 0 := (hpos.self_of_nhds x).ne'
  refine ((hρ₁.fun_div hρ hr0).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hpos] with s hs using logW_eq_div hs i x
  · rw [J.half_sum_pd3 i x, J.half_sum_pd2 x, J.pd_rho i x]
    field

/-- Along the heat flow, `∂ₜAᵢⱼ = (Σₖ Qᵢⱼₖₖ + 2 Σₖ (AᵢₖAⱼₖ + wₖTᵢⱼₖ)) / 2` at `(t, x)`. Here
`ρ s` must be `C²` at `x` for `s` near `t`. -/
theorem hasDerivAt_logA {ρ : ℝ → E d → ℝ} {t : ℝ} {x : E d}
    (J : IsLogJet (ρ t) (logW (ρ t)) (logA (ρ t)) (logT (ρ t)) (logQ (ρ t)))
    (hpos : ∀ᶠ s in 𝓝 t, ∀ y, 0 < ρ s y) (hreg : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 (ρ s) x)
    (hρ : HasDerivAt (fun s => ρ s x) ((1 / 2) * ∑ k, pd (pd (ρ t) k) k x) t)
    (hρ₁ : ∀ i, HasDerivAt (fun s => pd (ρ s) i x)
      ((1 / 2) * ∑ k, pd (pd (pd (ρ t) i) k) k x) t)
    (i j : Fin d)
    (hρ₂ : HasDerivAt (fun s => pd (pd (ρ s) i) j x)
      ((1 / 2) * ∑ k, pd (pd (pd (pd (ρ t) i) j) k) k x) t) :
    HasDerivAt (fun s => logA (ρ s) i j x)
      (((∑ k, logQ (ρ t) i j k k x)
        + 2 * ∑ k, (logA (ρ t) i k x * logA (ρ t) j k x + logW (ρ t) k x * logT (ρ t) i j k x))
        / 2) t := by
  have hr0 : ρ t x ≠ 0 := (hpos.self_of_nhds x).ne'
  have hN := (hρ₂.fun_mul hρ).fun_sub ((hρ₁ i).fun_mul (hρ₁ j))
  have hD : HasDerivAt (fun s => ρ s x ^ 2)
      (2 * ρ t x * ((1 / 2) * ∑ k, pd (pd (ρ t) k) k x)) t := by
    convert hρ.fun_pow 2 using 1
    norm_num
  refine ((hN.fun_div hD (pow_ne_zero 2 hr0)).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hpos, hreg] with s hs hs' using logA_eq_div hs hs' i j
  · rw [J.half_sum_pd4 i j x, J.half_sum_pd3 i x, J.half_sum_pd3 j x, J.half_sum_pd2 x,
      J.pd_pd_rho i j x, J.pd_rho i x, J.pd_rho j x]
    field

/-! ### The two divergence identities, in terms of `logW`, `logA`, `logT` -/

/-- P1, stated with `logW` and `logA` (see `Fisher41.hasDerivAt_fisherDensity`). -/
theorem hasDerivAt_fisher_aux {ρ : ℝ → E d → ℝ} {t : ℝ} {x : E d}
    (hpos : ∀ᶠ s in 𝓝 t, ∀ y, 0 < ρ s y) (hsmooth : ContDiff ℝ ∞ (ρ t))
    (hρ : HasDerivAt (fun s => ρ s x) ((1 / 2) * ∑ k, pd (pd (ρ t) k) k x) t)
    (hρ₁ : ∀ i, HasDerivAt (fun s => pd (ρ s) i x)
      ((1 / 2) * ∑ k, pd (pd (pd (ρ t) i) k) k x) t) :
    HasDerivAt (fun s => ρ s x * ∑ i, logW (ρ s) i x ^ 2)
      ((∑ i, pd (fun y => ρ t y * ((∑ k, logW (ρ t) k y ^ 2) * logW (ρ t) i y / 2
          + ∑ j, logA (ρ t) i j y * logW (ρ t) j y)) i x)
        - ρ t x * ∑ i, ∑ j, logA (ρ t) i j x ^ 2) t := by
  have J := isLogJet_log hsmooth hpos.self_of_nhds
  have hF := hasDerivAt_mul_sum_sq (Finset.univ : Finset (Fin d)) (hasDerivAt_rho J hρ)
    (fun i _ => hasDerivAt_logW J hpos hρ i (hρ₁ i))
  have core := p1_core_of_symm (ρ t x) (fun i => logW (ρ t) i x)
    (fun i j => logA (ρ t) i j x) (fun i j k => logT (ρ t) i j k x)
    (fun i j => congrFun (J.symm i j) x) (fun i j k => J.symm_T i j k x)
  refine hF.congr_deriv ?_
  rw [Finset.sum_congr rfl fun i _ => J.pd_fluxP1 i x]
  linear_combination core

/-- P2, stated with `logW`, `logA`, `logT` (see `Fisher41.hasDerivAt_rho_mul_sum_sq_hess`). -/
theorem hasDerivAt_hess_aux {ρ : ℝ → E d → ℝ} {t : ℝ} {x : E d}
    (hpos : ∀ᶠ s in 𝓝 t, ∀ y, 0 < ρ s y) (hreg : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 (ρ s) x)
    (hsmooth : ContDiff ℝ ∞ (ρ t))
    (hρ : HasDerivAt (fun s => ρ s x) ((1 / 2) * ∑ k, pd (pd (ρ t) k) k x) t)
    (hρ₁ : ∀ i, HasDerivAt (fun s => pd (ρ s) i x)
      ((1 / 2) * ∑ k, pd (pd (pd (ρ t) i) k) k x) t)
    (hρ₂ : ∀ i j, HasDerivAt (fun s => pd (pd (ρ s) i) j x)
      ((1 / 2) * ∑ k, pd (pd (pd (pd (ρ t) i) j) k) k x) t) :
    HasDerivAt (fun s => ρ s x * ∑ i, ∑ j, logA (ρ s) i j x ^ 2)
      ((∑ k, pd (fun y => ρ t y * ((∑ i, ∑ j, logA (ρ t) i j y ^ 2) * logW (ρ t) k y / 2
          + ∑ i, ∑ j, logA (ρ t) i j y * logT (ρ t) i j k y)) k x)
        - ρ t x * kernelK (ρ t) x) t := by
  have J := isLogJet_log hsmooth hpos.self_of_nhds
  have hF := hasDerivAt_mul_sum_sum_sq (Finset.univ : Finset (Fin d))
    (Finset.univ : Finset (Fin d)) (hasDerivAt_rho J hρ)
    (fun i _ j _ => hasDerivAt_logA J hpos hreg hρ hρ₁ i j (hρ₂ i j))
  have core := p2_core_of_symm (ρ t x) (fun i => logW (ρ t) i x)
    (fun i j => logA (ρ t) i j x) (fun i j k => logT (ρ t) i j k x)
    (fun i j k l => logQ (ρ t) i j k l x) (fun i j => congrFun (J.symm i j) x)
  refine hF.congr_deriv ?_
  rw [Finset.sum_congr rfl fun k _ => J.pd_fluxP2 k x, kernelK_eq_log]
  linear_combination core

end Identities

/-! ### Main statements -/

/-- **Pointwise divergence identity P1** (analytic form of `Fisher41.p1_core`). Let `ρ s` be
positive for `s` near `t`, `ρ t` smooth, and let `ρ` and `∇ρ` satisfy the heat equation
`∂ₜ = ½ Δ` at `(t, x)`. With `w = ∇ log ρ t` and `A = ∇² log ρ t`,
`∂ₜ (ρ |w|²) = Σᵢ ∂ᵢ (ρ (|w|² wᵢ / 2 + Σⱼ Aᵢⱼ wⱼ)) - ρ |A|²` at `(t, x)`. -/
theorem hasDerivAt_fisherDensity {d : ℕ} {ρ : ℝ → E d → ℝ} {t : ℝ} {x : E d}
    (hpos : ∀ᶠ s in 𝓝 t, ∀ y, 0 < ρ s y) (hsmooth : ContDiff ℝ ∞ (ρ t))
    (hρ : HasDerivAt (fun s => ρ s x) ((1 / 2) * ∑ k, pd (pd (ρ t) k) k x) t)
    (hρ₁ : ∀ i, HasDerivAt (fun s => pd (ρ s) i x)
      ((1 / 2) * ∑ k, pd (pd (pd (ρ t) i) k) k x) t) :
    HasDerivAt (fun s => fisherDensity (ρ s) x)
      ((∑ i, pd (fun y => ρ t y *
          ((∑ k, (pd (fun z => Real.log (ρ t z)) k y) ^ 2) * pd (fun z => Real.log (ρ t z)) i y / 2
            + ∑ j, pd (pd (fun z => Real.log (ρ t z)) i) j y * pd (fun z => Real.log (ρ t z)) j y))
          i x)
        - ρ t x * ∑ i, ∑ j, (pd (pd (fun z => Real.log (ρ t z)) i) j x) ^ 2) t :=
  Identities.hasDerivAt_fisher_aux hpos hsmooth hρ hρ₁

/-- **Pointwise divergence identity P2** (analytic form of `Fisher41.p2_core`). Let `ρ s` be
positive and `C²` at `x` for `s` near `t`, `ρ t` smooth, and let `ρ`, `∇ρ`, `∇²ρ` satisfy the
heat equation `∂ₜ = ½ Δ` at `(t, x)`. With `w, A, T` the first three derivatives of
`log ρ t`, `∂ₜ (ρ |A|²) = Σₖ ∂ₖ (ρ (|A|² wₖ / 2 + Σᵢⱼ Aᵢⱼ Tᵢⱼₖ)) - ρ K_ρ` at `(t, x)`. -/
theorem hasDerivAt_rho_mul_sum_sq_hess {d : ℕ} {ρ : ℝ → E d → ℝ} {t : ℝ} {x : E d}
    (hpos : ∀ᶠ s in 𝓝 t, ∀ y, 0 < ρ s y) (hreg : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 (ρ s) x)
    (hsmooth : ContDiff ℝ ∞ (ρ t))
    (hρ : HasDerivAt (fun s => ρ s x) ((1 / 2) * ∑ k, pd (pd (ρ t) k) k x) t)
    (hρ₁ : ∀ i, HasDerivAt (fun s => pd (ρ s) i x)
      ((1 / 2) * ∑ k, pd (pd (pd (ρ t) i) k) k x) t)
    (hρ₂ : ∀ i j, HasDerivAt (fun s => pd (pd (ρ s) i) j x)
      ((1 / 2) * ∑ k, pd (pd (pd (pd (ρ t) i) j) k) k x) t) :
    HasDerivAt (fun s => ρ s x * ∑ i, ∑ j, (pd (pd (fun z => Real.log (ρ s z)) i) j x) ^ 2)
      ((∑ k, pd (fun y => ρ t y *
          ((∑ i, ∑ j, (pd (pd (fun z => Real.log (ρ t z)) i) j y) ^ 2)
              * pd (fun z => Real.log (ρ t z)) k y / 2
            + ∑ i, ∑ j, pd (pd (fun z => Real.log (ρ t z)) i) j y
                * pd (pd (pd (fun z => Real.log (ρ t z)) i) j) k y)) k x)
        - ρ t x * kernelK (ρ t) x) t :=
  Identities.hasDerivAt_hess_aux hpos hreg hsmooth hρ hρ₁ hρ₂

/-- **Bridge for `K`**: since `negHess g = -∇² log g`,
`K_g = Σᵢⱼₖ (∂ₖ∂ⱼ∂ᵢ log g)² - 2 Σᵢⱼₖ Aᵢⱼ Aⱼₖ Aₖᵢ` with `A = ∇² log g`. -/
theorem kernelK_eq_sum {d : ℕ} (g : E d → ℝ) (x : E d) :
    kernelK g x = ∑ i, ∑ j, ∑ k, (pd (pd (pd (fun z => Real.log (g z)) i) j) k x) ^ 2
      - 2 * ∑ i, ∑ j, ∑ k, pd (pd (fun z => Real.log (g z)) i) j x
          * pd (pd (fun z => Real.log (g z)) j) k x * pd (pd (fun z => Real.log (g z)) k) i x :=
  Identities.kernelK_eq_log g x

end Fisher41
