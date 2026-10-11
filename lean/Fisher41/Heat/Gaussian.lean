/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Defs
import TauCeti.Analysis.InnerProductSpace.CompleteSquare
import TauCeti.Analysis.PDE.HeatKernel.Basic
import TauCeti.Analysis.PDE.HeatKernel.HeatEquation

/-!
# The Gaussian kernel and the heat flow

`Fisher41.gaussian d t` is the centred Gaussian density of variance `t` on `E d = ℝᵈ`, and
`Fisher41.heat f t = f ⋆ gaussian d t` is the heat flow. Tau Ceti's heat kernel
`TauCeti.heatKernel s x = (4πs)^(-d/2) exp(-‖x‖²/(4s))` has variance `2s` and solves `∂ₛ = Δ`,
so `gaussian d t = heatKernel (t / 2)` and the heat flow solves `∂ₜ = ½ Δ`. This file transfers
Tau Ceti's results on the heat kernel through this identification.

## Main results

* `Fisher41.gaussian_eq_heatKernel`: `gaussian d t = TauCeti.heatKernel (t / 2)`.
* `Fisher41.gaussian_pos`, `Fisher41.integrable_gaussian`, `Fisher41.integral_gaussian_eq_one`:
  at positive variance the Gaussian is a positive probability density.
* `Fisher41.integral_gaussian_mul_gaussian_sub`: the semigroup identity
  `∫ γₛ(y) γₜ(x - y) dy = γₛ₊ₜ(x)`.
* `Fisher41.heat_eq_convolution`: `heat f t = TauCeti.heatKernel (t / 2) ⋆ f`.
* `Fisher41.hasDerivAt_heat`: the heat equation `∂ₜ heat f t x = ½ Δ (heat f t) x` for a
  measurable, essentially bounded `f`.
* `Fisher41.gaussian_mul_gaussian_sub`: completing the square,
  `γ_T(y) γₜ(x - y) = γ_{T+t}(x) γ_β(y - α • x)` with `α = T / (T + t)`, `β = T t / (T + t)`.
* `Fisher41.mul_gaussian_le_heat`: Gaussian lower bounds propagate along the heat flow,
  `c γ_T ≤ f` implies `c γ_{T+t} ≤ heat f t`.
-/

open MeasureTheory Real
open scoped Convolution Laplacian

noncomputable section

namespace Fisher41

/-- The Gaussian of variance `t` is Tau Ceti's heat kernel at time `t / 2`. -/
theorem gaussian_eq_heatKernel (d : ℕ) (t : ℝ) :
    gaussian d t = TauCeti.heatKernel (E := E d) (t / 2) := by
  funext x
  rw [TauCeti.heatKernel_apply, finrank_euclideanSpace_fin, gaussian,
    show 4 * π * (t / 2) = 2 * π * t by ring, show 4 * (t / 2) = 2 * t by ring]

/-- The Gaussian is positive at positive variance. -/
theorem gaussian_pos {d : ℕ} {t : ℝ} (ht : 0 < t) (x : E d) : 0 < gaussian d t x := by
  rw [gaussian]
  positivity

/-- The Gaussian is continuous. -/
theorem continuous_gaussian (d : ℕ) (t : ℝ) : Continuous (gaussian d t) := by
  rw [gaussian_eq_heatKernel]
  exact (TauCeti.contDiff_heatKernel (t / 2) (k := 0)).continuous

/-- The Gaussian is bounded by its value `(2πt)^(-d/2)` at the origin. -/
theorem gaussian_le {d : ℕ} {t : ℝ} (ht : 0 < t) (x : E d) :
    gaussian d t x ≤ (2 * π * t) ^ (-(d : ℝ) / 2) := by
  rw [gaussian]
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  rw [neg_div]
  exact neg_nonpos.2 (by positivity)

/-- The Gaussian is integrable at positive variance. -/
theorem integrable_gaussian {d : ℕ} {t : ℝ} (ht : 0 < t) : Integrable (gaussian d t) := by
  rw [gaussian_eq_heatKernel]
  exact TauCeti.integrable_heatKernel (half_pos ht)

/-- The Gaussian has mass one at positive variance. -/
theorem integral_gaussian_eq_one {d : ℕ} {t : ℝ} (ht : 0 < t) : ∫ x, gaussian d t x = 1 := by
  rw [gaussian_eq_heatKernel]
  exact TauCeti.integral_heatKernel (half_pos ht)

/-- **The semigroup property of the Gaussian** (Chapman–Kolmogorov): variances add under
convolution, `∫ γₛ(y) γₜ(x - y) dy = γₛ₊ₜ(x)` for `s, t > 0`. -/
theorem integral_gaussian_mul_gaussian_sub {d : ℕ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x : E d) : ∫ y, gaussian d s y * gaussian d t (x - y) = gaussian d (s + t) x := by
  have h := congrFun (TauCeti.heatKernel_convolution_heatKernel (E := E d) (half_pos hs)
    (half_pos ht)) x
  rw [convolution_lsmul] at h
  rw [gaussian_eq_heatKernel, gaussian_eq_heatKernel, gaussian_eq_heatKernel, add_div]
  simpa only [smul_eq_mul] using h

/-- The heat flow is the convolution with Tau Ceti's heat kernel at time `t / 2`. -/
theorem heat_eq_convolution {d : ℕ} (f : E d → ℝ) (t : ℝ) (x : E d) :
    heat f t x = (TauCeti.heatKernel (t / 2) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x := by
  rw [convolution_lsmul_swap, heat, gaussian_eq_heatKernel]
  congr 1 with y
  rw [smul_eq_mul, mul_comm]

/-- **The heat equation** `∂ₜu = ½ Δu` for the heat flow `u(t) = heat f t` of a measurable,
essentially bounded function `f`, at every positive time. Here `Δ` is Mathlib's Laplacian
`Laplacian.laplacian`, the same term as in `TauCeti.hasDerivAt_heatKernel_convolution`. -/
theorem hasDerivAt_heat {d : ℕ} {f : E d → ℝ} {M t : ℝ} (hf : AEStronglyMeasurable f)
    (hM : ∀ᵐ y, ‖f y‖ ≤ M) (ht : 0 < t) (x : E d) :
    HasDerivAt (fun s => heat f s x) ((1 / 2) * Δ (heat f t) x) t := by
  have hK := (TauCeti.hasDerivAt_heatKernel_convolution (half_pos ht) hf hM x).comp t
    ((hasDerivAt_id' t).div_const 2)
  have h₁ : (fun s => heat f s x) =
      (fun s => (TauCeti.heatKernel s ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f) x) ∘ fun s => s / 2 :=
    funext fun s => heat_eq_convolution f s x
  have h₂ : heat f t = TauCeti.heatKernel (t / 2) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f :=
    funext (heat_eq_convolution f t)
  rw [h₁, h₂]
  exact hK.congr_deriv (mul_comm _ _)

/-- **Completing the square** in a product of Gaussians: for `T, t > 0`,
`γ_T(y) γₜ(x - y) = γ_{T+t}(x) γ_β(y - α • x)` with `α = T / (T + t)` and `β = T t / (T + t)`. -/
theorem gaussian_mul_gaussian_sub {d : ℕ} {T t : ℝ} (hT : 0 < T) (ht : 0 < t) (x y : E d) :
    gaussian d T y * gaussian d t (x - y) =
      gaussian d (T + t) x * gaussian d (T * t / (T + t)) (y - (T / (T + t)) • x) := by
  have hTt : 0 < T + t := add_pos hT ht
  -- The exponents, by completing the square.
  have hexp : -‖y‖ ^ 2 / (2 * T) + -‖x - y‖ ^ 2 / (2 * t) =
      -‖x‖ ^ 2 / (2 * (T + t)) + -‖y - (T / (T + t)) • x‖ ^ 2 / (2 * (T * t / (T + t))) := by
    have h := TauCeti.mul_norm_sq_add_mul_norm_sub_sq (a := (2 * T)⁻¹) (b := (2 * t)⁻¹)
      (by positivity) x y
    rw [show (2 * t)⁻¹ / ((2 * T)⁻¹ + (2 * t)⁻¹) = T / (T + t) by field_simp; ring,
      show (2 * T)⁻¹ * (2 * t)⁻¹ / ((2 * T)⁻¹ + (2 * t)⁻¹) = (2 * (T + t))⁻¹ by
        field_simp; ring,
      show (2 * T)⁻¹ + (2 * t)⁻¹ = (2 * (T * t / (T + t)))⁻¹ by field_simp; ring] at h
    linear_combination -h
  -- The normalizing constants: `(2πT) (2πt) = (2π(T + t)) (2πβ)`.
  have hconst : (2 * π * T) ^ (-(d : ℝ) / 2) * (2 * π * t) ^ (-(d : ℝ) / 2) =
      (2 * π * (T + t)) ^ (-(d : ℝ) / 2) * (2 * π * (T * t / (T + t))) ^ (-(d : ℝ) / 2) := by
    rw [← mul_rpow (by positivity) (by positivity), ← mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [div_eq_mul_inv]
    linear_combination -(2 * π) * (2 * π) * T * t * mul_inv_cancel₀ hTt.ne'
  simp only [gaussian]
  rw [mul_mul_mul_comm, ← exp_add, hexp, hconst, exp_add]
  ring

/-- **Gaussian lower bounds propagate along the heat flow**: if `f` is integrable and
`c γ_T ≤ f`, then `c γ_{T+t} ≤ heat f t` for `T, t > 0`. No sign condition on `c` is needed. -/
theorem mul_gaussian_le_heat {d : ℕ} {f : E d → ℝ} {c T t : ℝ} (hf : Integrable f)
    (hfc : ∀ y, c * gaussian d T y ≤ f y) (hT : 0 < T) (ht : 0 < t) (x : E d) :
    c * gaussian d (T + t) x ≤ heat f t x := by
  have hmeas : AEStronglyMeasurable (fun y => gaussian d t (x - y)) :=
    ((continuous_gaussian d t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbdd : ∀ᵐ y, ‖gaussian d t (x - y)‖ ≤ (2 * π * t) ^ (-(d : ℝ) / 2) :=
    ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (gaussian_pos ht _).le]
      exact gaussian_le ht _
  calc c * gaussian d (T + t) x = ∫ y, c * gaussian d T y * gaussian d t (x - y) := by
        simp_rw [mul_assoc]
        rw [integral_const_mul, integral_gaussian_mul_gaussian_sub hT ht]
    _ ≤ ∫ y, f y * gaussian d t (x - y) :=
        integral_mono (((integrable_gaussian hT).const_mul c).mul_bdd hmeas hbdd)
          (hf.mul_bdd hmeas hbdd) fun y =>
            mul_le_mul_of_nonneg_right (hfc y) (gaussian_pos ht _).le
    _ = heat f t x := rfl

end Fisher41
