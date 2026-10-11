/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Heat.Gaussian
import TauCeti.Analysis.PDE.HeatKernel.Bounds

/-!
# Gaussian domination along the heat flow

All integrands in the heat-flow part of the argument are bounded by `C (1 + ‖x‖)^m γ_{T'}(x)`,
where `γ_t = gaussian d t` is the centred Gaussian of variance `t`. This file provides the
uniform bounds used for differentiation under the integral sign and dominated convergence.

## Main results

* `Fisher41.integrable_one_add_norm_pow_mul_gaussian`: `(1 + ‖x‖)^m γ_t(x)` is integrable.
* `Fisher41.integral_one_add_norm_pow_mul_gaussian_le`,
  `Fisher41.exists_integral_one_add_norm_pow_mul_gaussian_le`: the moments
  `∫ (1 + ‖z‖)^m γ_t(z) dz` are bounded uniformly for `t ∈ (0, t₁]`.
* `Fisher41.gaussian_le_mul_gaussian`, `Fisher41.gaussian_add_le_mul_gaussian_add`: comparison
  of Gaussians in time, `γ_s ≤ (s'/s)^(d/2) γ_{s'}` for `0 < s ≤ s'`.
* `Fisher41.heat_one_add_norm_pow_mul_gaussian_le`,
  `Fisher41.exists_heat_one_add_norm_pow_mul_gaussian_le`: the heat flow of
  `(1 + ‖y‖)^m γ_T(y)` is bounded by `C (1 + ‖x‖)^m γ_{T+t}(x)`, uniformly for `t ∈ (0, t₁]`.
* `Fisher41.abs_heat_le_mul_heat`, `Fisher41.abs_heat_le_of_abs_le`,
  `Fisher41.abs_heat_le_of_abs_le_of_heat_le`, `Fisher41.exists_abs_heat_le`: domination of the
  heat flow of a function dominated by `K (1 + ‖y‖)^m γ_T(y)`.
* `Fisher41.PolyGauss`: domination by a polynomially weighted Gaussian, with closure lemmas
  (`add`, `neg`, `sub`, `const_mul`, `mul_poly`, `mono`, `heat`) and `PolyGauss.integrable`.

## Implementation notes

The basic pointwise estimate is `(1 + ‖x‖)^m γ_t(x) ≤ 2^(d/2) m! e^(1+t) γ_{2t}(x)`
(`Fisher41.Domination.one_add_norm_pow_mul_gaussian_le`), whose constant is explicit and
monotone in `t`; this gives `t`-uniform moment bounds without any change of variables. The heat
flow of a weighted Gaussian is computed by completing the square
(`Fisher41.gaussian_mul_gaussian_sub`) and translating by `α • x`.
-/

open MeasureTheory Real
open scoped Nat

noncomputable section

namespace Fisher41

variable {d : ℕ}

namespace Domination

/-- The Gaussian is nonnegative at nonnegative variance. -/
theorem gaussian_nonneg {t : ℝ} (ht : 0 ≤ t) (x : E d) : 0 ≤ gaussian d t x := by
  rw [gaussian]
  positivity

/-- The Gaussian of variance `t` is the Gaussian of variance `2t` times a Gaussian factor:
`γ_t(x) = 2^(d/2) exp(-‖x‖²/(4t)) γ_{2t}(x)`. -/
theorem gaussian_eq_mul_gaussian_two_mul {t : ℝ} (ht : 0 < t) (x : E d) :
    gaussian d t x = 2 ^ ((d : ℝ) / 2) * exp (-‖x‖ ^ 2 / (4 * t)) * gaussian d (2 * t) x := by
  have h := TauCeti.heatKernel_eq_mul_heatKernel_two_mul (E := E d) (half_pos ht) x
  rw [finrank_euclideanSpace_fin, show 8 * (t / 2) = 4 * t by ring,
    show 2 * (t / 2) = 2 * t / 2 by ring] at h
  rw [gaussian_eq_heatKernel, gaussian_eq_heatKernel]
  exact h

/-- **Polynomial weights with an explicit constant.**
`(1 + ‖x‖)^m γ_t(x) ≤ 2^(d/2) m! e^(1+t) γ_{2t}(x)`. -/
theorem one_add_norm_pow_mul_gaussian_le (m : ℕ) {t : ℝ} (ht : 0 < t) (x : E d) :
    (1 + ‖x‖) ^ m * gaussian d t x ≤
      2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) * gaussian d (2 * t) x := by
  -- `(1 + r)^m ≤ m! exp(1 + r)` and `1 + r - r² / (4t) ≤ 1 + t`.
  have hpow : (1 + ‖x‖) ^ m ≤ m ! * exp (1 + ‖x‖) := by
    have := pow_div_factorial_le_exp (1 + ‖x‖) (by positivity) m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hquad : 1 + ‖x‖ + -‖x‖ ^ 2 / (4 * t) ≤ 1 + t := by
    have h : ‖x‖ - t ≤ ‖x‖ ^ 2 / (4 * t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖x‖ - 2 * t)]
    rw [neg_div]
    linarith
  have hG : 0 ≤ gaussian d (2 * t) x := (gaussian_pos (by positivity) x).le
  rw [gaussian_eq_mul_gaussian_two_mul ht x]
  calc (1 + ‖x‖) ^ m * (2 ^ ((d : ℝ) / 2) * exp (-‖x‖ ^ 2 / (4 * t)) * gaussian d (2 * t) x)
      = 2 ^ ((d : ℝ) / 2) * ((1 + ‖x‖) ^ m * exp (-‖x‖ ^ 2 / (4 * t))) *
          gaussian d (2 * t) x := by ring
    _ ≤ 2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) * gaussian d (2 * t) x := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hG
        calc (1 + ‖x‖) ^ m * exp (-‖x‖ ^ 2 / (4 * t))
            ≤ m ! * exp (1 + ‖x‖) * exp (-‖x‖ ^ 2 / (4 * t)) :=
              mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
          _ = m ! * exp (1 + ‖x‖ + -‖x‖ ^ 2 / (4 * t)) := by
              rw [Real.exp_add (1 + ‖x‖)]
              ring
          _ ≤ m ! * exp (1 + t) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hquad) (by positivity)

/-- `1 + ‖z + a • x‖ ≤ (1 + ‖z‖) (1 + ‖x‖)` whenever `|a| ≤ 1`. -/
theorem one_add_norm_add_smul_le {a : ℝ} (z x : E d) (ha : |a| ≤ 1) :
    1 + ‖z + a • x‖ ≤ (1 + ‖z‖) * (1 + ‖x‖) := by
  have h₁ : ‖z + a • x‖ ≤ ‖z‖ + |a| * ‖x‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le z (a • x)
  have h₂ : |a| * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg x) ha
  nlinarith [mul_nonneg (norm_nonneg z) (norm_nonneg x)]

/-- A bound `|g| ≤ K (1 + ‖·‖)^m γ_T` with `T > 0` forces `K ≥ 0`. -/
theorem nonneg_of_forall_abs_le {g : E d → ℝ} {K T : ℝ} {m : ℕ} (hT : 0 < T)
    (hg : ∀ y, |g y| ≤ K * (1 + ‖y‖) ^ m * gaussian d T y) : 0 ≤ K := by
  have h := (abs_nonneg (g 0)).trans (hg 0)
  rw [mul_assoc] at h
  exact (mul_nonneg_iff_of_pos_right
    (mul_pos (by positivity) (gaussian_pos hT (0 : E d)))).1 h

end Domination

/-! ### Moments of the Gaussian -/

/-- Polynomially weighted Gaussians are integrable. -/
theorem integrable_one_add_norm_pow_mul_gaussian (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : E d => (1 + ‖x‖) ^ m * gaussian d t x) := by
  have hmeas : AEStronglyMeasurable (fun x : E d => (1 + ‖x‖) ^ m * gaussian d t x) :=
    (((continuous_const.add continuous_norm).pow m).mul
      (continuous_gaussian d t)).aestronglyMeasurable
  have hbound : ∀ x : E d, ‖(1 + ‖x‖) ^ m * gaussian d t x‖ ≤
      2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) * gaussian d (2 * t) x := fun x => by
    have h0 : 0 ≤ (1 + ‖x‖) ^ m * gaussian d t x :=
      mul_nonneg (by positivity) (gaussian_pos ht x).le
    rw [Real.norm_of_nonneg h0]
    exact Domination.one_add_norm_pow_mul_gaussian_le m ht x
  exact ((integrable_gaussian (by positivity : (0 : ℝ) < 2 * t)).const_mul _).mono' hmeas
    (ae_of_all _ hbound)

/-- **Moments of the Gaussian**, with an explicit constant:
`∫ (1 + ‖z‖)^m γ_t(z) dz ≤ 2^(d/2) m! e^(1+t)`. -/
theorem integral_one_add_norm_pow_mul_gaussian_le (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ z, (1 + ‖z‖) ^ m * gaussian d t z ≤ 2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) := by
  have h2t : 0 < 2 * t := by positivity
  calc ∫ z, (1 + ‖z‖) ^ m * gaussian d t z
      ≤ ∫ z, 2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) * gaussian d (2 * t) z :=
        integral_mono_of_nonneg
          (ae_of_all _ fun z => mul_nonneg (by positivity) (gaussian_pos ht z).le)
          ((integrable_gaussian h2t).const_mul _)
          (ae_of_all _ fun z => Domination.one_add_norm_pow_mul_gaussian_le m ht z)
    _ = 2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) := by
        rw [integral_const_mul, integral_gaussian_eq_one h2t, mul_one]

/-- **Uniform moments.** For every `m` and `t₁`, the moments `∫ (1 + ‖z‖)^m γ_t(z) dz` are
bounded uniformly in `t ∈ (0, t₁]`. -/
theorem exists_integral_one_add_norm_pow_mul_gaussian_le (m : ℕ) (t₁ : ℝ) :
    ∃ C, ∀ t ∈ Set.Ioc 0 t₁, ∫ z, (1 + ‖z‖) ^ m * gaussian d t z ≤ C :=
  ⟨2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t₁)), fun t ht =>
    (integral_one_add_norm_pow_mul_gaussian_le m ht.1).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by linarith [ht.2])) (by positivity)) (by positivity))⟩

/-! ### Comparison of Gaussians in time -/

/-- **Comparison of Gaussians.** For `0 < s ≤ s'`, `γ_s ≤ (s'/s)^(d/2) γ_{s'}`. -/
theorem gaussian_le_mul_gaussian {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s') (x : E d) :
    gaussian d s x ≤ (s' / s) ^ ((d : ℝ) / 2) * gaussian d s' x := by
  have h := TauCeti.heatKernel_le_mul_heatKernel (E := E d) (half_pos hs)
    (by linarith : s / 2 ≤ s' / 2) x
  rw [finrank_euclideanSpace_fin,
    div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
  rw [gaussian_eq_heatKernel, gaussian_eq_heatKernel]
  exact h

/-- **Gaussian comparison in time.** For `0 < T` and `0 ≤ t ≤ t₁`,
`γ_{T+t} ≤ ((T + t₁)/T)^(d/2) γ_{T+t₁}`. -/
theorem gaussian_add_le_mul_gaussian_add {T t t₁ : ℝ} (hT : 0 < T) (ht : 0 ≤ t)
    (htt₁ : t ≤ t₁) (x : E d) :
    gaussian d (T + t) x ≤ ((T + t₁) / T) ^ ((d : ℝ) / 2) * gaussian d (T + t₁) x := by
  have hTt : 0 < T + t := by linarith
  have hTt₁ : 0 < T + t₁ := by linarith
  calc gaussian d (T + t) x ≤ ((T + t₁) / (T + t)) ^ ((d : ℝ) / 2) * gaussian d (T + t₁) x :=
        gaussian_le_mul_gaussian hTt (by linarith) x
    _ ≤ ((T + t₁) / T) ^ ((d : ℝ) / 2) * gaussian d (T + t₁) x :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (div_nonneg hTt₁.le hTt.le)
            (div_le_div_of_nonneg_left hTt₁.le hT (by linarith)) (by positivity))
          (gaussian_pos hTt₁ x).le

/-! ### The heat flow of a polynomially weighted Gaussian -/

/-- **Heat flow of a polynomially weighted Gaussian**, with an explicit constant: for `T, t > 0`,
`heat ((1 + ‖·‖)^m γ_T) t x ≤ 2^(d/2) m! e^(1+t) (1 + ‖x‖)^m γ_{T+t}(x)`. -/
theorem heat_one_add_norm_pow_mul_gaussian_le (m : ℕ) {T t : ℝ} (hT : 0 < T) (ht : 0 < t)
    (x : E d) :
    heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x ≤
      2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) * (1 + ‖x‖) ^ m * gaussian d (T + t) x := by
  have hTt : 0 < T + t := add_pos hT ht
  have hβ : 0 < T * t / (T + t) := by positivity
  have hβt : T * t / (T + t) ≤ t := by
    rw [div_le_iff₀ hTt]
    nlinarith [mul_pos ht ht]
  have hα : |T / (T + t)| ≤ 1 := by
    rw [abs_of_pos (div_pos hT hTt), div_le_one hTt]
    linarith
  -- Completing the square and translating by `α • x`, `α = T / (T + t)`, turns the heat flow
  -- into `γ_{T+t}(x)` times a weighted moment of `γ_β`, `β = T t / (T + t)`.
  have hsq : heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x =
      gaussian d (T + t) x *
        ∫ z, (1 + ‖z + (T / (T + t)) • x‖) ^ m * gaussian d (T * t / (T + t)) z := by
    have h₁ : heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x =
        ∫ y, gaussian d (T + t) x *
          ((1 + ‖y‖) ^ m * gaussian d (T * t / (T + t)) (y - (T / (T + t)) • x)) := by
      simp only [heat]
      congr 1 with y
      rw [mul_assoc, gaussian_mul_gaussian_sub hT ht x y, mul_left_comm]
    have h₂ := integral_sub_right_eq_self (μ := (volume : Measure (E d)))
      (fun z => (1 + ‖z + (T / (T + t)) • x‖) ^ m * gaussian d (T * t / (T + t)) z)
      ((T / (T + t)) • x)
    simp only [sub_add_cancel] at h₂
    rw [h₁, integral_const_mul, h₂]
  -- `1 + ‖z + α • x‖ ≤ (1 + ‖z‖)(1 + ‖x‖)` reduces to the moments of `γ_β`, `β ≤ t`.
  have hpt : ∀ z : E d, (1 + ‖z + (T / (T + t)) • x‖) ^ m * gaussian d (T * t / (T + t)) z ≤
      (1 + ‖x‖) ^ m * ((1 + ‖z‖) ^ m * gaussian d (T * t / (T + t)) z) := fun z => by
    calc (1 + ‖z + (T / (T + t)) • x‖) ^ m * gaussian d (T * t / (T + t)) z
        ≤ ((1 + ‖z‖) * (1 + ‖x‖)) ^ m * gaussian d (T * t / (T + t)) z :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) (Domination.one_add_norm_add_smul_le z x hα) m)
            (gaussian_pos hβ z).le
      _ = (1 + ‖x‖) ^ m * ((1 + ‖z‖) ^ m * gaussian d (T * t / (T + t)) z) := by
          rw [mul_pow]
          ring
  have hmom : ∫ z, (1 + ‖z‖) ^ m * gaussian d (T * t / (T + t)) z ≤
      2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) :=
    (integral_one_add_norm_pow_mul_gaussian_le m hβ).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by linarith)) (by positivity)) (by positivity))
  have hint : ∫ z, (1 + ‖z + (T / (T + t)) • x‖) ^ m * gaussian d (T * t / (T + t)) z ≤
      (1 + ‖x‖) ^ m * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t))) :=
    calc ∫ z, (1 + ‖z + (T / (T + t)) • x‖) ^ m * gaussian d (T * t / (T + t)) z
        ≤ ∫ z, (1 + ‖x‖) ^ m * ((1 + ‖z‖) ^ m * gaussian d (T * t / (T + t)) z) :=
          integral_mono_of_nonneg
            (ae_of_all _ fun z => mul_nonneg (by positivity) (gaussian_pos hβ z).le)
            ((integrable_one_add_norm_pow_mul_gaussian m hβ).const_mul _) (ae_of_all _ hpt)
      _ = (1 + ‖x‖) ^ m * ∫ z, (1 + ‖z‖) ^ m * gaussian d (T * t / (T + t)) z :=
          integral_const_mul _ _
      _ ≤ (1 + ‖x‖) ^ m * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t))) :=
          mul_le_mul_of_nonneg_left hmom (by positivity)
  rw [hsq]
  calc gaussian d (T + t) x *
        ∫ z, (1 + ‖z + (T / (T + t)) • x‖) ^ m * gaussian d (T * t / (T + t)) z
      ≤ gaussian d (T + t) x * ((1 + ‖x‖) ^ m * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)))) :=
        mul_le_mul_of_nonneg_left hint (gaussian_pos hTt x).le
    _ = 2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) * (1 + ‖x‖) ^ m * gaussian d (T + t) x := by
        ring

/-- **Heat flow of a polynomially weighted Gaussian.** For `0 < T`, `m` and `t₁`, there is
`C ≥ 0` with `heat ((1 + ‖·‖)^m γ_T) t x ≤ C (1 + ‖x‖)^m γ_{T+t}(x)` for all `t ∈ (0, t₁]` and
all `x`. -/
theorem exists_heat_one_add_norm_pow_mul_gaussian_le (m : ℕ) {T : ℝ} (hT : 0 < T) (t₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Set.Ioc 0 t₁, ∀ x : E d,
      heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x ≤
        C * (1 + ‖x‖) ^ m * gaussian d (T + t) x := by
  refine ⟨2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t₁)), by positivity, fun t ht x => ?_⟩
  have hc : 2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) ≤
      2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t₁)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by linarith [ht.2])) (by positivity)) (by positivity)
  exact (heat_one_add_norm_pow_mul_gaussian_le m hT ht.1 x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
      (gaussian_pos (add_pos hT ht.1) x).le)

/-! ### Domination of the heat flow -/

/-- If `|g| ≤ K (1 + ‖·‖)^m γ_T`, then `|heat g t| ≤ K heat ((1 + ‖·‖)^m γ_T) t`. No
measurability of `g` is needed: if the integrand is not integrable, `heat g t x = 0`. -/
theorem abs_heat_le_mul_heat {g : E d → ℝ} {K T t : ℝ} {m : ℕ} (hT : 0 < T) (ht : 0 < t)
    (hg : ∀ y, |g y| ≤ K * (1 + ‖y‖) ^ m * gaussian d T y) (x : E d) :
    |heat g t x| ≤ K * heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x := by
  have hmeas : AEStronglyMeasurable (fun y => gaussian d t (x - y)) :=
    ((continuous_gaussian d t).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbdd : ∀ᵐ y, ‖gaussian d t (x - y)‖ ≤ (2 * π * t) ^ (-(d : ℝ) / 2) :=
    ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (gaussian_pos ht _).le]
      exact gaussian_le ht _
  have hint : Integrable fun y => K * ((1 + ‖y‖) ^ m * gaussian d T y) * gaussian d t (x - y) :=
    ((integrable_one_add_norm_pow_mul_gaussian m hT).const_mul K).mul_bdd hmeas hbdd
  have hpt : ∀ y, ‖g y * gaussian d t (x - y)‖ ≤
      K * ((1 + ‖y‖) ^ m * gaussian d T y) * gaussian d t (x - y) := fun y => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (gaussian_pos ht _).le]
    exact mul_le_mul_of_nonneg_right ((hg y).trans_eq (mul_assoc _ _ _)) (gaussian_pos ht _).le
  calc |heat g t x| = ‖∫ y, g y * gaussian d t (x - y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, K * ((1 + ‖y‖) ^ m * gaussian d T y) * gaussian d t (x - y) :=
        norm_integral_le_of_norm_le hint (ae_of_all _ hpt)
    _ = K * heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x := by
        simp only [heat, mul_assoc, integral_const_mul]

/-- **Domination of the heat flow of a dominated function**, with an explicit constant: if
`|g y| ≤ K (1 + ‖y‖)^m γ_T(y)` for all `y`, then
`|heat g t x| ≤ K 2^(d/2) m! e^(1+t) (1 + ‖x‖)^m γ_{T+t}(x)` for `T, t > 0`. -/
theorem abs_heat_le_of_abs_le {g : E d → ℝ} {K T t : ℝ} {m : ℕ} (hT : 0 < T) (ht : 0 < t)
    (hg : ∀ y, |g y| ≤ K * (1 + ‖y‖) ^ m * gaussian d T y) (x : E d) :
    |heat g t x| ≤
      K * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t))) * (1 + ‖x‖) ^ m * gaussian d (T + t) x := by
  have hK : 0 ≤ K := Domination.nonneg_of_forall_abs_le hT hg
  calc |heat g t x| ≤ K * heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x :=
        abs_heat_le_mul_heat hT ht hg x
    _ ≤ K * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t)) * (1 + ‖x‖) ^ m *
          gaussian d (T + t) x) :=
        mul_le_mul_of_nonneg_left (heat_one_add_norm_pow_mul_gaussian_le m hT ht x) hK
    _ = K * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t))) * (1 + ‖x‖) ^ m *
          gaussian d (T + t) x := by ring

/-- **Domination of the heat flow of a dominated function**, with the constant `C` of
`Fisher41.exists_heat_one_add_norm_pow_mul_gaussian_le`: if `|g y| ≤ K (1 + ‖y‖)^m γ_T(y)` for
all `y`, then `|heat g t x| ≤ K C (1 + ‖x‖)^m γ_{T+t}(x)` for `t ∈ (0, t₁]`. -/
theorem abs_heat_le_of_abs_le_of_heat_le {g : E d → ℝ} {K C T t₁ : ℝ} {m : ℕ} (hT : 0 < T)
    (hg : ∀ y, |g y| ≤ K * (1 + ‖y‖) ^ m * gaussian d T y)
    (hC : ∀ t ∈ Set.Ioc 0 t₁, ∀ x : E d,
      heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x ≤
        C * (1 + ‖x‖) ^ m * gaussian d (T + t) x)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 t₁) (x : E d) :
    |heat g t x| ≤ K * C * (1 + ‖x‖) ^ m * gaussian d (T + t) x := by
  have hK : 0 ≤ K := Domination.nonneg_of_forall_abs_le hT hg
  calc |heat g t x| ≤ K * heat (fun y => (1 + ‖y‖) ^ m * gaussian d T y) t x :=
        abs_heat_le_mul_heat hT ht.1 hg x
    _ ≤ K * (C * (1 + ‖x‖) ^ m * gaussian d (T + t) x) :=
        mul_le_mul_of_nonneg_left (hC t ht x) hK
    _ = K * C * (1 + ‖x‖) ^ m * gaussian d (T + t) x := by ring

/-- **Uniform domination of the heat flow**: for `0 < T`, `m` and `t₁` there is `C ≥ 0` such
that `|g y| ≤ K (1 + ‖y‖)^m γ_T(y)` for all `y` implies
`|heat g t x| ≤ K C (1 + ‖x‖)^m γ_{T+t}(x)` for all `t ∈ (0, t₁]` and all `x`. -/
theorem exists_abs_heat_le (m : ℕ) {T : ℝ} (hT : 0 < T) (t₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (g : E d → ℝ) (K : ℝ), (∀ y, |g y| ≤ K * (1 + ‖y‖) ^ m * gaussian d T y) →
      ∀ t ∈ Set.Ioc 0 t₁, ∀ x, |heat g t x| ≤ K * C * (1 + ‖x‖) ^ m * gaussian d (T + t) x := by
  obtain ⟨C, hC0, hC⟩ := exists_heat_one_add_norm_pow_mul_gaussian_le (d := d) m hT t₁
  exact ⟨C, hC0, fun g K hg t ht x => abs_heat_le_of_abs_le_of_heat_le hT hg hC ht x⟩

/-! ### Domination by polynomially weighted Gaussians -/

/-- `g` is dominated by a polynomially weighted Gaussian of variance `T`:
`|g x| ≤ K (1 + ‖x‖)^m γ_T(x)` for some `K` and `m`. -/
def PolyGauss (T : ℝ) (g : E d → ℝ) : Prop :=
  ∃ K : ℝ, ∃ m : ℕ, ∀ x, |g x| ≤ K * (1 + ‖x‖) ^ m * gaussian d T x

/-- The Gaussian `γ_T` is dominated by itself. -/
theorem polyGauss_gaussian {T : ℝ} (hT : 0 ≤ T) : PolyGauss T (gaussian d T) :=
  ⟨1, 0, fun x => le_of_eq (by rw [abs_of_nonneg (Domination.gaussian_nonneg hT x)]; ring)⟩

namespace PolyGauss

variable {T T' : ℝ} {f g : E d → ℝ}

/-- A measurable function dominated by a polynomially weighted Gaussian is integrable. -/
theorem integrable (hT : 0 < T) (hg : PolyGauss T g) (hmeas : AEStronglyMeasurable g) :
    Integrable g := by
  obtain ⟨K, m, hK⟩ := hg
  have hb : ∀ x, ‖g x‖ ≤ K * ((1 + ‖x‖) ^ m * gaussian d T x) := fun x => by
    rw [Real.norm_eq_abs, ← mul_assoc]
    exact hK x
  exact ((integrable_one_add_norm_pow_mul_gaussian m hT).const_mul K).mono' hmeas
    (ae_of_all _ hb)

/-- The zero function is dominated. -/
theorem zero : PolyGauss T (0 : E d → ℝ) :=
  ⟨0, 0, fun x => by simp⟩

/-- A function dominated in absolute value by a dominated function is dominated. -/
theorem of_abs_le (hg : PolyGauss T g) (hfg : ∀ x, |f x| ≤ |g x|) : PolyGauss T f := by
  obtain ⟨K, m, h⟩ := hg
  exact ⟨K, m, fun x => (hfg x).trans (h x)⟩

/-- Negation preserves domination. -/
theorem neg (hg : PolyGauss T g) : PolyGauss T (-g) := by
  obtain ⟨K, m, h⟩ := hg
  exact ⟨K, m, fun x => by simpa only [Pi.neg_apply, abs_neg] using h x⟩

/-- Sums of dominated functions are dominated. -/
theorem add (hT : 0 ≤ T) (hf : PolyGauss T f) (hg : PolyGauss T g) : PolyGauss T (f + g) := by
  obtain ⟨K₁, m₁, h₁⟩ := hf
  obtain ⟨K₂, m₂, h₂⟩ := hg
  refine ⟨|K₁| + |K₂|, max m₁ m₂, fun x => ?_⟩
  have key : ∀ (K : ℝ) (k : ℕ), k ≤ max m₁ m₂ →
      K * (1 + ‖x‖) ^ k * gaussian d T x ≤ |K| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d T x :=
    fun K k hk => mul_le_mul_of_nonneg_right
      (mul_le_mul (le_abs_self K)
        (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg x)) hk)
        (by positivity) (abs_nonneg K))
      (Domination.gaussian_nonneg hT x)
  calc |(f + g) x| ≤ |f x| + |g x| := abs_add_le (f x) (g x)
    _ ≤ K₁ * (1 + ‖x‖) ^ m₁ * gaussian d T x + K₂ * (1 + ‖x‖) ^ m₂ * gaussian d T x :=
        add_le_add (h₁ x) (h₂ x)
    _ ≤ |K₁| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d T x +
          |K₂| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d T x :=
        add_le_add (key K₁ m₁ (le_max_left _ _)) (key K₂ m₂ (le_max_right _ _))
    _ = (|K₁| + |K₂|) * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d T x := by ring

/-- Differences of dominated functions are dominated. -/
theorem sub (hT : 0 ≤ T) (hf : PolyGauss T f) (hg : PolyGauss T g) : PolyGauss T (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hT hg.neg

/-- Constant multiples of dominated functions are dominated. -/
theorem const_mul (c : ℝ) (hg : PolyGauss T g) : PolyGauss T (fun x => c * g x) := by
  obtain ⟨K, m, h⟩ := hg
  refine ⟨|c| * K, m, fun x => ?_⟩
  show |c * g x| ≤ |c| * K * (1 + ‖x‖) ^ m * gaussian d T x
  rw [abs_mul]
  calc |c| * |g x| ≤ |c| * (K * (1 + ‖x‖) ^ m * gaussian d T x) :=
        mul_le_mul_of_nonneg_left (h x) (abs_nonneg c)
    _ = |c| * K * (1 + ‖x‖) ^ m * gaussian d T x := by ring

/-- Multiplying a dominated function by a function of polynomial growth,
`|p x| ≤ K' (1 + ‖x‖)^k`, gives a dominated function. -/
theorem mul_poly {p : E d → ℝ} {K' : ℝ} {k : ℕ} (hg : PolyGauss T g)
    (hp : ∀ x, |p x| ≤ K' * (1 + ‖x‖) ^ k) : PolyGauss T (p * g) := by
  obtain ⟨K, m, h⟩ := hg
  refine ⟨K' * K, k + m, fun x => ?_⟩
  show |p x * g x| ≤ K' * K * (1 + ‖x‖) ^ (k + m) * gaussian d T x
  rw [abs_mul]
  calc |p x| * |g x| ≤ K' * (1 + ‖x‖) ^ k * (K * (1 + ‖x‖) ^ m * gaussian d T x) :=
        mul_le_mul (hp x) (h x) (abs_nonneg _) ((abs_nonneg _).trans (hp x))
    _ = K' * K * (1 + ‖x‖) ^ (k + m) * gaussian d T x := by ring

/-- **Comparison in time**: domination at variance `T > 0` implies domination at any larger
variance `T'`, since `γ_T ≤ (T'/T)^(d/2) γ_{T'}`. -/
theorem mono (hT : 0 < T) (hTT' : T ≤ T') (hg : PolyGauss T g) : PolyGauss T' g := by
  obtain ⟨K, m, h⟩ := hg
  refine ⟨|K| * (T' / T) ^ ((d : ℝ) / 2), m, fun x => ?_⟩
  have hP : 0 ≤ (1 + ‖x‖) ^ m := by positivity
  calc |g x| ≤ K * (1 + ‖x‖) ^ m * gaussian d T x := h x
    _ ≤ |K| * (1 + ‖x‖) ^ m * gaussian d T x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) hP)
          (gaussian_pos hT x).le
    _ ≤ |K| * (1 + ‖x‖) ^ m * ((T' / T) ^ ((d : ℝ) / 2) * gaussian d T' x) :=
        mul_le_mul_of_nonneg_left (gaussian_le_mul_gaussian hT hTT' x)
          (mul_nonneg (abs_nonneg K) hP)
    _ = |K| * (T' / T) ^ ((d : ℝ) / 2) * (1 + ‖x‖) ^ m * gaussian d T' x := by ring

/-- The heat flow at time `t > 0` of a function dominated at variance `T > 0` is dominated at
variance `T + t`. -/
theorem heat (hT : 0 < T) {t : ℝ} (ht : 0 < t) (hg : PolyGauss T g) :
    PolyGauss (T + t) (Fisher41.heat g t) := by
  obtain ⟨K, m, h⟩ := hg
  exact ⟨K * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + t))), m, abs_heat_le_of_abs_le hT ht h⟩

end PolyGauss

end Fisher41
