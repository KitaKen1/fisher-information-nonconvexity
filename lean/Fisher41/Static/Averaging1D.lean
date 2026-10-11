/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fourier-free Gaussian averaging of a periodic function in one dimension

Let `g : ℝ → ℝ` be continuous, `L`-periodic and bounded by `M`. We show that averaging `g`
against the centered Gaussian density `gauss1 R` of standard deviation `R` approximates the mean
of `g` over a period, with an error `O(M L² / R²)`:

`|∫ g φ_R - (1/L) ∫₀ᴸ g| ≤ 8 M L² / R²`.

## Proof sketch

Let `m` be the mean of `g` and `a = g - m`. The primitive `A x = ∫₀ˣ a` is `L`-periodic with
`|A| ≤ 2 M L`; subtracting its mean gives `A₀` with `|A₀| ≤ 4 M L`, whose primitive `B` is again
`L`-periodic with `|B| ≤ 4 M L²`, and `B'' = a`. Integrating by parts twice on `ℝ`
(boundary terms vanish since `B`, `B'` are bounded and `φ`, `φ'` are integrable),
`∫ a φ = ∫ B φ''`. Finally `∫ |φ''| ≤ 2 / R²`, since `φ'' = (x²/R⁴ - 1/R²) φ` and the second
moment of `φ` is `R²`. No Fourier analysis is used.

## Main results

* `Fisher41.gauss1`: the centered Gaussian density with standard deviation `R`.
* `Fisher41.integral_gauss1`: `∫ gauss1 R = 1`.
* `Fisher41.abs_integral_mul_gauss1_sub_average_le`: the averaging estimate.
-/

open MeasureTheory Real Filter

namespace Fisher41

/-- Centered Gaussian density with standard deviation `R` (variance `R^2`). -/
noncomputable def gauss1 (R x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi) * R)⁻¹ * Real.exp (-x ^ 2 / (2 * R ^ 2))

/-! ### Elementary properties of `gauss1` -/

/-- `gauss1` in the form `c * exp (-b * x ^ 2)` used by Mathlib's Gaussian integral lemmas. -/
theorem gauss1_eq (R x : ℝ) :
    gauss1 R x = (√(2 * π) * R)⁻¹ * exp (-(1 / (2 * R ^ 2)) * x ^ 2) := by
  unfold gauss1
  congr 2
  ring

/-- `gauss1 R` is nonnegative for `0 ≤ R`. -/
theorem gauss1_nonneg {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : 0 ≤ gauss1 R x := by
  unfold gauss1
  positivity

/-- `gauss1 R` is integrable. -/
theorem integrable_gauss1 {R : ℝ} (hR : 0 < R) : Integrable (gauss1 R) := by
  have hb : 0 < 1 / (2 * R ^ 2) := by positivity
  have := (integrable_exp_neg_mul_sq hb).const_mul ((√(2 * π) * R)⁻¹)
  convert this using 1
  funext x
  exact gauss1_eq R x

/-- `x ↦ x * gauss1 R x` is integrable. -/
theorem integrable_mul_gauss1 {R : ℝ} (hR : 0 < R) :
    Integrable (fun x ↦ x * gauss1 R x) := by
  have hb : 0 < 1 / (2 * R ^ 2) := by positivity
  have := (integrable_mul_exp_neg_mul_sq hb).const_mul ((√(2 * π) * R)⁻¹)
  convert this using 1
  funext x
  rw [gauss1_eq]
  ring

/-- `x ↦ x ^ 2 * gauss1 R x` is integrable. -/
theorem integrable_sq_mul_gauss1 {R : ℝ} (hR : 0 < R) :
    Integrable (fun x ↦ x ^ 2 * gauss1 R x) := by
  have hb : 0 < 1 / (2 * R ^ 2) := by positivity
  have := (integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)).const_mul
    ((√(2 * π) * R)⁻¹)
  convert this using 1
  funext x
  rw [gauss1_eq, Real.rpow_two]
  ring

/-- The Gaussian density `gauss1 R` has total mass one. -/
theorem integral_gauss1 {R : ℝ} (hR : 0 < R) : ∫ x, gauss1 R x = 1 := by
  simp_rw [gauss1_eq]
  rw [integral_const_mul, integral_gaussian]
  have h1 : π / (1 / (2 * R ^ 2)) = (√(2 * π) * R) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [h1, Real.sqrt_sq (by positivity)]
  have : √(2 * π) * R ≠ 0 := by positivity
  field_simp

/-- First derivative of `gauss1`: `φ' x = -(x / R²) φ x`. -/
theorem hasDerivAt_gauss1 {R : ℝ} (hR : R ≠ 0) (x : ℝ) :
    HasDerivAt (gauss1 R) (-(x / R ^ 2) * gauss1 R x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -y ^ 2 / (2 * R ^ 2)) (-(x / R ^ 2)) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const (2 * R ^ 2)
    convert this using 1
    field_simp
    ring
  have h2 : HasDerivAt (gauss1 R)
      ((√(2 * π) * R)⁻¹ * (exp (-x ^ 2 / (2 * R ^ 2)) * -(x / R ^ 2))) x :=
    h1.exp.const_mul _
  convert h2 using 1
  unfold gauss1
  ring

/-- Second derivative of `gauss1`: `φ'' x = (x² / R⁴ - 1 / R²) φ x`. -/
theorem hasDerivAt_gauss1_deriv {R : ℝ} (hR : R ≠ 0) (x : ℝ) :
    HasDerivAt (fun y ↦ -(y / R ^ 2) * gauss1 R y)
      ((x ^ 2 / R ^ 4 - 1 / R ^ 2) * gauss1 R x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -(y / R ^ 2)) (-(1 / R ^ 2)) x :=
    ((hasDerivAt_id' x).div_const (R ^ 2)).neg
  have := h1.mul (hasDerivAt_gauss1 hR x)
  convert this using 1
  ring

/-- The first derivative of `gauss1 R` is integrable. -/
theorem integrable_gauss1_deriv {R : ℝ} (hR : 0 < R) :
    Integrable (fun x ↦ -(x / R ^ 2) * gauss1 R x) := by
  have := (integrable_mul_gauss1 hR).const_mul (-(1 / R ^ 2))
  convert this using 1
  funext x
  ring

/-- The second derivative of `gauss1 R` is integrable. -/
theorem integrable_gauss1_deriv2 {R : ℝ} (hR : 0 < R) :
    Integrable (fun x ↦ (x ^ 2 / R ^ 4 - 1 / R ^ 2) * gauss1 R x) := by
  have := ((integrable_sq_mul_gauss1 hR).const_mul (1 / R ^ 4)).sub
    ((integrable_gauss1 hR).const_mul (1 / R ^ 2))
  convert this using 1
  funext x
  simp only [Pi.sub_apply]
  ring

/-- The second moment of `gauss1 R` is `R ^ 2` (proved by integration by parts). -/
theorem integral_sq_mul_gauss1 {R : ℝ} (hR : 0 < R) : ∫ x, x ^ 2 * gauss1 R x = R ^ 2 := by
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x ↦ x)
    (u' := fun _ ↦ (1 : ℝ)) (v := gauss1 R) (v' := fun x ↦ -(x / R ^ 2) * gauss1 R x)
    (fun x _ ↦ hasDerivAt_id' x) (fun x _ ↦ hasDerivAt_gauss1 hR.ne' x) ?_ ?_ ?_
  · have h1 : ∫ x, x * (-(x / R ^ 2) * gauss1 R x) =
        -(1 / R ^ 2) * ∫ x, x ^ 2 * gauss1 R x := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [h1] at key
    simp only [one_mul, integral_gauss1 hR] at key
    have hR2 : R ^ 2 ≠ 0 := by positivity
    field_simp at key
    linarith
  · have := (integrable_sq_mul_gauss1 hR).const_mul (-(1 / R ^ 2))
    convert this using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  · simpa [Pi.mul_def] using integrable_gauss1 hR
  · exact integrable_mul_gauss1 hR

/-- `∫ |φ''| ≤ 2 / R²`, in the form needed below: integrating the second derivative of the
Gaussian `gauss1 R` against a function bounded by `K` gives at most `2 K / R²`. -/
theorem abs_integral_gauss1_deriv2_mul_le {R K : ℝ} (hR : 0 < R) {B : ℝ → ℝ}
    (hBK : ∀ x, |B x| ≤ K) :
    |∫ x, (x ^ 2 / R ^ 4 - 1 / R ^ 2) * gauss1 R x * B x| ≤ 2 * K / R ^ 2 := by
  have hint : Integrable
      (fun x ↦ (K / R ^ 4) * (x ^ 2 * gauss1 R x) + (K / R ^ 2) * gauss1 R x) :=
    ((integrable_sq_mul_gauss1 hR).const_mul _).add ((integrable_gauss1 hR).const_mul _)
  rw [← Real.norm_eq_abs]
  calc ‖∫ x, (x ^ 2 / R ^ 4 - 1 / R ^ 2) * gauss1 R x * B x‖
      ≤ ∫ x, (K / R ^ 4) * (x ^ 2 * gauss1 R x) + (K / R ^ 2) * gauss1 R x := by
        refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun x ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gauss1_nonneg hR.le x)]
        have h0 : 0 ≤ x ^ 2 / R ^ 4 := by positivity
        have h0' : 0 < 1 / R ^ 2 := by positivity
        have h1 : |x ^ 2 / R ^ 4 - 1 / R ^ 2| ≤ x ^ 2 / R ^ 4 + 1 / R ^ 2 := by
          rw [abs_le]
          constructor <;> linarith
        have hφ0 := gauss1_nonneg hR.le x
        calc |x ^ 2 / R ^ 4 - 1 / R ^ 2| * gauss1 R x * |B x|
            ≤ (x ^ 2 / R ^ 4 + 1 / R ^ 2) * gauss1 R x * K :=
              mul_le_mul (mul_le_mul_of_nonneg_right h1 hφ0) (hBK x) (abs_nonneg _)
                (mul_nonneg (by positivity) hφ0)
          _ = (K / R ^ 4) * (x ^ 2 * gauss1 R x) + (K / R ^ 2) * gauss1 R x := by ring
    _ = 2 * K / R ^ 2 := by
        rw [integral_add ((integrable_sq_mul_gauss1 hR).const_mul _)
          ((integrable_gauss1 hR).const_mul _), integral_const_mul, integral_const_mul,
          integral_sq_mul_gauss1 hR, integral_gauss1 hR]
        field_simp
        ring

/-! ### Primitives of periodic functions -/

/-- The primitive `x ↦ ∫₀ˣ f` of a continuous `L`-periodic function with zero integral over a
period is `L`-periodic. -/
theorem periodic_intervalIntegral_of_integral_eq_zero {f : ℝ → ℝ} {L : ℝ} (hf : Continuous f)
    (hper : Function.Periodic f L) (h0 : ∫ x in (0 : ℝ)..L, f x = 0) :
    Function.Periodic (fun x ↦ ∫ t in (0 : ℝ)..x, f t) L := by
  intro x
  simp only
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 x)
    (hf.intervalIntegrable x (x + L)), hper.intervalIntegral_add_eq x 0, zero_add, h0, add_zero]

/-- The primitive `x ↦ ∫₀ˣ f` of a continuous `L`-periodic function bounded by `K` with zero
integral over a period is bounded by `K * L`. -/
theorem abs_intervalIntegral_le_of_periodic {f : ℝ → ℝ} {L K : ℝ} (hL : 0 < L)
    (hf : Continuous f) (hper : Function.Periodic f L) (h0 : ∫ x in (0 : ℝ)..L, f x = 0)
    (hK : ∀ x, |f x| ≤ K) (x : ℝ) : |∫ t in (0 : ℝ)..x, f t| ≤ K * L := by
  obtain ⟨y, hy, hxy⟩ :=
    (periodic_intervalIntegral_of_integral_eq_zero hf hper h0).exists_mem_Ico₀ hL x
  rw [hxy]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := y) (C := K) (f := f)
    (fun t _ ↦ hK t)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hy.1] at this
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  calc |∫ t in (0 : ℝ)..y, f t| ≤ K * y := this
    _ ≤ K * L := mul_le_mul_of_nonneg_left hy.2.le hK0

/-- Subtracting its mean over `[0, L]` from a continuous function gives zero integral over
`[0, L]`. -/
theorem intervalIntegral_sub_div_eq_zero {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : Continuous f) :
    ∫ x in (0 : ℝ)..L, (f x - (∫ t in (0 : ℝ)..L, f t) / L) = 0 := by
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp
  ring

/-- The mean over `[0, L]` of a function bounded by `K` is bounded by `K`. -/
theorem abs_intervalIntegral_div_le {f : ℝ → ℝ} {L K : ℝ} (hL : 0 < L) (hK : ∀ x, |f x| ≤ K) :
    |(∫ t in (0 : ℝ)..L, f t) / L| ≤ K := by
  rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L) (C := K) (f := f)
    (fun t _ ↦ hK t)
  rwa [Real.norm_eq_abs, sub_zero, abs_of_pos hL] at this

/-! ### The averaging estimate -/

/-- **Fourier-free Gaussian averaging.** For a continuous `L`-periodic function `g` bounded by
`M`, the Gaussian average `∫ g · gauss1 R` differs from the mean `(1/L) ∫₀ᴸ g` by at most
`8 M L² / R²`. -/
theorem abs_integral_mul_gauss1_sub_average_le {g : ℝ → ℝ} {L M R : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hg : Continuous g) (hper : Function.Periodic g L)
    (hM : ∀ x, |g x| ≤ M) :
    |(∫ x, g x * gauss1 R x) - (∫ x in (0:ℝ)..L, g x) / L| ≤ 8 * M * L ^ 2 / R ^ 2 := by
  -- the mean `m` and the mean-zero part `a = g - m`
  set m := (∫ x in (0 : ℝ)..L, g x) / L
  set a : ℝ → ℝ := fun x ↦ g x - m
  have ha_cont : Continuous a := hg.sub continuous_const
  have ha_per : Function.Periodic a L := fun x ↦ by simp only [a, hper x]
  have ha0 : ∫ x in (0 : ℝ)..L, a x = 0 := intervalIntegral_sub_div_eq_zero hL hg
  have hm_le : |m| ≤ M := abs_intervalIntegral_div_le hL hM
  have ha_le : ∀ x, |a x| ≤ 2 * M := fun x ↦ by
    have := abs_sub (g x) m
    have := hM x
    simp only [a]
    linarith
  -- the primitive `A` of `a`: periodic, bounded by `2 M L`
  set A : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, a t
  have hA_deriv : ∀ x, HasDerivAt A (a x) x := fun x ↦
    (ha_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hA_cont : Continuous A :=
    continuous_iff_continuousAt.2 fun x ↦ (hA_deriv x).continuousAt
  have hA_le : ∀ x, |A x| ≤ 2 * M * L :=
    abs_intervalIntegral_le_of_periodic hL ha_cont ha_per ha0 ha_le
  have hA_per : Function.Periodic A L :=
    periodic_intervalIntegral_of_integral_eq_zero ha_cont ha_per ha0
  -- the mean-zero part `A₀ = A - c` of `A`: periodic, bounded by `4 M L`, `A₀' = a`
  set c := (∫ x in (0 : ℝ)..L, A x) / L
  set A₀ : ℝ → ℝ := fun x ↦ A x - c
  have hA₀_cont : Continuous A₀ := hA_cont.sub continuous_const
  have hA₀_per : Function.Periodic A₀ L := fun x ↦ by simp only [A₀, hA_per x]
  have hA₀0 : ∫ x in (0 : ℝ)..L, A₀ x = 0 := intervalIntegral_sub_div_eq_zero hL hA_cont
  have hc_le : |c| ≤ 2 * M * L := abs_intervalIntegral_div_le hL hA_le
  have hA₀_le : ∀ x, |A₀ x| ≤ 4 * M * L := fun x ↦ by
    have := abs_sub (A x) c
    have := hA_le x
    simp only [A₀]
    linarith
  have hA₀_deriv : ∀ x, HasDerivAt A₀ (a x) x := fun x ↦ (hA_deriv x).sub_const c
  -- the primitive `B` of `A₀`: bounded by `4 M L²`, `B' = A₀`, `B'' = a`
  set B : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, A₀ t
  have hB_deriv : ∀ x, HasDerivAt B (A₀ x) x := fun x ↦
    (hA₀_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hB_cont : Continuous B :=
    continuous_iff_continuousAt.2 fun x ↦ (hB_deriv x).continuousAt
  have hB_le : ∀ x, |B x| ≤ 4 * M * L * L :=
    abs_intervalIntegral_le_of_periodic hL hA₀_cont hA₀_per hA₀0 hA₀_le
  -- integrability of the products appearing in the integrations by parts
  have hφ := integrable_gauss1 hR
  have hφ' := integrable_gauss1_deriv hR
  have hφ'' := integrable_gauss1_deriv2 hR
  have hint_φa : Integrable (fun x ↦ gauss1 R x * a x) :=
    hφ.mul_bdd ha_cont.aestronglyMeasurable (Eventually.of_forall fun x ↦ ha_le x)
  have hint_φA₀ : Integrable (fun x ↦ gauss1 R x * A₀ x) :=
    hφ.mul_bdd hA₀_cont.aestronglyMeasurable (Eventually.of_forall fun x ↦ hA₀_le x)
  have hint_φ'A₀ : Integrable (fun x ↦ -(x / R ^ 2) * gauss1 R x * A₀ x) :=
    hφ'.mul_bdd hA₀_cont.aestronglyMeasurable (Eventually.of_forall fun x ↦ hA₀_le x)
  have hint_φ'B : Integrable (fun x ↦ -(x / R ^ 2) * gauss1 R x * B x) :=
    hφ'.mul_bdd hB_cont.aestronglyMeasurable (Eventually.of_forall fun x ↦ hB_le x)
  have hint_φ''B : Integrable (fun x ↦ (x ^ 2 / R ^ 4 - 1 / R ^ 2) * gauss1 R x * B x) :=
    hφ''.mul_bdd hB_cont.aestronglyMeasurable (Eventually.of_forall fun x ↦ hB_le x)
  -- first integration by parts: `∫ φ a = -∫ φ' A₀`
  have ibp1 : ∫ x, gauss1 R x * a x = -∫ x, -(x / R ^ 2) * gauss1 R x * A₀ x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (u := gauss1 R)
      (u' := fun x ↦ -(x / R ^ 2) * gauss1 R x) (v := A₀) (v' := a)
      (fun x _ ↦ hasDerivAt_gauss1 hR.ne' x) (fun x _ ↦ hA₀_deriv x)
      hint_φa hint_φ'A₀ hint_φA₀
  -- second integration by parts: `∫ φ' A₀ = -∫ φ'' B`
  have ibp2 : ∫ x, -(x / R ^ 2) * gauss1 R x * A₀ x =
      -∫ x, (x ^ 2 / R ^ 4 - 1 / R ^ 2) * gauss1 R x * B x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x ↦ -(x / R ^ 2) * gauss1 R x)
      (u' := fun x ↦ (x ^ 2 / R ^ 4 - 1 / R ^ 2) * gauss1 R x) (v := B) (v' := A₀)
      (fun x _ ↦ hasDerivAt_gauss1_deriv hR.ne' x) (fun x _ ↦ hB_deriv x)
      hint_φ'A₀ hint_φ''B hint_φ'B
  -- the left-hand side is `∫ φ a`, using `∫ φ = 1`
  have hlhs : (∫ x, g x * gauss1 R x) - m = ∫ x, gauss1 R x * a x := by
    have hgφ : Integrable (fun x ↦ g x * gauss1 R x) := by
      have := hφ.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall fun x ↦ hM x)
      simpa only [mul_comm] using this
    have : (fun x ↦ gauss1 R x * a x) = fun x ↦ g x * gauss1 R x - m * gauss1 R x := by
      funext x
      simp only [a]
      ring
    rw [this, integral_sub hgφ (hφ.const_mul m), integral_const_mul, integral_gauss1 hR,
      mul_one]
  rw [hlhs, ibp1, ibp2, neg_neg]
  calc |∫ x, (x ^ 2 / R ^ 4 - 1 / R ^ 2) * gauss1 R x * B x|
      ≤ 2 * (4 * M * L * L) / R ^ 2 := abs_integral_gauss1_deriv2_mul_le hR hB_le
    _ = 8 * M * L ^ 2 / R ^ 2 := by ring

end Fisher41
