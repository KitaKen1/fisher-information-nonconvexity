/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The flat cutoff `η` and explicit bounds on its first three derivatives

We define the cutoff
`η(v) = b(2 - v) / (b(2 - v) + b(v - 1))`, where `b = expNegInvGlue`
(`b a = exp (-1/a)` for `a > 0` and `b a = 0` for `a ≤ 0`).

## Main results

* `Fisher41.eta_eq_smoothTransition`: `η v = Real.smoothTransition (2 - v)`.
* `Fisher41.contDiff_eta`: `η` is smooth.
* `Fisher41.eta_of_le_one`, `Fisher41.eta_of_two_le`, `Fisher41.eta_nonneg`,
  `Fisher41.eta_le_one`: `η = 1` on `(-∞, 1]`, `η = 0` on `[2, ∞)`, and `0 ≤ η ≤ 1`.
* `Fisher41.abs_deriv_eta_le`, `Fisher41.abs_iteratedDeriv_two_eta_le`,
  `Fisher41.abs_iteratedDeriv_three_eta_le`: the deliberately crude bounds
  `|η'| ≤ 300`, `|η''| ≤ 30000`, `|η'''| ≤ 3000000` on all of `ℝ`.

## Proof sketch

* By `expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul`, at *every* point of `ℝ` we have
  `b' = b₁`, `b₁' = b₂`, `b₂' = b₃`, where `bₖ x = Pₖ(x⁻¹) b(x)` with
  `P₁ = X²`, `P₂ = X⁴ - 2X³`, `P₃ = X⁶ - 6X⁵ + 6X⁴`.
* Since `yⁿ e^{-y} ≤ n!` for `y ≥ 0`, we get `|b₁| ≤ 2`, `|b₂| ≤ 36`, `|b₃| ≤ 1584`.
* The denominator `G(v) = b(2 - v) + b(v - 1)` satisfies `G ≥ e⁻² ≥ 1/8` everywhere (one of
  `2 - v`, `v - 1` is at least `1/2`), and `|G'| ≤ 4`, `|G''| ≤ 72`, `|G'''| ≤ 3168`.
* Differentiating the identity `η · G = A`, `A = b(2 - ·)`, three times (Leibniz rule) gives
  `η' G = A' - η G'`, `η'' G = A'' - 2 η' G' - η G''`,
  `η''' G = A''' - 3 η'' G' - 3 η' G'' - η G'''`; together with `|η| ≤ 1` this yields
  recursively `|η'| ≤ 48`, `|η''| ≤ 3936`, `|η'''| ≤ 498816`.

The argument works on all of `ℝ` at once, so no separate treatment of the points `1` and `2`
(or of the region where `η` is locally constant) is needed.
-/

open scoped ContDiff

namespace Fisher41

/-- The flat cutoff of the construction:
`η(v) = b(2-v) / (b(2-v) + b(v-1))` with `b = expNegInvGlue`
(`b a = exp(-1/a)` for `a > 0`, else `0`). -/
noncomputable def eta (v : ℝ) : ℝ :=
  expNegInvGlue (2 - v) / (expNegInvGlue (2 - v) + expNegInvGlue (v - 1))

/-- `η` is the reflected and shifted smooth transition function:
`η v = Real.smoothTransition (2 - v)`. -/
theorem eta_eq_smoothTransition (v : ℝ) : eta v = Real.smoothTransition (2 - v) := by
  rw [eta, Real.smoothTransition, show (1 : ℝ) - (2 - v) = v - 1 by ring]

/-- `η` is smooth (`C^∞`). -/
theorem contDiff_eta : ContDiff ℝ ∞ eta := by
  have h : eta = fun v => Real.smoothTransition (2 - v) := funext eta_eq_smoothTransition
  rw [h]
  exact Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

/-- `η = 1` on `(-∞, 1]`. -/
theorem eta_of_le_one {v : ℝ} (hv : v ≤ 1) : eta v = 1 := by
  rw [eta_eq_smoothTransition]
  exact Real.smoothTransition.one_of_one_le (by linarith)

/-- `η = 0` on `[2, ∞)`. -/
theorem eta_of_two_le {v : ℝ} (hv : 2 ≤ v) : eta v = 0 := by
  rw [eta_eq_smoothTransition]
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- `η` is nonnegative. -/
theorem eta_nonneg (v : ℝ) : 0 ≤ eta v := by
  rw [eta_eq_smoothTransition]
  exact Real.smoothTransition.nonneg _

/-- `η` is at most one. -/
theorem eta_le_one (v : ℝ) : eta v ≤ 1 := by
  rw [eta_eq_smoothTransition]
  exact Real.smoothTransition.le_one _

/-- `|η| ≤ 1`. -/
theorem abs_eta_le_one (v : ℝ) : |eta v| ≤ 1 :=
  abs_le.2 ⟨by linarith [eta_nonneg v], eta_le_one v⟩

namespace Cutoff

/-! ### Derivatives of `b = expNegInvGlue` -/

section GlueDerivatives

open Polynomial

/-- `b₁ x = (x⁻¹)² b(x)`: the derivative of `b = expNegInvGlue` (at every point of `ℝ`). -/
noncomputable def b1 (x : ℝ) : ℝ := x⁻¹ ^ 2 * expNegInvGlue x

/-- `b₂ x = ((x⁻¹)⁴ - 2 (x⁻¹)³) b(x)`: the second derivative of `b = expNegInvGlue`. -/
noncomputable def b2 (x : ℝ) : ℝ := (x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3) * expNegInvGlue x

/-- `b₃ x = ((x⁻¹)⁶ - 6 (x⁻¹)⁵ + 6 (x⁻¹)⁴) b(x)`: the third derivative of `b = expNegInvGlue`. -/
noncomputable def b3 (x : ℝ) : ℝ := (x⁻¹ ^ 6 - 6 * x⁻¹ ^ 5 + 6 * x⁻¹ ^ 4) * expNegInvGlue x

/-- `b' = b₁` everywhere. -/
theorem hasDerivAt_b (x : ℝ) : HasDerivAt expNegInvGlue (b1 x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x
  have hf : (fun y : ℝ => (1 : ℝ[X]).eval y⁻¹ * expNegInvGlue y) = expNegInvGlue := by
    funext y
    rw [eval_one, one_mul]
  rw [hf] at h
  refine h.congr_deriv ?_
  rw [b1, derivative_one, sub_zero, mul_one, eval_pow, eval_X]

/-- `b₁' = b₂` everywhere. -/
theorem hasDerivAt_b1 (x : ℝ) : HasDerivAt b1 (b2 x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (X ^ 2) x
  have hf : (fun y : ℝ => (X ^ 2 : ℝ[X]).eval y⁻¹ * expNegInvGlue y) = b1 := by
    funext y
    rw [b1, eval_pow, eval_X]
  have hd : (X ^ 2 * (X ^ 2 - derivative (X ^ 2)) : ℝ[X]).eval x⁻¹ =
      x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3 := by
    simp
    ring
  rw [hf] at h
  refine h.congr_deriv ?_
  rw [hd, b2]

/-- `b₂' = b₃` everywhere. -/
theorem hasDerivAt_b2 (x : ℝ) : HasDerivAt b2 (b3 x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (X ^ 4 - 2 * X ^ 3) x
  have hf : (fun y : ℝ => (X ^ 4 - 2 * X ^ 3 : ℝ[X]).eval y⁻¹ * expNegInvGlue y) = b2 := by
    funext y
    simp only [b2, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
  have hd : (X ^ 2 * (X ^ 4 - 2 * X ^ 3 - derivative (X ^ 4 - 2 * X ^ 3)) : ℝ[X]).eval x⁻¹ =
      x⁻¹ ^ 6 - 6 * x⁻¹ ^ 5 + 6 * x⁻¹ ^ 4 := by
    simp
    ring
  rw [hf] at h
  refine h.congr_deriv ?_
  rw [hd, b3]

end GlueDerivatives

/-! ### Bounds on `b₁, b₂, b₃` -/

/-- `b x = exp (-x⁻¹)` for `x > 0`. -/
theorem expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) : expNegInvGlue x = Real.exp (-x⁻¹) := by
  simp [expNegInvGlue, not_le.2 hx]

/-- `yⁿ e^{-y} ≤ n!` for `y ≥ 0`. -/
theorem pow_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    y ^ n * Real.exp (-y) ≤ n.factorial := by
  have h := Real.pow_div_factorial_le_exp y hy n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos y)]
  linarith [mul_comm (Real.exp y) (n.factorial : ℝ)]

/-- `|y² e^{-y}| ≤ 2` for `y ≥ 0`. -/
theorem abs_poly1_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) : |y ^ 2 * Real.exp (-y)| ≤ 2 := by
  have h2 := pow_mul_exp_neg_le hy 2
  rw [show Nat.factorial 2 = 2 from rfl, Nat.cast_ofNat] at h2
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hy 2) (Real.exp_pos _).le)]
  exact h2

/-- `|(y⁴ - 2y³) e^{-y}| ≤ 36` for `y ≥ 0`. -/
theorem abs_poly2_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) :
    |(y ^ 4 - 2 * y ^ 3) * Real.exp (-y)| ≤ 36 := by
  have h3 := pow_mul_exp_neg_le hy 3
  have h4 := pow_mul_exp_neg_le hy 4
  rw [show Nat.factorial 3 = 6 from rfl, Nat.cast_ofNat] at h3
  rw [show Nat.factorial 4 = 24 from rfl, Nat.cast_ofNat] at h4
  have p3 := mul_nonneg (pow_nonneg hy 3) (Real.exp_pos (-y)).le
  have p4 := mul_nonneg (pow_nonneg hy 4) (Real.exp_pos (-y)).le
  rw [abs_le]
  constructor <;> nlinarith

/-- `|(y⁶ - 6y⁵ + 6y⁴) e^{-y}| ≤ 1584` for `y ≥ 0`. -/
theorem abs_poly3_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) :
    |(y ^ 6 - 6 * y ^ 5 + 6 * y ^ 4) * Real.exp (-y)| ≤ 1584 := by
  have h4 := pow_mul_exp_neg_le hy 4
  have h5 := pow_mul_exp_neg_le hy 5
  have h6 := pow_mul_exp_neg_le hy 6
  rw [show Nat.factorial 4 = 24 from rfl, Nat.cast_ofNat] at h4
  rw [show Nat.factorial 5 = 120 from rfl, Nat.cast_ofNat] at h5
  rw [show Nat.factorial 6 = 720 from rfl, Nat.cast_ofNat] at h6
  have p4 := mul_nonneg (pow_nonneg hy 4) (Real.exp_pos (-y)).le
  have p5 := mul_nonneg (pow_nonneg hy 5) (Real.exp_pos (-y)).le
  have p6 := mul_nonneg (pow_nonneg hy 6) (Real.exp_pos (-y)).le
  rw [abs_le]
  constructor <;> nlinarith

/-- `|b₁| ≤ 2` everywhere. -/
theorem abs_b1_le (x : ℝ) : |b1 x| ≤ 2 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [b1, expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    norm_num
  · rw [b1, expNegInvGlue_of_pos hx]
    exact abs_poly1_mul_exp_neg_le (inv_nonneg.2 hx.le)

/-- `|b₂| ≤ 36` everywhere. -/
theorem abs_b2_le (x : ℝ) : |b2 x| ≤ 36 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [b2, expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    norm_num
  · rw [b2, expNegInvGlue_of_pos hx]
    exact abs_poly2_mul_exp_neg_le (inv_nonneg.2 hx.le)

/-- `|b₃| ≤ 1584` everywhere. -/
theorem abs_b3_le (x : ℝ) : |b3 x| ≤ 1584 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [b3, expNegInvGlue.zero_of_nonpos hx, mul_zero, abs_zero]
    norm_num
  · rw [b3, expNegInvGlue_of_pos hx]
    exact abs_poly3_mul_exp_neg_le (inv_nonneg.2 hx.le)

/-! ### The denominator `G(v) = b(2 - v) + b(v - 1)` and its derivatives -/

/-- The denominator `G v = b(2 - v) + b(v - 1)` of `η`. -/
noncomputable def den (v : ℝ) : ℝ := expNegInvGlue (2 - v) + expNegInvGlue (v - 1)

/-- `G' v = -b₁(2 - v) + b₁(v - 1)`. -/
noncomputable def den1 (v : ℝ) : ℝ := -b1 (2 - v) + b1 (v - 1)

/-- `G'' v = b₂(2 - v) + b₂(v - 1)`. -/
noncomputable def den2 (v : ℝ) : ℝ := b2 (2 - v) + b2 (v - 1)

/-- `G''' v = -b₃(2 - v) + b₃(v - 1)`. -/
noncomputable def den3 (v : ℝ) : ℝ := -b3 (2 - v) + b3 (v - 1)

/-- Derivative of the numerator `A v = b(2 - v)`. -/
theorem hasDerivAt_num (v : ℝ) :
    HasDerivAt (fun w => expNegInvGlue (2 - w)) (-b1 (2 - v)) v :=
  (hasDerivAt_b (2 - v)).comp_const_sub 2 v

/-- Second derivative of the numerator `A v = b(2 - v)`. -/
theorem hasDerivAt_num1 (v : ℝ) : HasDerivAt (fun w => -b1 (2 - w)) (b2 (2 - v)) v := by
  have h := ((hasDerivAt_b1 (2 - v)).comp_const_sub 2 v).fun_neg
  rwa [neg_neg] at h

/-- Third derivative of the numerator `A v = b(2 - v)`. -/
theorem hasDerivAt_num2 (v : ℝ) : HasDerivAt (fun w => b2 (2 - w)) (-b3 (2 - v)) v :=
  (hasDerivAt_b2 (2 - v)).comp_const_sub 2 v

/-- `G' = den1`. -/
theorem hasDerivAt_den (v : ℝ) : HasDerivAt den (den1 v) v := by
  have h := ((hasDerivAt_b (2 - v)).comp_const_sub 2 v).fun_add
    ((hasDerivAt_b (v - 1)).comp_sub_const v 1)
  exact h

/-- `den1' = den2`. -/
theorem hasDerivAt_den1 (v : ℝ) : HasDerivAt den1 (den2 v) v := by
  have h := ((hasDerivAt_b1 (2 - v)).comp_const_sub 2 v).fun_neg.fun_add
    ((hasDerivAt_b1 (v - 1)).comp_sub_const v 1)
  rw [neg_neg] at h
  exact h

/-- `den2' = den3`. -/
theorem hasDerivAt_den2 (v : ℝ) : HasDerivAt den2 (den3 v) v := by
  have h := ((hasDerivAt_b2 (2 - v)).comp_const_sub 2 v).fun_add
    ((hasDerivAt_b2 (v - 1)).comp_sub_const v 1)
  exact h

/-- `e⁻² ≥ 1/8`. -/
theorem one_div_eight_le_exp_neg_two : (1 : ℝ) / 8 ≤ Real.exp (-2) := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : Real.exp 2 ≤ 8 := by
    rw [h2]
    nlinarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (Real.exp_pos 2) h3

/-- The denominator is bounded below: `G ≥ 1/8` everywhere. -/
theorem one_div_eight_le_den (v : ℝ) : 1 / 8 ≤ den v := by
  have hb : (1 : ℝ) / 8 ≤ expNegInvGlue (1 / 2) := by
    rw [expNegInvGlue_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      show -((1 : ℝ) / 2)⁻¹ = -2 by norm_num]
    exact one_div_eight_le_exp_neg_two
  rcases le_total ((1 : ℝ) / 2) (2 - v) with h | h
  · have h1 := expNegInvGlue.monotone h
    have h2 := expNegInvGlue.nonneg (v - 1)
    rw [den]
    linarith
  · have h1 := expNegInvGlue.monotone (show (1 : ℝ) / 2 ≤ v - 1 by linarith)
    have h2 := expNegInvGlue.nonneg (2 - v)
    rw [den]
    linarith

/-- The denominator is positive. -/
theorem den_pos (v : ℝ) : 0 < den v :=
  lt_of_lt_of_le (by norm_num) (one_div_eight_le_den v)

/-- `|G'| ≤ 4`. -/
theorem abs_den1_le (v : ℝ) : |den1 v| ≤ 4 := by
  have h1 := abs_le.1 (abs_b1_le (2 - v))
  have h2 := abs_le.1 (abs_b1_le (v - 1))
  rw [den1, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `|G''| ≤ 72`. -/
theorem abs_den2_le (v : ℝ) : |den2 v| ≤ 72 := by
  have h1 := abs_le.1 (abs_b2_le (2 - v))
  have h2 := abs_le.1 (abs_b2_le (v - 1))
  rw [den2, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `|G'''| ≤ 3168`. -/
theorem abs_den3_le (v : ℝ) : |den3 v| ≤ 3168 := by
  have h1 := abs_le.1 (abs_b3_le (2 - v))
  have h2 := abs_le.1 (abs_b3_le (v - 1))
  rw [den3, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Differentiating `η · G = b(2 - ·)` -/

/-- The defining identity `η · G = b(2 - ·)`. -/
theorem eta_mul_den (v : ℝ) : eta v * den v = expNegInvGlue (2 - v) := by
  rw [eta]
  exact div_mul_cancel₀ _ (den_pos v).ne'

/-- `η` is differentiable. -/
theorem differentiable_eta : Differentiable ℝ eta :=
  (contDiff_infty_iff_deriv.1 contDiff_eta).1

/-- `η'` is smooth. -/
theorem contDiff_deriv_eta : ContDiff ℝ ∞ (deriv eta) :=
  (contDiff_infty_iff_deriv.1 contDiff_eta).2

/-- `η'` is differentiable. -/
theorem differentiable_deriv_eta : Differentiable ℝ (deriv eta) :=
  (contDiff_infty_iff_deriv.1 contDiff_deriv_eta).1

/-- `η''` is differentiable. -/
theorem differentiable_deriv_deriv_eta : Differentiable ℝ (deriv (deriv eta)) :=
  (contDiff_infty_iff_deriv.1 (contDiff_infty_iff_deriv.1 contDiff_deriv_eta).2).1

/-- First derivative of `η · G = A`: `η' G + η G' = A'`. -/
theorem deriv_eta_identity (v : ℝ) :
    deriv eta v * den v + eta v * den1 v = -b1 (2 - v) := by
  have h1 := (differentiable_eta v).hasDerivAt.fun_mul (hasDerivAt_den v)
  have h2 : HasDerivAt (fun w => eta w * den w) (-b1 (2 - v)) v :=
    (hasDerivAt_num v).congr_of_eventuallyEq (Filter.Eventually.of_forall eta_mul_den)
  exact h1.unique h2

/-- Second derivative of `η · G = A`: `η'' G + 2 η' G' + η G'' = A''`. -/
theorem deriv2_eta_identity (v : ℝ) :
    deriv (deriv eta) v * den v + 2 * (deriv eta v * den1 v) + eta v * den2 v = b2 (2 - v) := by
  have h1 := ((differentiable_deriv_eta v).hasDerivAt.fun_mul (hasDerivAt_den v)).fun_add
    ((differentiable_eta v).hasDerivAt.fun_mul (hasDerivAt_den1 v))
  have h2 : HasDerivAt (fun w => deriv eta w * den w + eta w * den1 w) (b2 (2 - v)) v :=
    (hasDerivAt_num1 v).congr_of_eventuallyEq (Filter.Eventually.of_forall deriv_eta_identity)
  have := h1.unique h2
  linarith

/-- Third derivative of `η · G = A`: `η''' G + 3 η'' G' + 3 η' G'' + η G''' = A'''`. -/
theorem deriv3_eta_identity (v : ℝ) :
    deriv (deriv (deriv eta)) v * den v + 3 * (deriv (deriv eta) v * den1 v) +
      3 * (deriv eta v * den2 v) + eta v * den3 v = -b3 (2 - v) := by
  have h1 := (((differentiable_deriv_deriv_eta v).hasDerivAt.fun_mul (hasDerivAt_den v)).fun_add
    (((differentiable_deriv_eta v).hasDerivAt.fun_mul (hasDerivAt_den1 v)).const_mul 2)).fun_add
    ((differentiable_eta v).hasDerivAt.fun_mul (hasDerivAt_den2 v))
  have h2 : HasDerivAt
      (fun w => deriv (deriv eta) w * den w + 2 * (deriv eta w * den1 w) + eta w * den2 w)
      (-b3 (2 - v)) v :=
    (hasDerivAt_num2 v).congr_of_eventuallyEq (Filter.Eventually.of_forall deriv2_eta_identity)
  have := h1.unique h2
  linarith

/-! ### The bounds -/

/-- `|x y| ≤ X Y` whenever `|x| ≤ X` and `|y| ≤ Y`. -/
theorem abs_mul_le_of_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)

/-- If `x G(v) = r` and `|r| ≤ c`, then `|x| ≤ 8 c` (since `G ≥ 1/8`). -/
theorem abs_le_of_mul_den_eq {x r c : ℝ} (v : ℝ) (h : x * den v = r) (hr : |r| ≤ c) :
    |x| ≤ 8 * c := by
  have hg := one_div_eight_le_den v
  have h1 : |x| * den v ≤ c := by
    calc |x| * den v = |x * den v| := by rw [abs_mul, abs_of_pos (den_pos v)]
      _ = |r| := by rw [h]
      _ ≤ c := hr
  nlinarith [abs_nonneg x]

/-- `|η'| ≤ 48`. -/
theorem abs_deriv_eta_le_48 (v : ℝ) : |deriv eta v| ≤ 48 := by
  have hb := abs_le.1 (abs_b1_le (2 - v))
  have hp := abs_le.1 (abs_mul_le_of_le (abs_eta_le_one v) (abs_den1_le v))
  have hr : |-b1 (2 - v) - eta v * den1 v| ≤ 6 := by
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2, hp.1, hp.2]
  have h := abs_le_of_mul_den_eq v
    (by linarith [deriv_eta_identity v] :
      deriv eta v * den v = -b1 (2 - v) - eta v * den1 v) hr
  linarith

/-- `|η''| ≤ 3936`. -/
theorem abs_deriv2_eta_le (v : ℝ) : |deriv (deriv eta) v| ≤ 3936 := by
  have hb := abs_le.1 (abs_b2_le (2 - v))
  have hp1 := abs_le.1 (abs_mul_le_of_le (abs_deriv_eta_le_48 v) (abs_den1_le v))
  have hp2 := abs_le.1 (abs_mul_le_of_le (abs_eta_le_one v) (abs_den2_le v))
  have hr : |b2 (2 - v) - 2 * (deriv eta v * den1 v) - eta v * den2 v| ≤ 492 := by
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2, hp1.1, hp1.2, hp2.1, hp2.2]
  have h := abs_le_of_mul_den_eq v
    (by linarith [deriv2_eta_identity v] :
      deriv (deriv eta) v * den v = b2 (2 - v) - 2 * (deriv eta v * den1 v) - eta v * den2 v) hr
  linarith

/-- `|η'''| ≤ 498816`. -/
theorem abs_deriv3_eta_le (v : ℝ) : |deriv (deriv (deriv eta)) v| ≤ 498816 := by
  have hb := abs_le.1 (abs_b3_le (2 - v))
  have hp1 := abs_le.1 (abs_mul_le_of_le (abs_deriv2_eta_le v) (abs_den1_le v))
  have hp2 := abs_le.1 (abs_mul_le_of_le (abs_deriv_eta_le_48 v) (abs_den2_le v))
  have hp3 := abs_le.1 (abs_mul_le_of_le (abs_eta_le_one v) (abs_den3_le v))
  have hr : |-b3 (2 - v) - 3 * (deriv (deriv eta) v * den1 v) - 3 * (deriv eta v * den2 v) -
      eta v * den3 v| ≤ 62352 := by
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2, hp1.1, hp1.2, hp2.1, hp2.2, hp3.1, hp3.2]
  have h := abs_le_of_mul_den_eq v
    (by linarith [deriv3_eta_identity v] :
      deriv (deriv (deriv eta)) v * den v = -b3 (2 - v) - 3 * (deriv (deriv eta) v * den1 v) -
        3 * (deriv eta v * den2 v) - eta v * den3 v) hr
  linarith

end Cutoff

/-- `|η'| ≤ 300` on all of `ℝ` (in fact `|η'| ≤ 48`, see `Fisher41.Cutoff.abs_deriv_eta_le_48`). -/
theorem abs_deriv_eta_le (v : ℝ) : |deriv eta v| ≤ 300 := by
  linarith [Cutoff.abs_deriv_eta_le_48 v]

/-- `|η''| ≤ 30000` on all of `ℝ` (in fact `|η''| ≤ 3936`, see
`Fisher41.Cutoff.abs_deriv2_eta_le`). -/
theorem abs_iteratedDeriv_two_eta_le (v : ℝ) : |iteratedDeriv 2 eta v| ≤ 30000 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  linarith [Cutoff.abs_deriv2_eta_le v]

/-- `|η'''| ≤ 3000000` on all of `ℝ` (in fact `|η'''| ≤ 498816`, see
`Fisher41.Cutoff.abs_deriv3_eta_le`). -/
theorem abs_iteratedDeriv_three_eta_le (v : ℝ) : |iteratedDeriv 3 eta v| ≤ 3000000 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  linarith [Cutoff.abs_deriv3_eta_le v]

end Fisher41
