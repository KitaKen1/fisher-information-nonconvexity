/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Error bound for the midpoint rule

For a twice differentiable `F : ℝ → ℝ` with `|F''| ≤ M` on `[a, b]`, the midpoint rule satisfies

  `|∫ x in a..b, F x - (b - a) * F ((a + b) / 2)| ≤ M * (b - a) ^ 3 / 24`.

This is used to turn a computer-checked certificate (a finite sum of midpoint values together
with a bound on the second derivative) into a rigorous bound on a real integral.

The derivatives are given as explicit functions `F1`, `F2` with `HasDerivAt` hypotheses on all
of `ℝ`; no continuity or integrability of `F2` is needed.

## Proof outline

Put `m = (a + b) / 2`. A function `g` with `g m = g' m = 0` and `g'' ≥ 0` on `[a, b]` is
nonnegative on `[a, b]` (`g'` is monotone, hence of the sign of `x - m`, so `g` decreases up to
`m` and increases afterwards). Applied to the differences between `F` and the quadratics
`F m + F' m (x - m) ± M (x - m) ^ 2 / 2`, this sandwiches `F` between two quadratics on
`[a, b]`, whose integrals are computed by the fundamental theorem of calculus.

## Main results

* `Fisher41.midpoint_abs_sub_le`: the two-sided midpoint error bound.
* `Fisher41.integral_le_midpoint_add`: the upper bound on the integral.
-/

open Set intervalIntegral

namespace Fisher41

/-- If `g m = g' m = 0` and `g'' ≥ 0` on `[a, b] ∋ m`, then `g ≥ 0` on `[a, b]`. -/
theorem nonneg_of_hasDerivAt_of_hasDerivAt_nonneg {g g1 g2 : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g1 x) x) (hg1 : ∀ x, HasDerivAt g1 (g2 x) x)
    {a b m : ℝ} (hm : m ∈ Icc a b) (h0 : g m = 0) (h1 : g1 m = 0)
    (h2 : ∀ x ∈ Icc a b, 0 ≤ g2 x) : ∀ x ∈ Icc a b, 0 ≤ g x := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hg1c : Continuous g1 := continuous_iff_continuousAt.2 fun x => (hg1 x).continuousAt
  have hmono : MonotoneOn g1 (Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hg1c.continuousOn
      (fun x _ => (hg1 x).hasDerivWithinAt) fun x hx => h2 x (interior_subset hx)
  intro x hx
  rcases le_total m x with hmx | hxm
  · -- on `[m, b]` the derivative `g1` is nonnegative, so `g` is monotone there
    have hgm : MonotoneOn g (Icc m b) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc m b) hgc.continuousOn
        (fun y _ => (hg y).hasDerivWithinAt) fun y hy => ?_
      rw [interior_Icc] at hy
      rw [← h1]
      exact hmono hm ⟨hm.1.trans hy.1.le, hy.2.le⟩ hy.1.le
    rw [← h0]
    exact hgm ⟨le_rfl, hm.2⟩ ⟨hmx, hx.2⟩ hmx
  · -- on `[a, m]` the derivative `g1` is nonpositive, so `g` is antitone there
    have hga : AntitoneOn g (Icc a m) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a m) hgc.continuousOn
        (fun y _ => (hg y).hasDerivWithinAt) fun y hy => ?_
      rw [interior_Icc] at hy
      rw [← h1]
      exact hmono ⟨hy.1.le, hy.2.le.trans hm.2⟩ hm hy.2.le
    rw [← h0]
    exact hga ⟨hx.1, hxm⟩ ⟨hm.1, le_rfl⟩ hxm

/-- If `F'' ≤ c` on `[a, b] ∋ m`, then `F` lies below its second-order Taylor polynomial at `m`
with leading coefficient `c` on `[a, b]`. -/
theorem le_taylor_quadratic {F F1 F2 : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F1 x) x) (hF1 : ∀ x, HasDerivAt F1 (F2 x) x)
    {a b m c : ℝ} (hm : m ∈ Icc a b) (hc : ∀ x ∈ Icc a b, F2 x ≤ c) :
    ∀ x ∈ Icc a b, F x ≤ F m + F1 m * (x - m) + c * (x - m) ^ 2 / 2 := by
  have key := nonneg_of_hasDerivAt_of_hasDerivAt_nonneg
    (g := fun x => F m + F1 m * (x - m) + c * (x - m) ^ 2 / 2 - F x)
    (g1 := fun x => F1 m + c * (x - m) - F1 x) (g2 := fun x => c - F2 x)
    (fun y => by
      have h1 : HasDerivAt (fun y => y - m) 1 y := (hasDerivAt_id' y).sub_const m
      convert ((((h1.const_mul (F1 m)).const_add (F m)).add
        (((h1.fun_pow 2).const_mul c).div_const 2)).sub (hF y)) using 1
      push_cast
      ring)
    (fun y => by
      have h1 : HasDerivAt (fun y => y - m) 1 y := (hasDerivAt_id' y).sub_const m
      convert ((h1.const_mul c).const_add (F1 m)).sub (hF1 y) using 1
      ring)
    hm (by simp) (by simp) fun y hy => sub_nonneg.2 (hc y hy)
  intro x hx
  have := key x hx
  linarith

/-- If `c ≤ F''` on `[a, b] ∋ m`, then `F` lies above its second-order Taylor polynomial at `m`
with leading coefficient `c` on `[a, b]`. -/
theorem taylor_quadratic_le {F F1 F2 : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F1 x) x) (hF1 : ∀ x, HasDerivAt F1 (F2 x) x)
    {a b m c : ℝ} (hm : m ∈ Icc a b) (hc : ∀ x ∈ Icc a b, c ≤ F2 x) :
    ∀ x ∈ Icc a b, F m + F1 m * (x - m) + c * (x - m) ^ 2 / 2 ≤ F x := by
  intro x hx
  have := le_taylor_quadratic (F := fun x => -F x) (F1 := fun x => -F1 x)
    (F2 := fun x => -F2 x) (c := -c) (fun y => (hF y).neg) (fun y => (hF1 y).neg) hm
    (fun y hy => neg_le_neg (hc y hy)) x hx
  linarith

/-- An antiderivative of the quadratic `c0 + c1 * (x - m) + c2 * (x - m) ^ 2 / 2`. -/
theorem hasDerivAt_taylor_cubic (c0 c1 c2 m x : ℝ) :
    HasDerivAt (fun y => c0 * (y - m) + c1 * (y - m) ^ 2 / 2 + c2 * (y - m) ^ 3 / 6)
      (c0 + c1 * (x - m) + c2 * (x - m) ^ 2 / 2) x := by
  have h1 : HasDerivAt (fun y => y - m) 1 x := (hasDerivAt_id' x).sub_const m
  convert ((h1.const_mul c0).add (((h1.fun_pow 2).const_mul c1).div_const 2)).add
    (((h1.fun_pow 3).const_mul c2).div_const 6) using 1
  push_cast
  ring

/-- The midpoint rule is exact up to the quadratic term for quadratics centred at the
midpoint. -/
theorem integral_taylor_quadratic_midpoint (c0 c1 c2 a b : ℝ) :
    ∫ x in a..b, (c0 + c1 * (x - (a + b) / 2) + c2 * (x - (a + b) / 2) ^ 2 / 2) =
      (b - a) * c0 + c2 * (b - a) ^ 3 / 24 := by
  rw [integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_taylor_cubic c0 c1 c2 ((a + b) / 2) x)
    ((by fun_prop : Continuous fun x : ℝ =>
      c0 + c1 * (x - (a + b) / 2) + c2 * (x - (a + b) / 2) ^ 2 / 2).intervalIntegrable a b)]
  ring

/-- **Midpoint rule error bound.** If `F' = F1`, `F1' = F2` on `ℝ` and `|F2| ≤ M` on `[a, b]`,
then the midpoint rule approximates `∫ x in a..b, F x` up to `M * (b - a) ^ 3 / 24`. -/
theorem midpoint_abs_sub_le {F F1 F2 : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F1 x) x) (hF1 : ∀ x, HasDerivAt F1 (F2 x) x)
    {a b M : ℝ} (hab : a ≤ b) (hM : ∀ x ∈ Set.Icc a b, |F2 x| ≤ M) :
    |(∫ x in a..b, F x) - (b - a) * F ((a + b) / 2)| ≤ M * (b - a) ^ 3 / 24 := by
  have hm : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hFi : IntervalIntegrable F MeasureTheory.volume a b :=
    (continuous_iff_continuousAt.2 fun x => (hF x).continuousAt).intervalIntegrable a b
  have hq : ∀ c : ℝ, IntervalIntegrable (fun x => F ((a + b) / 2) +
      F1 ((a + b) / 2) * (x - (a + b) / 2) + c * (x - (a + b) / 2) ^ 2 / 2)
      MeasureTheory.volume a b := fun c => by
    apply Continuous.intervalIntegrable
    fun_prop
  have hupper : (∫ x in a..b, F x) ≤ (b - a) * F ((a + b) / 2) + M * (b - a) ^ 3 / 24 := by
    rw [← integral_taylor_quadratic_midpoint _ (F1 ((a + b) / 2))]
    exact integral_mono_on hab hFi (hq M)
      (le_taylor_quadratic hF hF1 hm fun x hx => (abs_le.1 (hM x hx)).2)
  have hlower : (b - a) * F ((a + b) / 2) + (-M) * (b - a) ^ 3 / 24 ≤ ∫ x in a..b, F x := by
    rw [← integral_taylor_quadratic_midpoint _ (F1 ((a + b) / 2))]
    exact integral_mono_on hab (hq (-M)) hFi
      (taylor_quadratic_le hF hF1 hm fun x hx => (abs_le.1 (hM x hx)).1)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **Midpoint rule upper bound.** If `F' = F1`, `F1' = F2` on `ℝ` and `|F2| ≤ M` on `[a, b]`,
then `∫ x in a..b, F x ≤ (b - a) * F ((a + b) / 2) + M * (b - a) ^ 3 / 24`. -/
theorem integral_le_midpoint_add {F F1 F2 : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F1 x) x) (hF1 : ∀ x, HasDerivAt F1 (F2 x) x)
    {a b M : ℝ} (hab : a ≤ b) (hM : ∀ x ∈ Set.Icc a b, |F2 x| ≤ M) :
    (∫ x in a..b, F x) ≤ (b - a) * F ((a + b) / 2) + M * (b - a) ^ 3 / 24 := by
  have h := midpoint_abs_sub_le hF hF1 hab hM
  have := le_abs_self ((∫ x in a..b, F x) - (b - a) * F ((a + b) / 2))
  linarith

end Fisher41
