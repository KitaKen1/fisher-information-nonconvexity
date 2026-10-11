/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Heat.Gaussian
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.HeatKernel.HeatEquation

/-!
# Differentiating the heat flow

For `t > 0` the heat flow `heat g t = g ⋆ γₜ` can be differentiated in space and in time. This
file provides the glue between Tau Ceti's results on the heat kernel (smoothing, and the heat
equation stated with Mathlib's Laplacian `Δ`) and the coordinate partial derivatives `pd` in
which `Fisher41.Defs` is phrased.

## Main results

* `Fisher41.heat_eq_integral_sub`: `heat g t x = ∫ g (x - y) γₜ(y) dy`.
* `Fisher41.hasFDerivAt_heat`, `Fisher41.pd_heat`: for `g` of class `C¹` with `g` and `Dg`
  bounded, spatial derivatives fall on `g`: `D (heat g t) x = ∫ γₜ(y) Dg(x - y) dy` and
  `∂ᵢ (heat g t) = heat (∂ᵢ g) t`.
* `Fisher41.contDiff_heat`: the heat flow of a measurable, essentially bounded function is smooth
  at every positive time.
* `Fisher41.laplacian_eq_sum_pd_pd`: Mathlib's Laplacian is `∑ᵢ ∂ᵢ∂ᵢ`.
* `Fisher41.hasDerivAt_heat_sum_pd`: the heat equation in coordinates,
  `∂ₜ heat g t x = ½ ∑ᵢ ∂ᵢ∂ᵢ (heat g t) x`.
* `Fisher41.hasDerivAt_pd_heat`: for `g` as in `pd_heat`, spatial derivatives of the heat flow
  solve the heat equation as well: `∂ₜ ∂ᵢ heat g t x = ½ ∑ₖ ∂ₖ∂ₖ ∂ᵢ (heat g t) x`.
-/

open MeasureTheory Real
open scoped Convolution ContDiff Laplacian Topology

noncomputable section

namespace Fisher41

/-- **Change of variables in the heat flow**: `heat g t x = ∫ g (x - y) γₜ(y) dy`. -/
theorem heat_eq_integral_sub {d : ℕ} (g : E d → ℝ) (t : ℝ) (x : E d) :
    heat g t x = ∫ y, g (x - y) * gaussian d t y := by
  have h := integral_sub_left_eq_self (fun y => g y * gaussian d t (x - y))
    (volume : Measure (E d)) x
  simp only [sub_sub_cancel] at h
  rw [heat]
  exact h.symm

namespace Commute

/-- A bounded, a.e.-strongly measurable function times the Gaussian is integrable. -/
theorem integrable_gaussian_smul {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E d → F} {C t : ℝ} (ht : 0 < t) (hφ : AEStronglyMeasurable φ)
    (hC : ∀ y, ‖φ y‖ ≤ C) : Integrable (fun y => gaussian d t y • φ y) := by
  refine ((integrable_gaussian ht).const_mul C).mono'
    ((continuous_gaussian d t).aestronglyMeasurable.smul hφ) (ae_of_all _ fun y => ?_)
  have hγ := gaussian_pos ht y
  calc ‖gaussian d t y • φ y‖ = ‖φ y‖ * gaussian d t y := by
        rw [norm_smul, Real.norm_of_nonneg hγ.le, mul_comm]
    _ ≤ C * gaussian d t y := mul_le_mul_of_nonneg_right (hC y) hγ.le

/-- A partial derivative of a `C¹` function is continuous. -/
theorem continuous_pd {d : ℕ} {g : E d → ℝ} (hg : ContDiff ℝ 1 g) (i : Fin d) :
    Continuous (pd g i) := by
  show Continuous fun x => fderiv ℝ g x (EuclideanSpace.single i 1)
  exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- A partial derivative is bounded by the operator norm of the derivative. -/
theorem norm_pd_le {d : ℕ} (g : E d → ℝ) (i : Fin d) (x : E d) :
    ‖pd g i x‖ ≤ ‖fderiv ℝ g x‖ := by
  simpa [pd] using (fderiv ℝ g x).le_opNorm (EuclideanSpace.single i (1 : ℝ))

end Commute

/-- **Spatial derivatives of the heat flow fall on the data.** If `g` is `C¹` with `g` and its
derivative bounded, then for `t > 0` the heat flow `heat g t` has derivative
`∫ γₜ(y) Dg(x - y) dy` at `x`. -/
theorem hasFDerivAt_heat {d : ℕ} {g : E d → ℝ} {M M' t : ℝ} (hg : ContDiff ℝ 1 g)
    (hgM : ∀ x, |g x| ≤ M) (hgM' : ∀ x, ‖fderiv ℝ g x‖ ≤ M') (ht : 0 < t) (x : E d) :
    HasFDerivAt (heat g t) (∫ y, gaussian d t y • fderiv ℝ g (x - y)) x := by
  have hγ : Integrable (gaussian d t) := integrable_gaussian ht
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hF_meas : ∀ x' : E d, AEStronglyMeasurable (fun y => g (x' - y) * gaussian d t y) :=
    fun x' => ((hgc.comp (continuous_sub_left x')).mul
      (continuous_gaussian d t)).aestronglyMeasurable
  have hF_int : Integrable (fun y => g (x - y) * gaussian d t y) := by
    refine (hγ.const_mul M).mono' (hF_meas x) (ae_of_all _ fun y => ?_)
    have hγy := gaussian_pos ht y
    calc ‖g (x - y) * gaussian d t y‖ = |g (x - y)| * gaussian d t y := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos hγy]
      _ ≤ M * gaussian d t y := mul_le_mul_of_nonneg_right (hgM _) hγy.le
  have hF'_meas : AEStronglyMeasurable (fun y => gaussian d t y • fderiv ℝ g (x - y)) :=
    ((continuous_gaussian d t).smul (hg'c.comp (continuous_sub_left x))).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂(volume : Measure (E d)), ∀ x' ∈ (Set.univ : Set (E d)),
      ‖gaussian d t y • fderiv ℝ g (x' - y)‖ ≤ M' * gaussian d t y := by
    refine ae_of_all _ fun y x' _ => ?_
    have hγy := gaussian_pos ht y
    calc ‖gaussian d t y • fderiv ℝ g (x' - y)‖ = ‖fderiv ℝ g (x' - y)‖ * gaussian d t y := by
          rw [norm_smul, Real.norm_of_nonneg hγy.le, mul_comm]
      _ ≤ M' * gaussian d t y := mul_le_mul_of_nonneg_right (hgM' _) hγy.le
  have h_diff : ∀ᵐ y ∂(volume : Measure (E d)), ∀ x' ∈ (Set.univ : Set (E d)),
      HasFDerivAt (fun x'' => g (x'' - y) * gaussian d t y)
        (gaussian d t y • fderiv ℝ g (x' - y)) x' := by
    refine ae_of_all _ fun y x' _ => ?_
    have h1 : HasFDerivAt (fun x'' => g (x'' - y)) (fderiv ℝ g (x' - y)) x' := by
      simpa [Function.comp_def] using
        (hgd (x' - y)).hasFDerivAt.comp x' ((hasFDerivAt_id x').sub_const y)
    exact h1.mul_const (gaussian d t y)
  rw [show heat g t = fun x' => ∫ y, g (x' - y) * gaussian d t y from
    funext (heat_eq_integral_sub g t)]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (x₀ := x)
    (F := fun x' y => g (x' - y) * gaussian d t y)
    (F' := fun x' y => gaussian d t y • fderiv ℝ g (x' - y))
    (bound := fun y => M' * gaussian d t y) Filter.univ_mem
    (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound (hγ.const_mul M') h_diff

/-- **Partial derivatives commute with the heat flow**: if `g` is `C¹` with `g` and its
derivative bounded, then `∂ᵢ (heat g t) = heat (∂ᵢ g) t` for `t > 0`. -/
theorem pd_heat {d : ℕ} {g : E d → ℝ} {M M' t : ℝ} (hg : ContDiff ℝ 1 g)
    (hgM : ∀ x, |g x| ≤ M) (hgM' : ∀ x, ‖fderiv ℝ g x‖ ≤ M') (ht : 0 < t) (i : Fin d)
    (x : E d) : pd (heat g t) i x = heat (pd g i) t x := by
  have hint : Integrable (fun y => gaussian d t y • fderiv ℝ g (x - y)) :=
    Commute.integrable_gaussian_smul ht
      ((hg.continuous_fderiv one_ne_zero).comp (continuous_sub_left x)).aestronglyMeasurable
      fun y => hgM' (x - y)
  rw [pd, (hasFDerivAt_heat hg hgM hgM' ht x).fderiv, ContinuousLinearMap.integral_apply hint,
    heat_eq_integral_sub]
  congr 1 with y
  simp only [_root_.smul_apply, smul_eq_mul, pd]
  ring

/-- **Smoothing by the heat flow**: the heat flow of a measurable, essentially bounded function
is smooth at every positive time. -/
theorem contDiff_heat {d : ℕ} {g : E d → ℝ} {M t : ℝ} (hg : AEStronglyMeasurable g)
    (hM : ∀ᵐ y, ‖g y‖ ≤ M) (ht : 0 < t) : ContDiff ℝ ∞ (heat g t) := by
  rw [show heat g t = TauCeti.heatKernel (t / 2) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g from
    funext (heat_eq_convolution g t)]
  exact TauCeti.contDiff_heatKernel_convolution (half_pos ht) hg hM

/-- **The Laplacian in coordinates**: if `fderiv ℝ h` is differentiable at `x`, then Mathlib's
Laplacian of `h` at `x` is the sum of the pure second partial derivatives `∑ᵢ ∂ᵢ∂ᵢ h x`. -/
theorem laplacian_eq_sum_pd_pd {d : ℕ} {h : E d → ℝ} {x : E d}
    (hh : DifferentiableAt ℝ (fderiv ℝ h) x) : Δ h x = ∑ i, pd (pd h i) i x := by
  rw [TauCeti.laplacian_eq_sum_fderiv_fderiv_apply (EuclideanSpace.basisFun (Fin d) ℝ) hh]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-- **The heat equation in coordinates**: for a measurable, essentially bounded `g` and `t > 0`,
`∂ₜ heat g t x = ½ ∑ᵢ ∂ᵢ∂ᵢ (heat g t) x`. -/
theorem hasDerivAt_heat_sum_pd {d : ℕ} {g : E d → ℝ} {M t : ℝ} (hg : AEStronglyMeasurable g)
    (hM : ∀ᵐ y, ‖g y‖ ≤ M) (ht : 0 < t) (x : E d) :
    HasDerivAt (fun s => heat g s x) ((1 / 2) * ∑ i, pd (pd (heat g t) i) i x) t := by
  have h2 : ContDiff ℝ 2 (heat g t) := contDiff_infty.1 (contDiff_heat hg hM ht) 2
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (heat g t)) x :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  rw [← laplacian_eq_sum_pd_pd hdiff]
  exact hasDerivAt_heat hg hM ht x

/-- **Spatial derivatives of the heat flow solve the heat equation**: if `g` is `C¹` with `g` and
its derivative bounded, then for `t > 0`,
`∂ₜ ∂ᵢ heat g t x = ½ ∑ₖ ∂ₖ∂ₖ ∂ᵢ (heat g t) x`. -/
theorem hasDerivAt_pd_heat {d : ℕ} {g : E d → ℝ} {M M' t : ℝ} (hg : ContDiff ℝ 1 g)
    (hgM : ∀ x, |g x| ≤ M) (hgM' : ∀ x, ‖fderiv ℝ g x‖ ≤ M') (ht : 0 < t) (i : Fin d)
    (x : E d) :
    HasDerivAt (fun s => pd (heat g s) i x)
      ((1 / 2) * ∑ k, pd (pd (pd (heat g t) i) k) k x) t := by
  have hpd : pd (heat g t) i = heat (pd g i) t :=
    funext fun y => pd_heat hg hgM hgM' ht i y
  have hbdd : ∀ᵐ y, ‖pd g i y‖ ≤ M' :=
    ae_of_all _ fun y => (Commute.norm_pd_le g i y).trans (hgM' y)
  rw [hpd]
  refine (hasDerivAt_heat_sum_pd (Commute.continuous_pd hg i).aestronglyMeasurable hbdd ht
    x).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  exact pd_heat hg hgM hgM' hs i x

end Fisher41
