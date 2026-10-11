/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.FC.Statement
import Fisher41.Defs

/-!
# The Formal Conjectures definitions and the project's definitions

The statement's heat flow and negative log-Hessian are the project's `Fisher41.heat` and
`Fisher41.negHess` by definition. Its Fisher information agrees with `Fisher41.fisher` because
`‖L‖² = ∑ᵢ (L eᵢ)²` for a linear functional `L` on Euclidean space, and the integrands of
`𝒬` and `𝒟` are `f ∑ H²` and `f K_f`.
-/

open MeasureTheory Real

namespace Arxiv.«2605.18081»

/-- The squared norm of a linear functional on Euclidean space is the sum of the squares of its
values on the standard basis. -/
theorem norm_sq_eq_sum {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ i, (L (EuclideanSpace.single i 1)) ^ 2 := by
  set v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm L with hv
  have hL : ‖L‖ = ‖v‖ := by rw [hv, LinearIsometryEquiv.norm_map]
  have hcoord : ∀ i, L (EuclideanSpace.single i 1) = v i := by
    intro i
    rw [← InnerProductSpace.toDual_symm_apply, ← hv, EuclideanSpace.inner_single_right]
    simp
  rw [hL, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp [hcoord, Real.norm_eq_abs, sq_abs]

/-- The heat flow of the statement is the project's heat flow. -/
theorem heatFlow_eq {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ) :
    heatFlow f t = Fisher41.heat f t := rfl

/-- The Fisher information integrand of the statement is the project's integrand. -/
theorem fisherIntegrand_eq {d : ℕ} (ρ : EuclideanSpace ℝ (Fin d) → ℝ) :
    (fun x => ‖fderiv ℝ (fun y => log (ρ y)) x‖ ^ 2 * ρ x) = Fisher41.fisherDensity ρ := by
  funext x
  rw [norm_sq_eq_sum, mul_comm]
  rfl

/-- The Fisher information of the statement is the project's Fisher information. -/
theorem fisherInformation_eq {d : ℕ} (ρ : EuclideanSpace ℝ (Fin d) → ℝ) :
    fisherInformation ρ = Fisher41.fisher ρ := by
  unfold fisherInformation Fisher41.fisher
  rw [fisherIntegrand_eq]

/-- The negative log-Hessian of the statement is the project's `negHess`. -/
theorem negLogHess_eq {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    negLogHess f = Fisher41.negHess f := rfl

/-- The integrand of `𝒬` is `f ∑ H²`. -/
theorem qIntegrand_eq {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    (fun x => (∑ i, ∑ j, negLogHess f i j x ^ 2) * f x) =
      fun x => f x * ∑ i, ∑ j, Fisher41.negHess f i j x ^ 2 := by
  funext x
  rw [mul_comm]
  rfl

/-- The integrand of `𝒟` is `f K_f`. -/
theorem dIntegrand_eq {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    (fun x => ((∑ i, ∑ j, ∑ k,
        fderiv ℝ (negLogHess f i j) x (EuclideanSpace.single k 1) ^ 2) +
      2 * ∑ i, ∑ j, ∑ k, negLogHess f i j x * negLogHess f j k x * negLogHess f k i x) * f x) =
      fun x => f x * Fisher41.kernelK f x := by
  funext x
  rw [mul_comm]
  rfl

end Arxiv.«2605.18081»
