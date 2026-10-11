/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Pointwise algebra behind the Fisher-information identities

Along the heat flow `∂ₜρ = ½Δρ`, write `v = log ρ`, `w = ∇v`, `A = ∇²v`, `T = ∇³v`,
`Q = ∇⁴v`. Then

* `∂ₜv = (Δv + |w|²)/2`,
* `∂ₜwᵢ = (Σₖ Tᵢₖₖ + 2 Σₖ wₖAₖᵢ)/2`,
* `∂ₜAᵢⱼ = (Σₖ Qᵢⱼₖₖ + 2 Σₖ (AᵢₖAⱼₖ + wₖTᵢⱼₖ))/2`.

The identities `I' = -∫ρ|A|²` and `(∫ρ|A|²)' = -∫ρ(|∇A|² - 2 tr A³)` follow from two
pointwise divergence identities. This file proves their purely algebraic cores, for an
arbitrary dimension `d` and arbitrary real data `ρ, w, A, T, Q`:

* `Fisher41.p1_core`: the core of `∂ₜ(ρ|w|²) = div(…) - ρ|A|²`;
* `Fisher41.p2_core`: the core of `∂ₜ(ρ|A|²) = div(…) - ρ(|T|² - 2 tr A³)`.

In each statement the left-hand side is `(∂ₜρ)·F + ρ·∂ₜF` with `∂ₜρ = ρ·∂ₜv`, and the big
sum on the right-hand side is the divergence `Σₖ ∂ₖ(ρ·Jₖ)` written out with the chain rule
`∂ₖρ = ρ wₖ`.

Only some of the symmetries of the derivative tensors are actually needed: `p1_core` uses
the symmetry of `A` and the symmetry of `T` in its first two slots, and `p2_core` uses only
the symmetry of `A`. The sharper forms are recorded as `Fisher41.p1_core_of_symm` and
`Fisher41.p2_core_of_symm`; the statements `p1_core`, `p2_core` carry all symmetries of
the derivative tensors for a uniform interface.

## Proof strategy

Each side is expanded into a linear combination of a few "atomic" sums (such as
`Σᵢ wᵢ Σₖ Tᵢₖₖ`), the atomic sums appearing on the two sides are identified using
`Finset.sum_comm`, `Finset.sum_comm_cycle` and the symmetry hypotheses, and the resulting
polynomial identity in the atoms is closed by `linear_combination`.
-/

open Finset

namespace Fisher41

/-- Algebraic core of `I' = -∫ρ|A|²`, assuming only the symmetry of `A` and the symmetry of
`T` in its first two slots. -/
theorem p1_core_of_symm {d : ℕ} (ρ : ℝ) (w : Fin d → ℝ) (A : Fin d → Fin d → ℝ)
    (T : Fin d → Fin d → Fin d → ℝ)
    (hA : ∀ i j, A i j = A j i) (hT₁ : ∀ i j k, T i j k = T j i k) :
    ρ * (((∑ k, A k k) + ∑ k, w k ^ 2) / 2) * (∑ k, w k ^ 2)
      + 2 * ρ * ∑ i, w i * (((∑ k, T i k k) + 2 * ∑ k, w k * A k i) / 2)
    = (∑ i, (ρ * w i * ((∑ k, w k ^ 2) * w i / 2 + ∑ j, A i j * w j)
        + ρ * ((∑ k, w k * A k i) * w i + (∑ k, w k ^ 2) * A i i / 2
              + ∑ j, (T i j i * w j + A i j * A j i))))
      - ρ * ∑ i, ∑ j, A i j ^ 2 := by
  -- Expansion of the sum on the left-hand side.
  have e1 : ∑ i, w i * (((∑ k, T i k k) + 2 * ∑ k, w k * A k i) / 2)
      = (∑ i, w i * ∑ k, T i k k) / 2 + ∑ i, w i * ∑ k, w k * A k i := by
    rw [sum_div, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  -- Expansion of the sum on the right-hand side.
  have e2 : ∑ i, (ρ * w i * ((∑ k, w k ^ 2) * w i / 2 + ∑ j, A i j * w j)
        + ρ * ((∑ k, w k * A k i) * w i + (∑ k, w k ^ 2) * A i i / 2
              + ∑ j, (T i j i * w j + A i j * A j i)))
      = ρ * (∑ k, w k ^ 2) / 2 * ∑ i, w i ^ 2 + ρ * ∑ i, w i * ∑ j, A i j * w j
        + ρ * ∑ i, (∑ k, w k * A k i) * w i + ρ * (∑ k, w k ^ 2) / 2 * ∑ i, A i i
        + ρ * ∑ i, ∑ j, T i j i * w j + ρ * ∑ i, ∑ j, A i j * A j i := by
    have h : ∀ i, ρ * w i * ((∑ k, w k ^ 2) * w i / 2 + ∑ j, A i j * w j)
          + ρ * ((∑ k, w k * A k i) * w i + (∑ k, w k ^ 2) * A i i / 2
              + ∑ j, (T i j i * w j + A i j * A j i))
        = ρ * (∑ k, w k ^ 2) / 2 * w i ^ 2 + ρ * (w i * ∑ j, A i j * w j)
          + ρ * ((∑ k, w k * A k i) * w i) + ρ * (∑ k, w k ^ 2) / 2 * A i i
          + ρ * ∑ j, T i j i * w j + ρ * ∑ j, A i j * A j i := by
      intro i
      simp only [sum_add_distrib]
      ring
    simp only [h]
    simp only [sum_add_distrib, ← mul_sum]
  -- Identification of the atomic sums.
  have r1 : ∑ i, w i * ∑ j, A i j * w j = ∑ i, w i * ∑ k, w k * A k i :=
    sum_congr rfl fun i _ => by
      congr 1
      exact sum_congr rfl fun j _ => by rw [hA i j]; ring
  have r2 : ∑ i, (∑ k, w k * A k i) * w i = ∑ i, w i * ∑ k, w k * A k i :=
    sum_congr rfl fun i _ => mul_comm _ _
  have r3 : ∑ i, ∑ j, T i j i * w j = ∑ i, w i * ∑ k, T i k k := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by rw [hT₁ i j i]; ring
  have r4 : ∑ i, ∑ j, A i j * A j i = ∑ i, ∑ j, A i j ^ 2 :=
    sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hA j i]; ring
  linear_combination (2 * ρ) * e1 - e2 - ρ * r1 - ρ * r2 - ρ * r3 - ρ * r4

-- The hypothesis `hT₂` is not needed (see `p1_core_of_symm`); it is kept so that the
-- statement lists all symmetries of the derivative tensors.
set_option linter.unusedVariables false in
/-- **Pointwise core of `I' = -∫ρ|A|²`.** With `v = log ρ`, `w = ∇v`, `A = ∇²v`,
`T = ∇³v`, the left-hand side is `∂ₜ(ρ|w|²) = (∂ₜρ)|w|² + 2ρ⟨w, ∂ₜw⟩` along the heat flow,
the big sum is the divergence of `ρ(|w|²w/2 + Aw)`, and the remainder is `-ρ|A|²`. -/
theorem p1_core {d : ℕ} (ρ : ℝ) (w : Fin d → ℝ) (A : Fin d → Fin d → ℝ)
    (T : Fin d → Fin d → Fin d → ℝ)
    (hA : ∀ i j, A i j = A j i) (hT₁ : ∀ i j k, T i j k = T j i k)
    (hT₂ : ∀ i j k, T i j k = T i k j) :
    ρ * (((∑ k, A k k) + ∑ k, w k ^ 2) / 2) * (∑ k, w k ^ 2)
      + 2 * ρ * ∑ i, w i * (((∑ k, T i k k) + 2 * ∑ k, w k * A k i) / 2)
    = (∑ i, (ρ * w i * ((∑ k, w k ^ 2) * w i / 2 + ∑ j, A i j * w j)
        + ρ * ((∑ k, w k * A k i) * w i + (∑ k, w k ^ 2) * A i i / 2
              + ∑ j, (T i j i * w j + A i j * A j i))))
      - ρ * ∑ i, ∑ j, A i j ^ 2 :=
  p1_core_of_symm ρ w A T hA hT₁

/-- Algebraic core of `(∫ρ|A|²)' = -∫ρ(|∇A|² - 2 tr A³)`, assuming only the symmetry
of `A`. -/
theorem p2_core_of_symm {d : ℕ} (ρ : ℝ) (w : Fin d → ℝ) (A : Fin d → Fin d → ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (Q : Fin d → Fin d → Fin d → Fin d → ℝ)
    (hA : ∀ i j, A i j = A j i) :
    ρ * (((∑ k, A k k) + ∑ k, w k ^ 2) / 2) * (∑ i, ∑ j, A i j ^ 2)
      + 2 * ρ * ∑ i, ∑ j, A i j *
          (((∑ k, Q i j k k) + 2 * ∑ k, (A i k * A j k + w k * T i j k)) / 2)
    = (∑ k, (ρ * w k * ((∑ i, ∑ j, A i j ^ 2) * w k / 2 + ∑ i, ∑ j, A i j * T i j k)
        + ρ * ((∑ i, ∑ j, A i j * T i j k) * w k + (∑ i, ∑ j, A i j ^ 2) * A k k / 2
              + ∑ i, ∑ j, (T i j k ^ 2 + A i j * Q i j k k))))
      - ρ * ((∑ i, ∑ j, ∑ k, T i j k ^ 2) - 2 * ∑ i, ∑ j, ∑ k, A i j * A j k * A k i) := by
  -- Expansion of the sum on the left-hand side.
  have e1 : ∑ i, ∑ j, A i j *
          (((∑ k, Q i j k k) + 2 * ∑ k, (A i k * A j k + w k * T i j k)) / 2)
      = (∑ i, ∑ j, A i j * ∑ k, Q i j k k) / 2 + ∑ i, ∑ j, A i j * ∑ k, A i k * A j k
        + ∑ i, ∑ j, A i j * ∑ k, w k * T i j k := by
    have h : ∀ i j, A i j *
          (((∑ k, Q i j k k) + 2 * ∑ k, (A i k * A j k + w k * T i j k)) / 2)
        = A i j * (∑ k, Q i j k k) / 2 + A i j * (∑ k, A i k * A j k)
          + A i j * ∑ k, w k * T i j k := by
      intro i j
      rw [sum_add_distrib]
      ring
    simp only [h]
    simp only [sum_add_distrib, ← sum_div]
  -- Expansion of the sum on the right-hand side.
  have e2 : ∑ k, (ρ * w k * ((∑ i, ∑ j, A i j ^ 2) * w k / 2 + ∑ i, ∑ j, A i j * T i j k)
        + ρ * ((∑ i, ∑ j, A i j * T i j k) * w k + (∑ i, ∑ j, A i j ^ 2) * A k k / 2
              + ∑ i, ∑ j, (T i j k ^ 2 + A i j * Q i j k k)))
      = ρ * (∑ i, ∑ j, A i j ^ 2) / 2 * ∑ k, w k ^ 2
        + ρ * ∑ k, w k * ∑ i, ∑ j, A i j * T i j k
        + ρ * ∑ k, (∑ i, ∑ j, A i j * T i j k) * w k
        + ρ * (∑ i, ∑ j, A i j ^ 2) / 2 * ∑ k, A k k
        + ρ * ∑ k, ∑ i, ∑ j, T i j k ^ 2
        + ρ * ∑ k, ∑ i, ∑ j, A i j * Q i j k k := by
    have h : ∀ k, ρ * w k * ((∑ i, ∑ j, A i j ^ 2) * w k / 2 + ∑ i, ∑ j, A i j * T i j k)
          + ρ * ((∑ i, ∑ j, A i j * T i j k) * w k + (∑ i, ∑ j, A i j ^ 2) * A k k / 2
              + ∑ i, ∑ j, (T i j k ^ 2 + A i j * Q i j k k))
        = ρ * (∑ i, ∑ j, A i j ^ 2) / 2 * w k ^ 2
          + ρ * (w k * ∑ i, ∑ j, A i j * T i j k)
          + ρ * ((∑ i, ∑ j, A i j * T i j k) * w k)
          + ρ * (∑ i, ∑ j, A i j ^ 2) / 2 * A k k
          + ρ * ∑ i, ∑ j, T i j k ^ 2
          + ρ * ∑ i, ∑ j, A i j * Q i j k k := by
      intro k
      simp only [sum_add_distrib]
      ring
    simp only [h]
    simp only [sum_add_distrib, ← mul_sum]
  -- Identification of the atomic sums.
  have r1 : ∑ k, w k * ∑ i, ∑ j, A i j * T i j k = ∑ i, ∑ j, A i j * ∑ k, w k * T i j k := by
    simp only [mul_sum]
    rw [eq_comm, sum_comm_cycle]
    exact sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have r1' : ∑ k, (∑ i, ∑ j, A i j * T i j k) * w k = ∑ k, w k * ∑ i, ∑ j, A i j * T i j k :=
    sum_congr rfl fun k _ => mul_comm _ _
  have r2 : ∑ k, ∑ i, ∑ j, T i j k ^ 2 = ∑ i, ∑ j, ∑ k, T i j k ^ 2 :=
    sum_comm_cycle.symm
  have r3 : ∑ k, ∑ i, ∑ j, A i j * Q i j k k = ∑ i, ∑ j, A i j * ∑ k, Q i j k k := by
    simp only [mul_sum]
    exact sum_comm_cycle.symm
  have r4 : ∑ i, ∑ j, A i j * ∑ k, A i k * A j k = ∑ i, ∑ j, ∑ k, A i j * A j k * A k i := by
    simp only [mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => by
      rw [hA k i]; ring
  linear_combination (2 * ρ) * e1 - e2 - ρ * r1' - (2 * ρ) * r1 - ρ * r2 - ρ * r3
    + (2 * ρ) * r4

-- Only `hA` is needed (see `p2_core_of_symm`); the other hypotheses are kept so that the
-- statement lists all symmetries of the derivative tensors.
set_option linter.unusedVariables false in
/-- **Pointwise core of `(∫ρ|A|²)' = -∫ρ(|∇A|² - 2 tr A³)`.** With `v = log ρ`, `w = ∇v`,
`A = ∇²v`, `T = ∇³v`, `Q = ∇⁴v`, the left-hand side is
`∂ₜ(ρ|A|²) = (∂ₜρ)|A|² + 2ρ⟨A, ∂ₜA⟩` along the heat flow, the big sum is the divergence of
`ρ(|A|²w/2 + ⟨A, T⟩)` (with `⟨A, T⟩ₖ = Σᵢⱼ AᵢⱼTᵢⱼₖ`), and the remainder is
`-ρ(|T|² - 2 tr A³)`. -/
theorem p2_core {d : ℕ} (ρ : ℝ) (w : Fin d → ℝ) (A : Fin d → Fin d → ℝ)
    (T : Fin d → Fin d → Fin d → ℝ) (Q : Fin d → Fin d → Fin d → Fin d → ℝ)
    (hA : ∀ i j, A i j = A j i) (hT₁ : ∀ i j k, T i j k = T j i k)
    (hT₂ : ∀ i j k, T i j k = T i k j)
    (hQ₁ : ∀ i j k l, Q i j k l = Q j i k l) (hQ₂ : ∀ i j k l, Q i j k l = Q i k j l)
    (hQ₃ : ∀ i j k l, Q i j k l = Q i j l k) :
    ρ * (((∑ k, A k k) + ∑ k, w k ^ 2) / 2) * (∑ i, ∑ j, A i j ^ 2)
      + 2 * ρ * ∑ i, ∑ j, A i j *
          (((∑ k, Q i j k k) + 2 * ∑ k, (A i k * A j k + w k * T i j k)) / 2)
    = (∑ k, (ρ * w k * ((∑ i, ∑ j, A i j ^ 2) * w k / 2 + ∑ i, ∑ j, A i j * T i j k)
        + ρ * ((∑ i, ∑ j, A i j * T i j k) * w k + (∑ i, ∑ j, A i j ^ 2) * A k k / 2
              + ∑ i, ∑ j, (T i j k ^ 2 + A i j * Q i j k k))))
      - ρ * ((∑ i, ∑ j, ∑ k, T i j k ^ 2) - 2 * ∑ i, ∑ j, ∑ k, A i j * A j k * A k i) :=
  p2_core_of_symm ρ w A T Q hA

end Fisher41
