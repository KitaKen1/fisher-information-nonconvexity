/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The radial tensor identity

For a radial density `ρ y = exp (U (‖y‖² / 2))` on `E d`, the kernel `kernelK ρ` only depends on
`s = ‖x‖² / 2` and on `U' s`, `U'' s`, `U''' s`:
`kernelK ρ x = Kd d s (-U' s) (U'' s) (U''' s)`.

Writing `w y = U (‖y‖² / 2)` and `δᵢⱼ = if i = j then 1 else 0`, we prove

* `Fisher41.pd_radial`: `∂ᵢ w = U'(s) xᵢ`;
* `Fisher41.pd_radial_mul_coord`: `∂ⱼ (U'(s) xᵢ) = U''(s) xᵢ xⱼ + U'(s) δᵢⱼ`;
* `Fisher41.pd_radial_hess`, `Fisher41.pd_pd_pd_radial`:
  `∂ₖ∂ⱼ∂ᵢ w = U'''(s) xᵢ xⱼ xₖ + U''(s) (δᵢⱼ xₖ + δᵢₖ xⱼ + δⱼₖ xᵢ)`;
* `Fisher41.kernelK_exp_radial`: the radial formula for `kernelK`.

The tensor contractions are carried out for a general dimension `d`, with Kronecker deltas
written as `if i = j then 1 else 0`: with `H = a Id - B x xᵀ` one has
`Σ (∂ₖHᵢⱼ)² = C²|x|⁶ + 6BC|x|⁴ + 3(d+2)B²|x|²` and
`Σ HᵢⱼHⱼₖHₖᵢ = (d-1)a³ + (a - B|x|²)³`
(`Fisher41.RadialTensor.sum_sq_third_radial`, `Fisher41.RadialTensor.sum_cube_hess_radial`).
Auxiliary lemmas live in the namespace `Fisher41.RadialTensor`.
-/

namespace Fisher41

variable {d : ℕ} {U U1 U2 U3 : ℝ → ℝ}

namespace RadialTensor

/-! ### Kronecker delta contractions -/

section Kronecker

variable (v : Fin d → ℝ)

/-- Contracting a Kronecker delta with a vector. -/
lemma sum_kron_mul (i : Fin d) : ∑ k, (if i = k then (1 : ℝ) else 0) * v k = v i := by
  simp

/-- Contracting a Kronecker delta with a vector (other orientation of the delta). -/
lemma sum_kron_mul' (i : Fin d) : ∑ k, (if k = i then (1 : ℝ) else 0) * v k = v i := by
  simp

/-- The squared Kronecker delta sums to one. -/
lemma sum_kron_sq (i : Fin d) : ∑ k, (if i = k then (1 : ℝ) else 0) ^ 2 = 1 := by
  simp

/-- `Σᵢⱼₖ (∂ₖHᵢⱼ)²` for the tensor `∂ₖHᵢⱼ = -(C vᵢvⱼvₖ + B (δᵢⱼvₖ + δᵢₖvⱼ + δⱼₖvᵢ))`. -/
lemma sum_sq_third_radial (B C : ℝ) :
    ∑ i, ∑ j, ∑ k, (-(C * v i * v j * v k + B * ((if i = j then (1 : ℝ) else 0) * v k +
        (if i = k then (1 : ℝ) else 0) * v j + (if j = k then (1 : ℝ) else 0) * v i))) ^ 2 =
      C ^ 2 * (∑ i, v i ^ 2) ^ 3 + 6 * B * C * (∑ i, v i ^ 2) ^ 2 +
        3 * ((d : ℝ) + 2) * B ^ 2 * ∑ i, v i ^ 2 := by
  have hk : ∀ i j, ∑ k, (-(C * v i * v j * v k + B * ((if i = j then (1 : ℝ) else 0) * v k +
        (if i = k then (1 : ℝ) else 0) * v j + (if j = k then (1 : ℝ) else 0) * v i))) ^ 2 =
      (C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) ^ 2 * (∑ k, v k ^ 2) + (B * v j) ^ 2 +
        (B * v i) ^ 2 + 2 * (C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) * (B * v j) * v i +
        2 * (C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) * (B * v i) * v j +
        2 * (B * v j) * (B * v i) * (if i = j then (1 : ℝ) else 0) := by
    intro i j
    trans ∑ k, ((C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) ^ 2 * v k ^ 2 +
        (B * v j) ^ 2 * (if i = k then (1 : ℝ) else 0) ^ 2 +
        (B * v i) ^ 2 * (if j = k then (1 : ℝ) else 0) ^ 2 +
        2 * (C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) * (B * v j) *
          ((if i = k then (1 : ℝ) else 0) * v k) +
        2 * (C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) * (B * v i) *
          ((if j = k then (1 : ℝ) else 0) * v k) +
        2 * (B * v j) * (B * v i) *
          ((if j = k then (1 : ℝ) else 0) * (if i = k then (1 : ℝ) else 0)))
    · exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_kron_sq, sum_kron_mul]
      ring
  have hj : ∀ i, ∑ j, ((C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) ^ 2 *
        (∑ k, v k ^ 2) + (B * v j) ^ 2 +
        (B * v i) ^ 2 + 2 * (C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) * (B * v j) * v i +
        2 * (C * v i * v j + B * (if i = j then (1 : ℝ) else 0)) * (B * v i) * v j +
        2 * (B * v j) * (B * v i) * (if i = j then (1 : ℝ) else 0)) =
      (C ^ 2 * (∑ k, v k ^ 2) ^ 2 + 6 * B * C * (∑ k, v k ^ 2) + ((d : ℝ) + 6) * B ^ 2) *
        v i ^ 2 + 2 * B ^ 2 * (∑ k, v k ^ 2) := by
    intro i
    trans ∑ j, ((C ^ 2 * v i ^ 2 * (∑ k, v k ^ 2) + B ^ 2 + 4 * B * C * v i ^ 2) * v j ^ 2 +
        B ^ 2 * (∑ k, v k ^ 2) * (if i = j then (1 : ℝ) else 0) ^ 2 +
        (2 * B * C * v i * (∑ k, v k ^ 2) + 6 * B ^ 2 * v i) *
          ((if i = j then (1 : ℝ) else 0) * v j) +
        B ^ 2 * v i ^ 2)
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_kron_sq, sum_kron_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
  simp only [hk]
  simp only [hj]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `Σᵢⱼₖ HᵢⱼHⱼₖHₖᵢ` for the matrix `Hᵢⱼ = -(B vᵢvⱼ + A δᵢⱼ)`. -/
lemma sum_cube_hess_radial (A B : ℝ) :
    ∑ i, ∑ j, ∑ k, (-(B * v i * v j + A * (if i = j then (1 : ℝ) else 0))) *
        (-(B * v j * v k + A * (if j = k then (1 : ℝ) else 0))) *
        (-(B * v k * v i + A * (if k = i then (1 : ℝ) else 0))) =
      -((d : ℝ) * A ^ 3 + 3 * A ^ 2 * B * (∑ i, v i ^ 2) + 3 * A * B ^ 2 * (∑ i, v i ^ 2) ^ 2 +
        B ^ 3 * (∑ i, v i ^ 2) ^ 3) := by
  have hk : ∀ i j, ∑ k, (-(B * v i * v j + A * (if i = j then (1 : ℝ) else 0))) *
        (-(B * v j * v k + A * (if j = k then (1 : ℝ) else 0))) *
        (-(B * v k * v i + A * (if k = i then (1 : ℝ) else 0))) =
      -(B * v i * v j + A * (if i = j then (1 : ℝ) else 0)) *
        ((B ^ 2 * (∑ k, v k ^ 2) + 2 * A * B) * v i * v j +
          A ^ 2 * (if j = i then (1 : ℝ) else 0)) := by
    intro i j
    trans ∑ k, (-(B * v i * v j + A * (if i = j then (1 : ℝ) else 0)) * B ^ 2 * v j * v i *
          v k ^ 2 +
        -(B * v i * v j + A * (if i = j then (1 : ℝ) else 0)) * A * B * v j *
          ((if k = i then (1 : ℝ) else 0) * v k) +
        -(B * v i * v j + A * (if i = j then (1 : ℝ) else 0)) * A * B * v i *
          ((if j = k then (1 : ℝ) else 0) * v k) +
        -(B * v i * v j + A * (if i = j then (1 : ℝ) else 0)) * A ^ 2 *
          ((if j = k then (1 : ℝ) else 0) * (if k = i then (1 : ℝ) else 0)))
    · exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_kron_mul, sum_kron_mul']
      ring
  have hj : ∀ i, ∑ j, -(B * v i * v j + A * (if i = j then (1 : ℝ) else 0)) *
        ((B ^ 2 * (∑ k, v k ^ 2) + 2 * A * B) * v i * v j +
          A ^ 2 * (if j = i then (1 : ℝ) else 0)) =
      -((B ^ 3 * (∑ k, v k ^ 2) ^ 2 + 3 * A * B ^ 2 * (∑ k, v k ^ 2) + 3 * A ^ 2 * B) *
        v i ^ 2 + A ^ 3) := by
    intro i
    trans ∑ j, (-(B * (B ^ 2 * (∑ k, v k ^ 2) + 2 * A * B) * v i ^ 2) * v j ^ 2 +
        -(A ^ 2 * B * v i) * ((if j = i then (1 : ℝ) else 0) * v j) +
        -(A * (B ^ 2 * (∑ k, v k ^ 2) + 2 * A * B) * v i) *
          ((if i = j then (1 : ℝ) else 0) * v j) +
        -(A ^ 3) * ((if i = j then (1 : ℝ) else 0) * (if j = i then (1 : ℝ) else 0)))
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_kron_mul, sum_kron_mul',
        ite_true]
      ring
  simp only [hk]
  simp only [hj]
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Kronecker

/-! ### Derivative helpers -/

section Derivatives

/-- The inner product with a standard basis vector picks out a coordinate. -/
lemma innerSL_single (x : E d) (i : Fin d) :
    innerSL ℝ x (EuclideanSpace.single i 1) = x i := by
  simp [EuclideanSpace.inner_single_right]

/-- The coordinate functional evaluated on a standard basis vector is a Kronecker delta. -/
lemma proj_single (i j : Fin d) :
    EuclideanSpace.proj (𝕜 := ℝ) i (EuclideanSpace.single j (1 : ℝ)) = if i = j then 1 else 0 := by
  simp

/-- The derivative of `s(y) = ‖y‖² / 2` is `⟪x, ·⟫`. -/
lemma hasFDerivAt_half_norm_sq (x : E d) :
    HasFDerivAt (fun y : E d => ‖y‖ ^ 2 / 2) (innerSL ℝ x) x := by
  have := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const (1 / 2 : ℝ)
  convert this using 1
  · ext y; ring
  · ext v; simp

/-- Chain rule for a radial function `U (‖y‖² / 2)`. -/
lemma hasFDerivAt_radial (hU : ∀ s, HasDerivAt U (U1 s) s) (x : E d) :
    HasFDerivAt (fun y : E d => U (‖y‖ ^ 2 / 2)) (U1 (‖x‖ ^ 2 / 2) • innerSL ℝ x) x :=
  (hU _).comp_hasFDerivAt x (hasFDerivAt_half_norm_sq x)

/-- The derivative of a coordinate function. -/
lemma hasFDerivAt_coord (x : E d) (i : Fin d) :
    HasFDerivAt (fun y : E d => y i) (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt

/-- Partial derivatives commute with negation. -/
lemma pd_neg (g : E d → ℝ) (i : Fin d) (x : E d) : pd (fun y => -g y) i x = -pd g i x := by
  simp [pd]

end Derivatives

end RadialTensor

open RadialTensor

/-! ### Derivatives of radial functions -/

section Derivatives

/-- First derivative of a radial function: `∂ᵢ U(‖x‖²/2) = U'(‖x‖²/2) xᵢ`. -/
theorem pd_radial (hU : ∀ s, HasDerivAt U (U1 s) s) (x : E d) (i : Fin d) :
    pd (fun y : E d => U (‖y‖ ^ 2 / 2)) i x = U1 (‖x‖ ^ 2 / 2) * x i := by
  rw [pd, (hasFDerivAt_radial hU x).fderiv, smul_apply, innerSL_single, smul_eq_mul]

/-- Second derivative of a radial function, written as the derivative of `U'(s) xᵢ`:
`∂ⱼ (U'(‖x‖²/2) xᵢ) = U''(‖x‖²/2) xᵢ xⱼ + U'(‖x‖²/2) δᵢⱼ`. -/
theorem pd_radial_mul_coord (hU1 : ∀ s, HasDerivAt U1 (U2 s) s) (x : E d) (i j : Fin d) :
    pd (fun y : E d => U1 (‖y‖ ^ 2 / 2) * y i) j x =
      U2 (‖x‖ ^ 2 / 2) * x i * x j + U1 (‖x‖ ^ 2 / 2) * (if i = j then 1 else 0) := by
  have h : HasFDerivAt (fun y : E d => U1 (‖y‖ ^ 2 / 2) * y i) _ x :=
    (hasFDerivAt_radial hU1 x).mul (hasFDerivAt_coord x i)
  rw [pd, h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_single, proj_single]
  ring

/-- Second derivative of a radial function:
`∂ⱼ∂ᵢ U(‖x‖²/2) = U''(‖x‖²/2) xᵢ xⱼ + U'(‖x‖²/2) δᵢⱼ`. -/
theorem pd_pd_radial (hU : ∀ s, HasDerivAt U (U1 s) s) (hU1 : ∀ s, HasDerivAt U1 (U2 s) s)
    (x : E d) (i j : Fin d) :
    pd (pd (fun y : E d => U (‖y‖ ^ 2 / 2)) i) j x =
      U2 (‖x‖ ^ 2 / 2) * x i * x j + U1 (‖x‖ ^ 2 / 2) * (if i = j then 1 else 0) := by
  have h : pd (fun y : E d => U (‖y‖ ^ 2 / 2)) i = fun y => U1 (‖y‖ ^ 2 / 2) * y i :=
    funext fun y => pd_radial hU y i
  rw [h, pd_radial_mul_coord hU1]

/-- Third derivative of a radial function, written as the derivative of the Hessian entry
`U''(s) xᵢ xⱼ + U'(s) δᵢⱼ`:
`∂ₖ (U''(s) xᵢ xⱼ + U'(s) δᵢⱼ) = U'''(s) xᵢ xⱼ xₖ + U''(s) (δᵢⱼ xₖ + δᵢₖ xⱼ + δⱼₖ xᵢ)`. -/
theorem pd_radial_hess (hU1 : ∀ s, HasDerivAt U1 (U2 s) s) (hU2 : ∀ s, HasDerivAt U2 (U3 s) s)
    (x : E d) (i j k : Fin d) :
    pd (fun y : E d => U2 (‖y‖ ^ 2 / 2) * y i * y j +
        U1 (‖y‖ ^ 2 / 2) * (if i = j then 1 else 0)) k x =
      U3 (‖x‖ ^ 2 / 2) * x i * x j * x k + U2 (‖x‖ ^ 2 / 2) *
        ((if i = j then 1 else 0) * x k + (if i = k then 1 else 0) * x j +
          (if j = k then 1 else 0) * x i) := by
  have h : HasFDerivAt (fun y : E d => U2 (‖y‖ ^ 2 / 2) * y i * y j +
      U1 (‖y‖ ^ 2 / 2) * (if i = j then 1 else 0)) _ x :=
    (((hasFDerivAt_radial hU2 x).mul (hasFDerivAt_coord x i)).mul (hasFDerivAt_coord x j)).add
      ((hasFDerivAt_radial hU1 x).mul_const (if i = j then (1 : ℝ) else 0))
  rw [pd, h.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_single, proj_single, Pi.mul_apply]
  ring

/-- Third derivative of a radial function:
`∂ₖ∂ⱼ∂ᵢ U(‖x‖²/2) = U'''(s) xᵢ xⱼ xₖ + U''(s) (δᵢⱼ xₖ + δᵢₖ xⱼ + δⱼₖ xᵢ)`, `s = ‖x‖²/2`. -/
theorem pd_pd_pd_radial (hU : ∀ s, HasDerivAt U (U1 s) s) (hU1 : ∀ s, HasDerivAt U1 (U2 s) s)
    (hU2 : ∀ s, HasDerivAt U2 (U3 s) s) (x : E d) (i j k : Fin d) :
    pd (pd (pd (fun y : E d => U (‖y‖ ^ 2 / 2)) i) j) k x =
      U3 (‖x‖ ^ 2 / 2) * x i * x j * x k + U2 (‖x‖ ^ 2 / 2) *
        ((if i = j then 1 else 0) * x k + (if i = k then 1 else 0) * x j +
          (if j = k then 1 else 0) * x i) := by
  have h : pd (pd (fun y : E d => U (‖y‖ ^ 2 / 2)) i) j = fun y =>
      U2 (‖y‖ ^ 2 / 2) * y i * y j + U1 (‖y‖ ^ 2 / 2) * (if i = j then 1 else 0) :=
    funext fun y => pd_pd_radial hU hU1 y i j
  rw [h, pd_radial_hess hU1 hU2]

end Derivatives

/-! ### The radial kernel -/

/-- **Radial tensor identity.** For `ρ y = exp (U (‖y‖² / 2))`, the kernel
`K_ρ = Σ (∂ₖHᵢⱼ)² + 2 Σ HᵢⱼHⱼₖHₖᵢ` at `x` equals `Kd d s (-U' s) (U'' s) (U''' s)` with
`s = ‖x‖² / 2`. -/
theorem kernelK_exp_radial (hU : ∀ s, HasDerivAt U (U1 s) s)
    (hU1 : ∀ s, HasDerivAt U1 (U2 s) s) (hU2 : ∀ s, HasDerivAt U2 (U3 s) s) (x : E d) :
    kernelK (fun y : E d => Real.exp (U (‖y‖ ^ 2 / 2))) x =
      Kd d (‖x‖ ^ 2 / 2) (-U1 (‖x‖ ^ 2 / 2)) (U2 (‖x‖ ^ 2 / 2)) (U3 (‖x‖ ^ 2 / 2)) := by
  have hH : ∀ i j, negHess (fun y : E d => Real.exp (U (‖y‖ ^ 2 / 2))) i j = fun y =>
      -(U2 (‖y‖ ^ 2 / 2) * y i * y j + U1 (‖y‖ ^ 2 / 2) * (if i = j then 1 else 0)) := by
    intro i j
    funext y
    simp only [negHess, Real.log_exp]
    rw [pd_pd_radial hU hU1]
  have hH' : ∀ i j, negHess (fun y : E d => Real.exp (U (‖y‖ ^ 2 / 2))) i j x =
      -(U2 (‖x‖ ^ 2 / 2) * x i * x j + U1 (‖x‖ ^ 2 / 2) * (if i = j then 1 else 0)) := by
    intro i j
    rw [hH i j]
  have hdH : ∀ i j k, pd (negHess (fun y : E d => Real.exp (U (‖y‖ ^ 2 / 2))) i j) k x =
      -(U3 (‖x‖ ^ 2 / 2) * x i * x j * x k + U2 (‖x‖ ^ 2 / 2) *
        ((if i = j then 1 else 0) * x k + (if i = k then 1 else 0) * x j +
          (if j = k then 1 else 0) * x i)) := by
    intro i j k
    rw [hH i j, pd_neg, pd_radial_hess hU1 hU2]
  simp only [kernelK, hdH, hH']
  rw [sum_sq_third_radial, sum_cube_hess_radial, ← EuclideanSpace.real_norm_sq_eq x]
  simp only [Kd]
  ring

end Fisher41
