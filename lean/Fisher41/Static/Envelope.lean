/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Gaussian envelope only shifts the log-Hessian

Let `q : E d → ℝ` be smooth and positive, `c > 0`, `R > 0`, and consider the enveloped density
`f y = c * q y * gaussian d (R ^ 2) y`. Since
`log f = log c + log q - (d / 2) log (2πR²) - ‖y‖² / (2R²)`,
the envelope only adds a quadratic polynomial to `log q`, and its effect on the quantities
entering `fisherDensity` and `kernelK` is explicit. Writing `H = negHess q`:

* `Fisher41.pd_log_mul_gaussian`: `∂ᵢ log f = ∂ᵢ log q - xᵢ / R²`;
* `Fisher41.negHess_mul_gaussian`: `negHess f = H + R⁻² Id`;
* `Fisher41.pd_negHess_mul_gaussian`: the third derivatives `∂ₖ (negHess f)ᵢⱼ` are those of `q`;
* `Fisher41.negHess_symm`: `H` is symmetric (Schwarz);
* `Fisher41.kernelK_mul_gaussian`:
  `K_f = K_q + 6 R⁻² Σᵢⱼ Hᵢⱼ² + 6 R⁻⁴ Σᵢ Hᵢᵢ + 2 d R⁻⁶`;
* `Fisher41.fisherDensity_mul_gaussian`, `Fisher41.abs_fisherDensity_mul_gaussian_le`:
  the Fisher integrand of `f` and a pointwise bound for it.

All results assume `hq : ContDiff ℝ ∞ q`, `hpos : ∀ x, 0 < q x`, `hc : 0 < c`, `hR : 0 < R`
(only the first two for `negHess_symm`), and are stated for the explicit function
`fun y => c * q y * gaussian d (R ^ 2) y`. Auxiliary lemmas live in the namespace
`Fisher41.Envelope`.
-/

open Real
open scoped ContDiff

namespace Fisher41

variable {d : ℕ} {q : E d → ℝ} {c R : ℝ}

namespace Envelope

/-! ### Kronecker delta contractions -/

section Kronecker

/-- Contracting a Kronecker delta with a vector. -/
lemma sum_kron_mul (v : Fin d → ℝ) (i : Fin d) :
    ∑ k, (if i = k then (1 : ℝ) else 0) * v k = v i := by
  simp

/-- Contracting a Kronecker delta with a vector (other orientation of the delta). -/
lemma sum_kron_mul' (v : Fin d → ℝ) (i : Fin d) :
    ∑ k, (if k = i then (1 : ℝ) else 0) * v k = v i := by
  simp

/-- The cubic trace of a shifted symmetric matrix: for `H` symmetric,
`Σᵢⱼₖ (H + ε Id)ᵢⱼ (H + ε Id)ⱼₖ (H + ε Id)ₖᵢ = Σᵢⱼₖ HᵢⱼHⱼₖHₖᵢ + 3ε Σᵢⱼ Hᵢⱼ² + 3ε² Σᵢ Hᵢᵢ + dε³`,
i.e. `tr (H + ε)³ = tr H³ + 3ε tr H² + 3ε² tr H + dε³`. -/
lemma sum_cube_add_smul_kron (H : Fin d → Fin d → ℝ) (hH : ∀ i j, H i j = H j i) (ε : ℝ) :
    ∑ i, ∑ j, ∑ k, (H i j + ε * (if i = j then (1 : ℝ) else 0)) *
        (H j k + ε * (if j = k then (1 : ℝ) else 0)) *
        (H k i + ε * (if k = i then (1 : ℝ) else 0)) =
      ∑ i, ∑ j, ∑ k, H i j * H j k * H k i + 3 * ε * ∑ i, ∑ j, H i j ^ 2 +
        3 * ε ^ 2 * ∑ i, H i i + (d : ℝ) * ε ^ 3 := by
  have hk : ∀ i j, ∑ k, (H i j + ε * (if i = j then (1 : ℝ) else 0)) *
        (H j k + ε * (if j = k then (1 : ℝ) else 0)) *
        (H k i + ε * (if k = i then (1 : ℝ) else 0)) =
      (H i j + ε * (if i = j then (1 : ℝ) else 0)) *
        (∑ k, H j k * H k i + 2 * ε * H j i + ε ^ 2 * (if j = i then (1 : ℝ) else 0)) := by
    intro i j
    trans ∑ k, ((H i j + ε * (if i = j then (1 : ℝ) else 0)) * (H j k * H k i) +
        (H i j + ε * (if i = j then (1 : ℝ) else 0)) * ε *
          ((if j = k then (1 : ℝ) else 0) * H k i) +
        (H i j + ε * (if i = j then (1 : ℝ) else 0)) * ε *
          ((if k = i then (1 : ℝ) else 0) * H j k) +
        (H i j + ε * (if i = j then (1 : ℝ) else 0)) * ε ^ 2 *
          ((if j = k then (1 : ℝ) else 0) * (if k = i then (1 : ℝ) else 0)))
    · exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_kron_mul, sum_kron_mul']
      ring
  have hj : ∀ i, ∑ j, (H i j + ε * (if i = j then (1 : ℝ) else 0)) *
        (∑ k, H j k * H k i + 2 * ε * H j i + ε ^ 2 * (if j = i then (1 : ℝ) else 0)) =
      ∑ j, H i j * ∑ k, H j k * H k i + ε * ∑ k, H i k * H k i +
        2 * ε * ∑ j, H i j * H j i + 3 * ε ^ 2 * H i i + ε ^ 3 := by
    intro i
    trans ∑ j, (H i j * ∑ k, H j k * H k i +
        ε * ((if i = j then (1 : ℝ) else 0) * ∑ k, H j k * H k i) +
        2 * ε * (H i j * H j i) + ε ^ 2 * ((if j = i then (1 : ℝ) else 0) * H i j) +
        2 * ε ^ 2 * ((if i = j then (1 : ℝ) else 0) * H j i) +
        ε ^ 3 * ((if i = j then (1 : ℝ) else 0) * (if j = i then (1 : ℝ) else 0)))
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_kron_mul, sum_kron_mul',
        ite_true]
      ring
  have h3 : ∑ i, ∑ j, H i j * ∑ k, H j k * H k i = ∑ i, ∑ j, ∑ k, H i j * H j k * H k i := by
    simp only [Finset.mul_sum, mul_assoc]
  have h2 : ∑ i, ∑ j, H i j * H j i = ∑ i, ∑ j, H i j ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [sq, hH j i]
  simp only [hk]
  simp only [hj]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [h3, h2]
  ring

/-- `(a - b)² ≤ 2 (a² + b²)`. -/
lemma sub_sq_le_two_mul (a b : ℝ) : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b)]

end Kronecker

/-! ### Derivative helpers -/

section Derivatives

/-- The inner product with a standard basis vector picks out a coordinate. -/
lemma innerSL_single (x : E d) (i : Fin d) :
    innerSL ℝ x (EuclideanSpace.single i 1) = x i := by
  simp [EuclideanSpace.inner_single_right]

/-- The coordinate functional evaluated on a standard basis vector is a Kronecker delta. -/
lemma proj_single (i j : Fin d) :
    EuclideanSpace.proj (𝕜 := ℝ) i (EuclideanSpace.single j (1 : ℝ)) =
      if i = j then 1 else 0 := by
  simp

/-- The derivative of a coordinate function. -/
lemma hasFDerivAt_coord (x : E d) (i : Fin d) :
    HasFDerivAt (fun y : E d => y i) (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt

/-- The derivative of `‖y‖² / 2` is `⟪x, ·⟫`. -/
lemma hasFDerivAt_half_norm_sq (x : E d) :
    HasFDerivAt (fun y : E d => ‖y‖ ^ 2 / 2) (innerSL ℝ x) x := by
  have := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const (1 / 2 : ℝ)
  convert this using 1
  · ext y; ring
  · ext v; simp

/-- A partial derivative of a smooth function is smooth. -/
lemma contDiff_pd {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin d) :
    ContDiff ℝ ∞ (pd g i) := by
  show ContDiff ℝ ∞ (fun x => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)))
  exact (contDiff_infty_iff_fderiv.1 hg).2.clm_apply contDiff_const

/-- A second partial derivative is the second Fréchet derivative evaluated on basis vectors:
`∂ⱼ∂ᵢ g x = D²g(x) eⱼ eᵢ`. -/
lemma pd_pd_eq_fderiv_fderiv {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (i j : Fin d) (x : E d) :
    pd (pd g i) j x = fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) := by
  have h2 : Differentiable ℝ (fderiv ℝ g) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_infty_iff_fderiv.1 hg).2).1
  have h : HasFDerivAt (pd g i) ((fderiv ℝ g x).comp (0 : E d →L[ℝ] E d) +
      (fderiv ℝ (fderiv ℝ g) x).flip (EuclideanSpace.single i (1 : ℝ))) x :=
    (h2 x).hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)
  rw [pd, h.fderiv]
  simp

/-- **Schwarz's theorem** for coordinate partial derivatives of a smooth function. -/
lemma pd_pd_comm {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (i j : Fin d) (x : E d) :
    pd (pd g i) j x = pd (pd g j) i x := by
  have h1 : Differentiable ℝ g := (contDiff_infty_iff_fderiv.1 hg).1
  have h2 : Differentiable ℝ (fderiv ℝ g) :=
    (contDiff_infty_iff_fderiv.1 (contDiff_infty_iff_fderiv.1 hg).2).1
  rw [pd_pd_eq_fderiv_fderiv hg, pd_pd_eq_fderiv_fderiv hg]
  exact second_derivative_symmetric (fun y => (h1 y).hasFDerivAt) (h2 x).hasFDerivAt _ _

end Derivatives

/-! ### The logarithm of the enveloped density -/

section Log

/-- `0 < 2πR²`. -/
lemma two_pi_mul_sq_pos (hR : 0 < R) : 0 < 2 * π * R ^ 2 :=
  mul_pos (mul_pos two_pos Real.pi_pos) (pow_pos hR 2)

/-- The Gaussian of variance `R²` is positive. -/
lemma gaussian_sq_pos (hR : 0 < R) (y : E d) : 0 < gaussian d (R ^ 2) y := by
  rw [gaussian]
  exact mul_pos (Real.rpow_pos_of_pos (two_pi_mul_sq_pos hR) _) (Real.exp_pos _)

/-- The logarithm of the enveloped density `c q γ_{R²}`:
`log f = log q + (log c + log (2πR²)^(-d/2)) - R⁻² ‖y‖² / 2`. -/
lemma log_mul_gaussian_eq (hpos : ∀ x, 0 < q x) (hc : 0 < c) (hR : 0 < R) :
    (fun y => Real.log (c * q y * gaussian d (R ^ 2) y)) = fun y =>
      Real.log (q y) + (Real.log c + Real.log ((2 * π * R ^ 2) ^ (-(d : ℝ) / 2))) -
        1 / R ^ 2 * (‖y‖ ^ 2 / 2) := by
  funext y
  have hA : 0 < (2 * π * R ^ 2) ^ (-(d : ℝ) / 2) :=
    Real.rpow_pos_of_pos (two_pi_mul_sq_pos hR) _
  have hB : 0 < Real.exp (-‖y‖ ^ 2 / (2 * R ^ 2)) := Real.exp_pos _
  rw [gaussian, Real.log_mul (mul_pos hc (hpos y)).ne' (mul_pos hA hB).ne',
    Real.log_mul hc.ne' (hpos y).ne', Real.log_mul hA.ne' hB.ne', Real.log_exp]
  ring

/-- The derivative of the logarithm of the enveloped density `c q γ_{R²}` is
`D log q (x) - R⁻² ⟪x, ·⟫`. -/
lemma hasFDerivAt_log_mul_gaussian (hq : ContDiff ℝ ∞ q) (hpos : ∀ x, 0 < q x) (hc : 0 < c)
    (hR : 0 < R) (x : E d) :
    HasFDerivAt (fun y => Real.log (c * q y * gaussian d (R ^ 2) y))
      (fderiv ℝ (fun y => Real.log (q y)) x - (1 / R ^ 2) • innerSL ℝ x) x := by
  have hL : Differentiable ℝ (fun y => Real.log (q y)) :=
    (contDiff_infty_iff_fderiv.1 (hq.log fun y => (hpos y).ne')).1
  rw [log_mul_gaussian_eq hpos hc hR]
  exact ((hL x).hasFDerivAt.add_const
    (Real.log c + Real.log ((2 * π * R ^ 2) ^ (-(d : ℝ) / 2)))).fun_sub
      ((hasFDerivAt_half_norm_sq x).const_mul (1 / R ^ 2))

end Log

end Envelope

open Envelope

/-! ### The envelope shifts the log-Hessian by `R⁻² Id` -/

/-- **First derivatives**: `∂ᵢ log (c q γ_{R²}) = ∂ᵢ log q - xᵢ / R²`. -/
theorem pd_log_mul_gaussian (hq : ContDiff ℝ ∞ q) (hpos : ∀ x, 0 < q x) (hc : 0 < c)
    (hR : 0 < R) (i : Fin d) (x : E d) :
    pd (fun y => Real.log (c * q y * gaussian d (R ^ 2) y)) i x =
      pd (fun y => Real.log (q y)) i x - x i / R ^ 2 := by
  show fderiv ℝ (fun y => Real.log (c * q y * gaussian d (R ^ 2) y)) x
      (EuclideanSpace.single i (1 : ℝ)) =
    fderiv ℝ (fun y => Real.log (q y)) x (EuclideanSpace.single i (1 : ℝ)) - x i / R ^ 2
  rw [(hasFDerivAt_log_mul_gaussian hq hpos hc hR x).fderiv, sub_apply, smul_apply,
    innerSL_single, smul_eq_mul]
  ring

/-- **Second derivatives**: the envelope shifts the log-Hessian by `R⁻² Id`,
`negHess (c q γ_{R²})ᵢⱼ = negHess qᵢⱼ + R⁻² δᵢⱼ`. -/
theorem negHess_mul_gaussian (hq : ContDiff ℝ ∞ q) (hpos : ∀ x, 0 < q x) (hc : 0 < c)
    (hR : 0 < R) (i j : Fin d) (x : E d) :
    negHess (fun y => c * q y * gaussian d (R ^ 2) y) i j x =
      negHess q i j x + (if i = j then 1 / R ^ 2 else 0) := by
  have hL : ContDiff ℝ ∞ (fun y => Real.log (q y)) := hq.log fun y => (hpos y).ne'
  have h1 : pd (fun y => Real.log (c * q y * gaussian d (R ^ 2) y)) i =
      fun y : E d => pd (fun y => Real.log (q y)) i y - y i * (1 / R ^ 2) := by
    funext y
    rw [pd_log_mul_gaussian hq hpos hc hR i y]
    ring
  have h2 : HasFDerivAt (fun y : E d => pd (fun y => Real.log (q y)) i y - y i * (1 / R ^ 2))
      (fderiv ℝ (pd (fun y => Real.log (q y)) i) x -
        (1 / R ^ 2) • EuclideanSpace.proj (𝕜 := ℝ) i) x :=
    ((contDiff_infty_iff_fderiv.1 (contDiff_pd hL i)).1 x).hasFDerivAt.fun_sub
      ((hasFDerivAt_coord x i).mul_const (1 / R ^ 2))
  show -pd (pd (fun y => Real.log (c * q y * gaussian d (R ^ 2) y)) i) j x =
    -pd (pd (fun y => Real.log (q y)) i) j x + (if i = j then 1 / R ^ 2 else 0)
  rw [h1]
  show -fderiv ℝ (fun y : E d => pd (fun y => Real.log (q y)) i y - y i * (1 / R ^ 2)) x
      (EuclideanSpace.single j (1 : ℝ)) =
    -fderiv ℝ (pd (fun y => Real.log (q y)) i) x (EuclideanSpace.single j (1 : ℝ)) +
      (if i = j then 1 / R ^ 2 else 0)
  rw [h2.fderiv, sub_apply, smul_apply, proj_single, smul_eq_mul]
  split_ifs <;> ring

/-- **Third derivatives** are unchanged by the envelope:
`∂ₖ negHess (c q γ_{R²})ᵢⱼ = ∂ₖ negHess qᵢⱼ`. -/
theorem pd_negHess_mul_gaussian (hq : ContDiff ℝ ∞ q) (hpos : ∀ x, 0 < q x) (hc : 0 < c)
    (hR : 0 < R) (i j k : Fin d) (x : E d) :
    pd (negHess (fun y => c * q y * gaussian d (R ^ 2) y) i j) k x =
      pd (negHess q i j) k x := by
  have h : negHess (fun y => c * q y * gaussian d (R ^ 2) y) i j =
      fun y => negHess q i j y + (if i = j then 1 / R ^ 2 else 0) :=
    funext fun y => negHess_mul_gaussian hq hpos hc hR i j y
  rw [h]
  simp only [pd, fderiv_add_const]

/-- **Symmetry of the log-Hessian** (Schwarz): `negHess q i j = negHess q j i`. -/
theorem negHess_symm (hq : ContDiff ℝ ∞ q) (hpos : ∀ x, 0 < q x) (i j : Fin d) (x : E d) :
    negHess q i j x = negHess q j i x := by
  show -pd (pd (fun y => Real.log (q y)) i) j x = -pd (pd (fun y => Real.log (q y)) j) i x
  rw [pd_pd_comm (hq.log fun y => (hpos y).ne') i j x]

/-- **The kernel under the envelope**: with `H = negHess q`,
`K_f = K_q + 6 R⁻² Σᵢⱼ Hᵢⱼ² + 6 R⁻⁴ Σᵢ Hᵢᵢ + 2 d R⁻⁶` for `f = c q γ_{R²}`. -/
theorem kernelK_mul_gaussian (hq : ContDiff ℝ ∞ q) (hpos : ∀ x, 0 < q x) (hc : 0 < c)
    (hR : 0 < R) (x : E d) :
    kernelK (fun y => c * q y * gaussian d (R ^ 2) y) x =
      kernelK q x + 6 / R ^ 2 * (∑ i, ∑ j, (negHess q i j x) ^ 2)
        + 6 / R ^ 4 * (∑ i, negHess q i i x) + 2 * d / R ^ 6 := by
  have hH : ∀ i j, negHess (fun y => c * q y * gaussian d (R ^ 2) y) i j x =
      negHess q i j x + 1 / R ^ 2 * (if i = j then (1 : ℝ) else 0) := by
    intro i j
    rw [negHess_mul_gaussian hq hpos hc hR i j x]
    split_ifs <;> ring
  have key : ∑ i, ∑ j, ∑ k,
      (negHess q i j x + 1 / R ^ 2 * (if i = j then (1 : ℝ) else 0)) *
        (negHess q j k x + 1 / R ^ 2 * (if j = k then (1 : ℝ) else 0)) *
        (negHess q k i x + 1 / R ^ 2 * (if k = i then (1 : ℝ) else 0)) =
      ∑ i, ∑ j, ∑ k, negHess q i j x * negHess q j k x * negHess q k i x +
        3 * (1 / R ^ 2) * ∑ i, ∑ j, negHess q i j x ^ 2 +
        3 * (1 / R ^ 2) ^ 2 * ∑ i, negHess q i i x + (d : ℝ) * (1 / R ^ 2) ^ 3 :=
    sum_cube_add_smul_kron (fun i j => negHess q i j x)
      (fun i j => negHess_symm hq hpos i j x) (1 / R ^ 2)
  simp only [kernelK, hH, pd_negHess_mul_gaussian hq hpos hc hR]
  rw [key]
  ring

/-- **The Fisher integrand under the envelope**:
`fisherDensity f x = f x Σᵢ (∂ᵢ log q (x) - xᵢ / R²)²` for `f = c q γ_{R²}`. -/
theorem fisherDensity_mul_gaussian (hq : ContDiff ℝ ∞ q) (hpos : ∀ x, 0 < q x) (hc : 0 < c)
    (hR : 0 < R) (x : E d) :
    fisherDensity (fun y => c * q y * gaussian d (R ^ 2) y) x =
      c * q x * gaussian d (R ^ 2) x *
        ∑ i, (pd (fun y => Real.log (q y)) i x - x i / R ^ 2) ^ 2 := by
  simp only [fisherDensity, pd_log_mul_gaussian hq hpos hc hR]

/-- **Pointwise bound for the Fisher integrand under the envelope**:
`|fisherDensity f x| ≤ f x Σᵢ 2 ((∂ᵢ log q (x))² + (xᵢ / R²)²)` for `f = c q γ_{R²}`. -/
theorem abs_fisherDensity_mul_gaussian_le (hq : ContDiff ℝ ∞ q) (hpos : ∀ x, 0 < q x)
    (hc : 0 < c) (hR : 0 < R) (x : E d) :
    |fisherDensity (fun y => c * q y * gaussian d (R ^ 2) y) x| ≤
      c * q x * gaussian d (R ^ 2) x *
        ∑ i, 2 * ((pd (fun y => Real.log (q y)) i x) ^ 2 + (x i / R ^ 2) ^ 2) := by
  have hf : 0 < c * q x * gaussian d (R ^ 2) x :=
    mul_pos (mul_pos hc (hpos x)) (gaussian_sq_pos hR x)
  have hS : 0 ≤ ∑ i, (pd (fun y => Real.log (q y)) i x - x i / R ^ 2) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [fisherDensity_mul_gaussian hq hpos hc hR x, abs_of_nonneg (mul_nonneg hf.le hS)]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => sub_sq_le_two_mul _ _) hf.le

end Fisher41
