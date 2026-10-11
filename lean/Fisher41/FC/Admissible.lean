/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.FC.Bridge
import Fisher41.Main.FlowHyp

/-!
# The densities `f_R` are admissible in the sense of Zou–Fan–Gao–Wang

For every `R > 0` the enveloped density `f_R = Z_R⁻¹ q γ_{R²}` (`Fisher41.fR`) belongs to the
admissible class `𝒜₄₁` of the statement (`Arxiv.«2605.18081».IsAdmissible`); in particular so
does the manuscript's density `Fisher41.fPDF` (`R = 10⁴⁰`).

## Main results

* `Arxiv.«2605.18081».fR_isAdmissible`: `f_R` is admissible for every `R > 0`.
* `Arxiv.«2605.18081».fPDF_isAdmissible`: the manuscript's density is admissible.

## Proof sketch

* **Schwartz.** The Gaussian `γ_T` is a Schwartz function: by Tau Ceti's bounds on the heat
  kernel, `‖D^n γ_T‖ ≤ C γ_{2T}` and `(1 + ‖x‖)^k γ_{2T} ≤ C' γ_{4T}`, which is bounded. The
  periodic factor `q` is smooth with bounded derivatives of all orders, hence of temperate
  growth, so `f_R = Z_R⁻¹ q γ_{R²}` is Schwartz (`SchwartzMap.smulLeftCLM`).
* **Finiteness.** Positivity, mass one and finiteness of the Fisher information are
  `Fisher41.fR_pos`, `Fisher41.integral_fR` and `Fisher41.integrable_fisherDensity_fR`. The
  envelope only shifts the log-Hessian by `R⁻² Id` (`Fisher41.negHess_mul_gaussian`,
  `Fisher41.kernelK_fR`), so `∑ᵢⱼ Hᵢⱼ²` and `K_{f_R}` are continuous and invariant under the
  lattice `20 ℤ⁴¹`, hence bounded, and their products with the integrable `f_R` are integrable.
* **`𝒬[f_R] > 0`.** Near `x₀ = 10 e₀`, at distance `10` from the lattice, the periodic
  log-density vanishes, so `q = 1` there and `H_{f_R}(x₀) = R⁻² Id`. The continuous nonnegative
  integrand `f_R ∑ᵢⱼ Hᵢⱼ²` is therefore positive at `x₀`, and its integral is positive.

Auxiliary lemmas live in the namespace `Arxiv.«2605.18081».Admissible`.
-/

open MeasureTheory Real
open scoped SchwartzMap

noncomputable section

namespace Arxiv.«2605.18081»

namespace Admissible

open Fisher41

/-! ### The Gaussian is a Schwartz function -/

/-- The heat kernel is bounded (by its value at the origin). -/
theorem exists_heatKernel_le {d : ℕ} {s : ℝ} (hs : 0 < s) :
    ∃ B, ∀ x : E d, TauCeti.heatKernel s x ≤ B := by
  refine ⟨(4 * π * s) ^ (-(Module.finrank ℝ (E d) : ℝ) / 2), fun x => ?_⟩
  rw [TauCeti.heatKernel_apply]
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  rw [neg_div]
  exact neg_nonpos.2 (by positivity)

/-- **Decay of the Gaussian.** All derivatives of the Gaussian `γ_T`, `T > 0`, decay faster
than any power: `‖x‖^k ‖D^n γ_T(x)‖ ≤ C`. -/
theorem gaussian_decay {d : ℕ} {T : ℝ} (hT : 0 < T) (k n : ℕ) :
    ∃ C, ∀ x : E d, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussian d T) x‖ ≤ C := by
  have hs₁ : 0 < 2 * (T / 2) := by positivity
  have hs₂ : 0 < 2 * (2 * (T / 2)) := by positivity
  obtain ⟨C₁, hC₁⟩ :=
    TauCeti.exists_norm_iteratedFDeriv_heatKernel_le (E := E d) (half_pos hT) n
  obtain ⟨C₂, hC₂⟩ := TauCeti.exists_one_add_norm_pow_mul_heatKernel_le (E := E d) hs₁ k
  obtain ⟨B, hB⟩ := exists_heatKernel_le (d := d) hs₂
  have hK₁ : ∀ x : E d, 0 < TauCeti.heatKernel (2 * (T / 2)) x :=
    fun x => TauCeti.heatKernel_pos hs₁ x
  have hK₂ : ∀ x : E d, 0 < TauCeti.heatKernel (2 * (2 * (T / 2))) x :=
    fun x => TauCeti.heatKernel_pos hs₂ x
  have hC₁0 : 0 ≤ C₁ :=
    (mul_nonneg_iff_of_pos_right (hK₁ 0)).1 ((norm_nonneg _).trans (hC₁ 0))
  have hC₂0 : 0 ≤ C₂ := (mul_nonneg_iff_of_pos_right (hK₂ 0)).1
    ((mul_nonneg (by positivity) (hK₁ 0).le).trans (hC₂ 0))
  refine ⟨C₁ * (C₂ * B), fun x => ?_⟩
  rw [gaussian_eq_heatKernel]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (TauCeti.heatKernel (E := E d) (T / 2)) x‖
      ≤ (1 + ‖x‖) ^ k * (C₁ * TauCeti.heatKernel (2 * (T / 2)) x) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) (by linarith) k) (hC₁ x) (norm_nonneg _)
          (by positivity)
    _ = C₁ * ((1 + ‖x‖) ^ k * TauCeti.heatKernel (2 * (T / 2)) x) := by ring
    _ ≤ C₁ * (C₂ * TauCeti.heatKernel (2 * (2 * (T / 2))) x) :=
        mul_le_mul_of_nonneg_left (hC₂ x) hC₁0
    _ ≤ C₁ * (C₂ * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB x) hC₂0) hC₁0

/-- The Gaussian `γ_T` of variance `T > 0`, as a Schwartz function. -/
def gaussianSchwartz {d : ℕ} {T : ℝ} (hT : 0 < T) : 𝓢(E d, ℝ) where
  toFun := gaussian d T
  smooth' := DensityNeg.contDiff_gaussian d T
  decay' := gaussian_decay hT

/-- The Schwartz function `gaussianSchwartz hT` is the Gaussian `γ_T`. -/
theorem gaussianSchwartz_apply {d : ℕ} {T : ℝ} (hT : 0 < T) (x : E d) :
    gaussianSchwartz hT x = gaussian d T x :=
  rfl

/-! ### `f_R` is a Schwartz function -/

/-- `q` has temperate growth: it is smooth and all its derivatives are bounded. -/
theorem hasTemperateGrowth_qper : Function.HasTemperateGrowth qper := by
  refine ⟨contDiff_qper, fun n => ?_⟩
  obtain ⟨C, hC⟩ := FlowHyp.exists_norm_iteratedFDeriv_qper_le n
  exact ⟨0, C, fun x => by rw [pow_zero, mul_one]; exact hC x⟩

/-- **`f_R` is a Schwartz function**: `f_R = Z_R⁻¹ q γ_{R²}`, where `γ_{R²}` is Schwartz and `q`
has temperate growth. -/
theorem exists_schwartzMap_eq_fR {R : ℝ} (hR : 0 < R) : ∃ φ : 𝓢(E 41, ℝ), ⇑φ = fR R := by
  have hT : (0 : ℝ) < R ^ 2 := by positivity
  refine ⟨(∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ •
    SchwartzMap.smulLeftCLM ℝ qper (gaussianSchwartz hT), funext fun x => ?_⟩
  have h : SchwartzMap.smulLeftCLM ℝ qper (gaussianSchwartz hT) x =
      qper x * gaussian 41 (R ^ 2) x := by
    rw [SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_qper, gaussianSchwartz_apply,
      smul_eq_mul]
  show (∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ •
    SchwartzMap.smulLeftCLM ℝ qper (gaussianSchwartz hT) x = fR R x
  rw [h, smul_eq_mul, fR]
  ring

/-! ### The log-Hessian of `f_R` -/

/-- The envelope shifts the log-Hessian by `R⁻² Id`: `H_{f_R} = H_q + R⁻² Id`. -/
theorem negHess_fR_apply {R : ℝ} (hR : 0 < R) (i j : Fin 41) (x : E 41) :
    negHess (fR R) i j x = negHess qper i j x + (if i = j then 1 / R ^ 2 else 0) := by
  have hZ : 0 < (∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ :=
    inv_pos.2 (lt_of_lt_of_le one_pos (one_le_integral_qper_mul_gaussian hR))
  rw [fR_eq, negHess_mul_gaussian contDiff_qper qper_pos hZ hR]

/-- The entries of the log-Hessian of `f_R` are continuous. -/
theorem continuous_negHess_fR {R : ℝ} (hR : 0 < R) (i j : Fin 41) :
    Continuous (negHess (fR R) i j) := by
  have h : negHess (fR R) i j = fun x => negHess qper i j x + (if i = j then 1 / R ^ 2 else 0) :=
    funext (negHess_fR_apply hR i j)
  rw [h]
  exact (DensityNeg.continuous_negHess_qper i j).add continuous_const

/-- The log-Hessian of `f_R` is invariant under the lattice `20 ℤ⁴¹`. -/
theorem negHess_fR_add_latt {R : ℝ} (hR : 0 < R) (i j : Fin 41) (x : E 41)
    (z : Fin 41 → ℤ) : negHess (fR R) i j (x + latt z) = negHess (fR R) i j x := by
  rw [negHess_fR_apply hR, negHess_fR_apply hR,
    DensityNeg.negHess_add_of_forall_add (ρ := qper) (a := latt z) (fun y => qper_add_latt y z)]

/-- `∑ᵢⱼ (H_{f_R})ᵢⱼ²` is continuous. -/
theorem continuous_sum_sq_negHess_fR {R : ℝ} (hR : 0 < R) :
    Continuous fun x => ∑ i, ∑ j, negHess (fR R) i j x ^ 2 :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_negHess_fR hR i j).pow 2

/-! ### Finiteness of `𝒬[f_R]` and `𝒟[f_R]` -/

/-- If `g` is continuous and invariant under the lattice `20 ℤ⁴¹`, then `f_R g` is integrable. -/
theorem integrable_fR_mul_of_add_latt {R : ℝ} (hR : 0 < R) {g : E 41 → ℝ} (hc : Continuous g)
    (hper : ∀ x z, g (x + latt z) = g x) : Integrable fun x => fR R x * g x := by
  obtain ⟨M, hM⟩ := DensityNeg.exists_abs_le_of_add_latt hc hper
  exact (integrable_fR hR).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs (g x)).trans_le (hM x))

/-- The integrand `f_R ∑ᵢⱼ Hᵢⱼ²` of `𝒬[f_R]` is integrable. -/
theorem integrable_fR_mul_sum_sq_negHess {R : ℝ} (hR : 0 < R) :
    Integrable fun x => fR R x * ∑ i, ∑ j, negHess (fR R) i j x ^ 2 :=
  integrable_fR_mul_of_add_latt hR (continuous_sum_sq_negHess_fR hR) fun x z => by
    simp only [negHess_fR_add_latt hR]

/-- The integrand `f_R K_{f_R}` of `𝒟[f_R]` is integrable. -/
theorem integrable_fR_mul_kernelK {R : ℝ} (hR : 0 < R) :
    Integrable fun x => fR R x * kernelK (fR R) x := by
  have hS : Continuous fun x => ∑ i, ∑ j, negHess qper i j x ^ 2 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (DensityNeg.continuous_negHess_qper i j).pow 2
  have hT : Continuous fun x => ∑ i, negHess qper i i x :=
    continuous_finsetSum _ fun i _ => DensityNeg.continuous_negHess_qper i i
  have hc : Continuous fun x => kernelK qper x + 6 / R ^ 2 * (∑ i, ∑ j, negHess qper i j x ^ 2) +
      6 / R ^ 4 * (∑ i, negHess qper i i x) + 2 * 41 / R ^ 6 :=
    ((DensityNeg.continuous_kernelK_qper.add (continuous_const.mul hS)).add
      (continuous_const.mul hT)).add continuous_const
  have hper : ∀ (x : E 41) (z : Fin 41 → ℤ),
      kernelK qper (x + latt z) + 6 / R ^ 2 * (∑ i, ∑ j, negHess qper i j (x + latt z) ^ 2) +
          6 / R ^ 4 * (∑ i, negHess qper i i (x + latt z)) + 2 * 41 / R ^ 6 =
        kernelK qper x + 6 / R ^ 2 * (∑ i, ∑ j, negHess qper i j x ^ 2) +
          6 / R ^ 4 * (∑ i, negHess qper i i x) + 2 * 41 / R ^ 6 := fun x z => by
    simp only [DensityNeg.kernelK_add_of_forall_add (ρ := qper) (a := latt z)
        (fun y => qper_add_latt y z),
      DensityNeg.negHess_add_of_forall_add (ρ := qper) (a := latt z)
        (fun y => qper_add_latt y z)]
  have hfun : (fun x => fR R x * kernelK (fR R) x) = fun x => fR R x *
      (kernelK qper x + 6 / R ^ 2 * (∑ i, ∑ j, negHess qper i j x ^ 2) +
        6 / R ^ 4 * (∑ i, negHess qper i i x) + 2 * 41 / R ^ 6) :=
    funext fun x => by rw [kernelK_fR hR x]
  rw [hfun]
  exact integrable_fR_mul_of_add_latt hR hc hper

/-! ### Positivity of `𝒬[f_R]` -/

/-- The point `10 e₀`, halfway between the lattice points `0` and `20 e₀`. -/
def xMid : E 41 := (10 : ℝ) • EuclideanSpace.single (0 : Fin 41) (1 : ℝ)

/-- `‖10 e₀‖ = 10`. -/
theorem norm_xMid : ‖xMid‖ = 10 := by
  simp [xMid, norm_smul]

/-- Near `10 e₀` no bump is active, so `q = 1` there. -/
theorem qper_eq_one_of_mem_ball {x : E 41} (hx : x ∈ Metric.ball xMid 1) : qper x = 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hbox : ∀ i, |x i| < 11 := fun i => by
    have h1 := Periodic.abs_apply_le_norm (x - xMid) i
    have h2 := Periodic.abs_apply_le_norm xMid i
    have h3 : x i = (x - xMid) i + xMid i := by rw [PiLp.sub_apply, sub_add_cancel]
    rw [h3]
    linarith [abs_add_le ((x - xMid) i) (xMid i), norm_xMid]
  have hnorm : 8 ≤ ‖x‖ := by
    have h := norm_sub_norm_le xMid x
    rw [norm_sub_rev, norm_xMid] at h
    linarith
  show Real.exp (Uper x) = 1
  rw [Uper_eq_bump hbox, bump_eq_zero hnorm, Real.exp_zero]

/-- The log-Hessian of `q` vanishes at `10 e₀`, since `q = 1` near this point. -/
theorem negHess_qper_xMid (i j : Fin 41) : negHess qper i j xMid = 0 := by
  have hs : IsOpen (Metric.ball xMid 1) := Metric.isOpen_ball
  have hlog : Set.EqOn (fun y => Real.log (qper y)) (fun _ => (0 : ℝ)) (Metric.ball xMid 1) :=
    fun y hy => by simp only [qper_eq_one_of_mem_ball hy, Real.log_one]
  have h1 := Periodic.pd_eqOn hs hlog i
  rw [DensityFlow.pd_const] at h1
  have h2 := Periodic.pd_eqOn hs h1 j
  rw [DensityFlow.pd_const] at h2
  have h3 : pd (pd (fun y => Real.log (qper y)) i) j xMid = 0 :=
    h2 (Metric.mem_ball_self one_pos)
  show -pd (pd (fun y => Real.log (qper y)) i) j xMid = 0
  rw [h3, neg_zero]

/-- **`𝒬[f_R] > 0`**: the continuous nonnegative integrand `f_R ∑ᵢⱼ Hᵢⱼ²` is positive at
`10 e₀`, where `H_{f_R} = R⁻² Id`. -/
theorem integral_fR_mul_sum_sq_negHess_pos {R : ℝ} (hR : 0 < R) :
    0 < ∫ x, fR R x * ∑ i, ∑ j, negHess (fR R) i j x ^ 2 := by
  have hH : negHess (fR R) 0 0 xMid = 1 / R ^ 2 := by
    rw [negHess_fR_apply hR, negHess_qper_xMid, ite_eq_left rfl, zero_add]
  have h00 : 0 < negHess (fR R) 0 0 xMid ^ 2 := by
    rw [hH]
    positivity
  have hrow : 0 < ∑ j, negHess (fR R) 0 j xMid ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨0, Finset.mem_univ _, h00⟩
  have hS : 0 < ∑ i, ∑ j, negHess (fR R) i j xMid ^ 2 :=
    Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      ⟨0, Finset.mem_univ _, hrow⟩
  exact integral_pos_of_integrable_nonneg_nonzero (x := xMid)
    ((contDiff_fR R).continuous.mul (continuous_sum_sq_negHess_fR hR))
    (integrable_fR_mul_sum_sq_negHess hR)
    (fun x => mul_nonneg (fR_pos hR x).le
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _))
    (mul_pos (fR_pos hR xMid) hS).ne'

end Admissible

/-- **The densities `f_R` are admissible**: for every `R > 0`, `f_R = Z_R⁻¹ q γ_{R²}` is a
positive Schwartz probability density with `ℐ[f_R], 𝒬[f_R], 𝒟[f_R] < ∞` and `𝒬[f_R] > 0`. -/
theorem fR_isAdmissible {R : ℝ} (hR : 0 < R) : IsAdmissible (Fisher41.fR R) := by
  refine ⟨Admissible.exists_schwartzMap_eq_fR hR, Fisher41.fR_pos hR, Fisher41.integral_fR hR,
    ?_, ?_, ?_, ?_⟩
  · rw [fisherIntegrand_eq (Fisher41.fR R)]
    exact Fisher41.integrable_fisherDensity_fR hR
  · rw [qIntegrand_eq (Fisher41.fR R)]
    exact Admissible.integrable_fR_mul_sum_sq_negHess hR
  · rw [dIntegrand_eq (Fisher41.fR R)]
    exact Admissible.integrable_fR_mul_kernelK hR
  · rw [qIntegrand_eq (Fisher41.fR R)]
    exact Admissible.integral_fR_mul_sum_sq_negHess_pos hR

/-- **The density of the manuscript is admissible** (`R = 10⁴⁰`). -/
theorem fPDF_isAdmissible : IsAdmissible Fisher41.fPDF :=
  fR_isAdmissible (R := Fisher41.Rstd) (by norm_num [Fisher41.Rstd])

end Arxiv.«2605.18081»
