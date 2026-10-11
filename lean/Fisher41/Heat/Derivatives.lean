/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Heat.DensityFlow
import Fisher41.Heat.Identities
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The first two time derivatives of the Fisher information along the heat flow

Let `H : DensityFlowHyp d T c Q q f` and `ρ s = heat f s`. For every `t > 0`:

* the integrands `ρ |∇ log ρ|²`, `ρ |∇² log ρ|²` and `ρ K_ρ` are integrable at time `t`
  (`Fisher41.DensityFlowHyp.integrable_fisherDensity_flow`,
  `Fisher41.DensityFlowHyp.integrable_hessDensity_flow`,
  `Fisher41.DensityFlowHyp.integrable_mul_kernelK_flow`);
* `I' = -Q`: the Fisher information `I(s) = fisher (ρ s)` has derivative `-Q(t)` at `t`, where
  `Q(s) = ∫ ρ s |∇² log ρ s|²` (`Fisher41.DensityFlowHyp.hasDerivAt_fisher_flow`);
* `Q' = -D`: `Q` has derivative `-Dfun (ρ t) = -∫ ρ t K_{ρ t}` at `t`
  (`Fisher41.DensityFlowHyp.hasDerivAt_hessFisher_flow`).

## Proof

We differentiate under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
for times `s ∈ (0, 2t)`. The pointwise time derivatives are the divergence identities P1 and P2
of `Fisher41.Heat.Identities`: with `w, A, T` the first three derivatives of `log ρ s`,
`∂ₛ (ρ |w|²) = Σᵢ ∂ᵢ Vᵢ - ρ |A|²` and `∂ₛ (ρ |A|²) = Σₖ ∂ₖ Wₖ - ρ K_ρ`.

Every integrand that occurs, including the fluxes `Vᵢ`, `Wₖ` and their divergences, is `ρ s`
times a polynomial in the logarithmic derivatives of `ρ s` of order at most four. These are
polynomials in the ratios `∂ˡρ s / ρ s` (`Fisher41.Derivatives.logA_eq_ratio`,
`Fisher41.Derivatives.logT_eq_ratio`, `Fisher41.Derivatives.logQ_eq_ratio`), which are bounded by
`K (1 + ‖x‖)^m` uniformly in `s ∈ (0, t₁]`
(`Fisher41.DensityFlowHyp.exists_abs_pdList_flow_div_le`).
Since moreover `ρ s ≤ c Q γ_{T+s} ≤ C γ_{T+t₁}`, all integrands are dominated by
`C (1 + ‖x‖)^m γ_{T+t₁}(x)`, uniformly in `s ∈ (0, t₁]`.

Finally `∫ ∂ᵢ V = 0` whenever `V` is differentiable and `V`, `∂ᵢ V` are integrable
(`Fisher41.Derivatives.integral_pd_eq_zero`, integration by parts against the constant `1`), so the
divergence terms integrate to zero.

## Implementation notes

* `Fisher41.Derivatives.UPoly S g` records measurability and a polynomial bound
  `|g s x| ≤ K (1 + ‖x‖)^m`, uniform in `s ∈ S`, of a time-dependent function `g`. It is closed
  under sums, differences, products, powers, division by constants and finite sums.
* `Fisher41.Derivatives.Dom T t₁ F` records measurability and the domination
  `|F s x| ≤ C (1 + ‖x‖)^m γ_{T+t₁}(x)`, uniform in `s ∈ (0, t₁]`. It is closed under sums,
  differences and finite sums, and `Fisher41.Derivatives.dom_of_upoly` passes from `UPoly` to
  `Dom` after multiplication by `ρ s`.
* The polynomial parts of the integrands are named (`Fisher41.Derivatives.pFlux1`,
  `Fisher41.Derivatives.pDFlux1`, …) so that the closure lemmas can be applied structurally.
-/

open MeasureTheory Real
open scoped Topology ContDiff

noncomputable section

namespace Fisher41

namespace Derivatives

open Identities

variable {d : ℕ}

/-! ### Fluxes and integrands -/

/-- The polynomial part `|w|² wᵢ / 2 + Σⱼ Aᵢⱼ wⱼ` of the flux of P1, where `w = ∇ log g` and
`A = ∇² log g`. -/
def pFlux1 (g : E d → ℝ) (i : Fin d) (x : E d) : ℝ :=
  (∑ k, logW g k x ^ 2) * logW g i x / 2 + ∑ j, logA g i j x * logW g j x

/-- The flux `Vᵢ = g (|w|² wᵢ / 2 + Σⱼ Aᵢⱼ wⱼ)` of the divergence identity P1. -/
def fluxP1 (g : E d → ℝ) (i : Fin d) (x : E d) : ℝ :=
  g x * pFlux1 g i x

/-- The polynomial part of the divergence `∂ᵢ Vᵢ` of the flux of P1
(see `Fisher41.Derivatives.pd_fluxP1_eq`). -/
def pDFlux1 (g : E d → ℝ) (i : Fin d) (x : E d) : ℝ :=
  logW g i x * pFlux1 g i x
    + ((∑ k, logW g k x * logA g k i x) * logW g i x + (∑ k, logW g k x ^ 2) * logA g i i x / 2
      + ∑ j, (logT g i j i x * logW g j x + logA g i j x * logA g j i x))

/-- `|∇² log g|² = Σᵢⱼ (∂ⱼ∂ᵢ log g)²`. -/
def pHess (g : E d → ℝ) (x : E d) : ℝ :=
  ∑ i, ∑ j, logA g i j x ^ 2

/-- The integrand `g |∇² log g|²` of the second functional `Q`. -/
def hessDensity (g : E d → ℝ) (x : E d) : ℝ :=
  g x * pHess g x

/-- The polynomial part `|A|² wₖ / 2 + Σᵢⱼ Aᵢⱼ Tᵢⱼₖ` of the flux of P2, where `w, A, T` are the
first three derivatives of `log g`. -/
def pFlux2 (g : E d → ℝ) (k : Fin d) (x : E d) : ℝ :=
  pHess g x * logW g k x / 2 + ∑ i, ∑ j, logA g i j x * logT g i j k x

/-- The flux `Wₖ = g (|A|² wₖ / 2 + Σᵢⱼ Aᵢⱼ Tᵢⱼₖ)` of the divergence identity P2. -/
def fluxP2 (g : E d → ℝ) (k : Fin d) (x : E d) : ℝ :=
  g x * pFlux2 g k x

/-- The polynomial part of the divergence `∂ₖ Wₖ` of the flux of P2
(see `Fisher41.Derivatives.pd_fluxP2_eq`). -/
def pDFlux2 (g : E d → ℝ) (k : Fin d) (x : E d) : ℝ :=
  logW g k x * pFlux2 g k x
    + ((∑ i, ∑ j, logA g i j x * logT g i j k x) * logW g k x + pHess g x * logA g k k x / 2
      + ∑ i, ∑ j, (logT g i j k x ^ 2 + logA g i j x * logQ g i j k k x))

/-- `K_g = Σᵢⱼₖ (∂ₖ∂ⱼ∂ᵢ log g)² - 2 Σᵢⱼₖ AᵢⱼAⱼₖAₖᵢ`, written with logarithmic derivatives
(see `Fisher41.Identities.kernelK_eq_log`). -/
def pKernel (g : E d → ℝ) (x : E d) : ℝ :=
  ∑ i, ∑ j, ∑ k, logT g i j k x ^ 2
    - 2 * ∑ i, ∑ j, ∑ k, logA g i j x * logA g j k x * logA g k i x

/-- The time derivative of the Fisher integrand along the heat flow (P1):
`Σᵢ ∂ᵢ Vᵢ - g |∇² log g|²`. -/
def dFisherDensity (g : E d → ℝ) (x : E d) : ℝ :=
  (∑ i, pd (fluxP1 g i) i x) - hessDensity g x

/-- The time derivative of `Fisher41.Derivatives.hessDensity` along the heat flow (P2):
`Σₖ ∂ₖ Wₖ - g K_g`. -/
def dHessDensity (g : E d → ℝ) (x : E d) : ℝ :=
  (∑ k, pd (fluxP2 g k) k x) - g x * kernelK g x

/-! ### Uniform polynomial bounds -/

/-- `UPoly S g`: for every `s ∈ S` the function `g s` is measurable, and
`|g s x| ≤ K (1 + ‖x‖)^m` for all `s ∈ S` and all `x`, with `K` and `m` independent of `s`. -/
def UPoly (S : Set ℝ) (g : ℝ → E d → ℝ) : Prop :=
  (∀ s ∈ S, Measurable (g s)) ∧ ∃ K : ℝ, ∃ m : ℕ, ∀ s ∈ S, ∀ x, |g s x| ≤ K * (1 + ‖x‖) ^ m

namespace UPoly

/-- Constants are uniformly polynomially bounded. -/
theorem const (S : Set ℝ) (a : ℝ) : UPoly S (fun (_ : ℝ) (_ : E d) => a) :=
  ⟨fun _ _ => measurable_const, |a|, 0, fun _ _ _ => by simp⟩

/-- Uniform polynomial bounds transfer along pointwise equalities on `S`. -/
theorem congr {S : Set ℝ} {g g' : ℝ → E d → ℝ} (h : UPoly S g)
    (e : ∀ s ∈ S, ∀ x, g' s x = g s x) : UPoly S g' := by
  obtain ⟨hm, K, m, hK⟩ := h
  refine ⟨fun s hs => ?_, K, m, fun s hs x => ?_⟩
  · rw [show g' s = g s from funext (e s hs)]
    exact hm s hs
  · rw [e s hs x]
    exact hK s hs x

/-- Sums of uniformly polynomially bounded functions. -/
theorem add {S : Set ℝ} {u v : ℝ → E d → ℝ} (hu : UPoly S u) (hv : UPoly S v) :
    UPoly S (fun s x => u s x + v s x) := by
  obtain ⟨hum, K₁, m₁, h₁⟩ := hu
  obtain ⟨hvm, K₂, m₂, h₂⟩ := hv
  refine ⟨fun s hs => (hum s hs).fun_add (hvm s hs), |K₁| + |K₂|, max m₁ m₂, fun s hs x => ?_⟩
  have hx : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have key : ∀ (K : ℝ) (k : ℕ), k ≤ max m₁ m₂ →
      K * (1 + ‖x‖) ^ k ≤ |K| * (1 + ‖x‖) ^ max m₁ m₂ := fun K k hk =>
    mul_le_mul (le_abs_self K) (pow_le_pow_right₀ hx hk) (by positivity) (abs_nonneg K)
  calc |u s x + v s x| ≤ |u s x| + |v s x| := abs_add_le _ _
    _ ≤ K₁ * (1 + ‖x‖) ^ m₁ + K₂ * (1 + ‖x‖) ^ m₂ := add_le_add (h₁ s hs x) (h₂ s hs x)
    _ ≤ |K₁| * (1 + ‖x‖) ^ max m₁ m₂ + |K₂| * (1 + ‖x‖) ^ max m₁ m₂ :=
        add_le_add (key K₁ m₁ (le_max_left _ _)) (key K₂ m₂ (le_max_right _ _))
    _ = (|K₁| + |K₂|) * (1 + ‖x‖) ^ max m₁ m₂ := by ring

/-- Differences of uniformly polynomially bounded functions. -/
theorem sub {S : Set ℝ} {u v : ℝ → E d → ℝ} (hu : UPoly S u) (hv : UPoly S v) :
    UPoly S (fun s x => u s x - v s x) := by
  obtain ⟨hum, K₁, m₁, h₁⟩ := hu
  obtain ⟨hvm, K₂, m₂, h₂⟩ := hv
  refine ⟨fun s hs => (hum s hs).fun_sub (hvm s hs), |K₁| + |K₂|, max m₁ m₂, fun s hs x => ?_⟩
  have hx : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have key : ∀ (K : ℝ) (k : ℕ), k ≤ max m₁ m₂ →
      K * (1 + ‖x‖) ^ k ≤ |K| * (1 + ‖x‖) ^ max m₁ m₂ := fun K k hk =>
    mul_le_mul (le_abs_self K) (pow_le_pow_right₀ hx hk) (by positivity) (abs_nonneg K)
  calc |u s x - v s x| ≤ |u s x| + |v s x| := abs_sub _ _
    _ ≤ K₁ * (1 + ‖x‖) ^ m₁ + K₂ * (1 + ‖x‖) ^ m₂ := add_le_add (h₁ s hs x) (h₂ s hs x)
    _ ≤ |K₁| * (1 + ‖x‖) ^ max m₁ m₂ + |K₂| * (1 + ‖x‖) ^ max m₁ m₂ :=
        add_le_add (key K₁ m₁ (le_max_left _ _)) (key K₂ m₂ (le_max_right _ _))
    _ = (|K₁| + |K₂|) * (1 + ‖x‖) ^ max m₁ m₂ := by ring

/-- Products of uniformly polynomially bounded functions. -/
theorem mul {S : Set ℝ} {u v : ℝ → E d → ℝ} (hu : UPoly S u) (hv : UPoly S v) :
    UPoly S (fun s x => u s x * v s x) := by
  obtain ⟨hum, K₁, m₁, h₁⟩ := hu
  obtain ⟨hvm, K₂, m₂, h₂⟩ := hv
  refine ⟨fun s hs => (hum s hs).fun_mul (hvm s hs), K₁ * K₂, m₁ + m₂, fun s hs x => ?_⟩
  calc |u s x * v s x| = |u s x| * |v s x| := abs_mul _ _
    _ ≤ K₁ * (1 + ‖x‖) ^ m₁ * (K₂ * (1 + ‖x‖) ^ m₂) :=
        mul_le_mul (h₁ s hs x) (h₂ s hs x) (abs_nonneg _) ((abs_nonneg _).trans (h₁ s hs x))
    _ = K₁ * K₂ * (1 + ‖x‖) ^ (m₁ + m₂) := by ring

/-- Powers of uniformly polynomially bounded functions. -/
theorem pow {S : Set ℝ} {u : ℝ → E d → ℝ} (hu : UPoly S u) (n : ℕ) :
    UPoly S (fun s x => u s x ^ n) := by
  induction n with
  | zero => exact (UPoly.const S 1).congr fun _ _ _ => pow_zero _
  | succ n ih => exact (ih.mul hu).congr fun _ _ _ => pow_succ _ _

/-- Quotients of uniformly polynomially bounded functions by constants. -/
theorem div_const {S : Set ℝ} {u : ℝ → E d → ℝ} (hu : UPoly S u) (c : ℝ) :
    UPoly S (fun s x => u s x / c) :=
  (hu.mul (UPoly.const S c⁻¹)).congr fun _ _ _ => div_eq_mul_inv _ _

/-- Finite sums of uniformly polynomially bounded functions. -/
theorem sum {S : Set ℝ} {ι : Type*} (u : Finset ι) {g : ι → ℝ → E d → ℝ}
    (h : ∀ i ∈ u, UPoly S (g i)) : UPoly S (fun s x => ∑ i ∈ u, g i s x) := by
  classical
  induction u using Finset.induction_on with
  | empty => exact (UPoly.const S 0).congr fun _ _ _ => Finset.sum_empty
  | insert a u ha ih =>
    exact ((h a (Finset.mem_insert_self a u)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).congr fun _ _ _ => Finset.sum_insert ha

end UPoly

/-! ### Uniform Gaussian domination -/

/-- `Dom T t₁ F`: for every `s ∈ (0, t₁]` the function `F s` is measurable, and
`|F s x| ≤ C (1 + ‖x‖)^m γ_{T+t₁}(x)` for all `s ∈ (0, t₁]` and all `x`, with `C` and `m`
independent of `s`. -/
def Dom (T t₁ : ℝ) (F : ℝ → E d → ℝ) : Prop :=
  (∀ s ∈ Set.Ioc 0 t₁, Measurable (F s)) ∧
    ∃ C : ℝ, ∃ m : ℕ, ∀ s ∈ Set.Ioc 0 t₁, ∀ x,
      |F s x| ≤ C * (1 + ‖x‖) ^ m * gaussian d (T + t₁) x

namespace Dom

/-- The zero function is dominated. -/
theorem zero {T t₁ : ℝ} : Dom T t₁ (fun (_ : ℝ) (_ : E d) => (0 : ℝ)) :=
  ⟨fun _ _ => measurable_const, 0, 0, fun _ _ _ => by simp⟩

/-- Domination transfers along pointwise equalities on `(0, t₁]`. -/
theorem congr {T t₁ : ℝ} {F F' : ℝ → E d → ℝ} (hF : Dom T t₁ F)
    (e : ∀ s ∈ Set.Ioc 0 t₁, ∀ x, F' s x = F s x) : Dom T t₁ F' := by
  obtain ⟨hm, C, m, hC⟩ := hF
  refine ⟨fun s hs => ?_, C, m, fun s hs x => ?_⟩
  · rw [show F' s = F s from funext (e s hs)]
    exact hm s hs
  · rw [e s hs x]
    exact hC s hs x

/-- Sums of dominated functions are dominated. -/
theorem add {T t₁ : ℝ} {F G : ℝ → E d → ℝ} (hT : 0 ≤ T) (hF : Dom T t₁ F) (hG : Dom T t₁ G) :
    Dom T t₁ (fun s x => F s x + G s x) := by
  obtain ⟨hFm, C₁, m₁, h₁⟩ := hF
  obtain ⟨hGm, C₂, m₂, h₂⟩ := hG
  refine ⟨fun s hs => (hFm s hs).fun_add (hGm s hs), |C₁| + |C₂|, max m₁ m₂, fun s hs x => ?_⟩
  have hγ : 0 ≤ gaussian d (T + t₁) x :=
    Domination.gaussian_nonneg (by linarith [hs.1, hs.2]) x
  have key : ∀ (C : ℝ) (k : ℕ), k ≤ max m₁ m₂ →
      C * (1 + ‖x‖) ^ k * gaussian d (T + t₁) x ≤
        |C| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d (T + t₁) x := fun C k hk =>
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self C)
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg x)) hk) (by positivity)
      (abs_nonneg C)) hγ
  calc |F s x + G s x| ≤ |F s x| + |G s x| := abs_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ m₁ * gaussian d (T + t₁) x +
          C₂ * (1 + ‖x‖) ^ m₂ * gaussian d (T + t₁) x := add_le_add (h₁ s hs x) (h₂ s hs x)
    _ ≤ |C₁| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d (T + t₁) x +
          |C₂| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d (T + t₁) x :=
        add_le_add (key C₁ m₁ (le_max_left _ _)) (key C₂ m₂ (le_max_right _ _))
    _ = (|C₁| + |C₂|) * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d (T + t₁) x := by ring

/-- Differences of dominated functions are dominated. -/
theorem sub {T t₁ : ℝ} {F G : ℝ → E d → ℝ} (hT : 0 ≤ T) (hF : Dom T t₁ F) (hG : Dom T t₁ G) :
    Dom T t₁ (fun s x => F s x - G s x) := by
  obtain ⟨hFm, C₁, m₁, h₁⟩ := hF
  obtain ⟨hGm, C₂, m₂, h₂⟩ := hG
  refine ⟨fun s hs => (hFm s hs).fun_sub (hGm s hs), |C₁| + |C₂|, max m₁ m₂, fun s hs x => ?_⟩
  have hγ : 0 ≤ gaussian d (T + t₁) x :=
    Domination.gaussian_nonneg (by linarith [hs.1, hs.2]) x
  have key : ∀ (C : ℝ) (k : ℕ), k ≤ max m₁ m₂ →
      C * (1 + ‖x‖) ^ k * gaussian d (T + t₁) x ≤
        |C| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d (T + t₁) x := fun C k hk =>
    mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self C)
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg x)) hk) (by positivity)
      (abs_nonneg C)) hγ
  calc |F s x - G s x| ≤ |F s x| + |G s x| := abs_sub _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ m₁ * gaussian d (T + t₁) x +
          C₂ * (1 + ‖x‖) ^ m₂ * gaussian d (T + t₁) x := add_le_add (h₁ s hs x) (h₂ s hs x)
    _ ≤ |C₁| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d (T + t₁) x +
          |C₂| * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d (T + t₁) x :=
        add_le_add (key C₁ m₁ (le_max_left _ _)) (key C₂ m₂ (le_max_right _ _))
    _ = (|C₁| + |C₂|) * (1 + ‖x‖) ^ max m₁ m₂ * gaussian d (T + t₁) x := by ring

/-- Finite sums of dominated functions are dominated. -/
theorem sum {T t₁ : ℝ} {ι : Type*} (hT : 0 ≤ T) (u : Finset ι) {F : ι → ℝ → E d → ℝ}
    (h : ∀ i ∈ u, Dom T t₁ (F i)) : Dom T t₁ (fun s x => ∑ i ∈ u, F i s x) := by
  classical
  induction u using Finset.induction_on with
  | empty => exact Dom.zero.congr fun _ _ _ => Finset.sum_empty
  | insert a u ha ih =>
    exact ((h a (Finset.mem_insert_self a u)).add hT
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).congr fun _ _ _ => Finset.sum_insert ha

/-- A dominated function is integrable at every time `s ∈ (0, t₁]`. -/
theorem integrable {T t₁ : ℝ} {F : ℝ → E d → ℝ} (hT : 0 < T) (hF : Dom T t₁ F) {s : ℝ}
    (hs : s ∈ Set.Ioc 0 t₁) : Integrable (F s) := by
  obtain ⟨hm, C, m, hC⟩ := hF
  have hTt : 0 < T + t₁ := by linarith [hs.1, hs.2]
  exact ((integrable_one_add_norm_pow_mul_gaussian m hTt).const_mul C).mono'
    (hm s hs).aestronglyMeasurable (ae_of_all _ fun x =>
      (Real.norm_eq_abs _).trans_le ((hC s hs x).trans_eq (mul_assoc _ _ _)))

end Dom

/-! ### Logarithmic derivatives as polynomials in `∂ˡg / g` -/

/-- For a smooth positive `g`, `∂ⱼ∂ᵢ log g = ∂ⱼ∂ᵢ g / g - ∂ᵢ log g ∂ⱼ log g`. -/
theorem logA_eq_ratio {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ y, 0 < g y) (i j : Fin d)
    (x : E d) :
    logA g i j x = pd (pd g i) j x / g x - logW g i x * logW g j x := by
  rw [(isLogJet_log hg hpos).pd_pd_rho i j x, mul_div_cancel_left₀ _ (hpos x).ne']
  ring

/-- For a smooth positive `g`, the third logarithmic derivative `∂ₖ∂ⱼ∂ᵢ log g` is
`∂ₖ∂ⱼ∂ᵢ g / g` minus a polynomial in the first two logarithmic derivatives. -/
theorem logT_eq_ratio {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ y, 0 < g y)
    (i j k : Fin d) (x : E d) :
    logT g i j k x = pd (pd (pd g i) j) k x / g x -
      (logW g k x * (logA g i j x + logW g i x * logW g j x) +
        (logA g i k x * logW g j x + logW g i x * logA g j k x)) := by
  rw [(isLogJet_log hg hpos).pd_pd_pd_rho i j k x, mul_div_cancel_left₀ _ (hpos x).ne']
  ring

/-- For a smooth positive `g`, the fourth logarithmic derivative `∂ₗ∂ₖ∂ⱼ∂ᵢ log g` is
`∂ₗ∂ₖ∂ⱼ∂ᵢ g / g` minus a polynomial in the first three logarithmic derivatives. -/
theorem logQ_eq_ratio {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ y, 0 < g y)
    (i j k l : Fin d) (x : E d) :
    logQ g i j k l x = pd (pd (pd (pd g i) j) k) l x / g x -
      (logW g l x * (logW g k x * (logA g i j x + logW g i x * logW g j x) +
          (logT g i j k x + (logA g i k x * logW g j x + logW g i x * logA g j k x))) +
        (logA g k l x * (logA g i j x + logW g i x * logW g j x) +
            logW g k x *
              (logT g i j l x + (logA g i l x * logW g j x + logW g i x * logA g j l x)) +
          (logT g i k l x * logW g j x + logA g i k x * logA g j l x +
            (logA g i l x * logA g j k x + logW g i x * logT g j k l x)))) := by
  rw [(isLogJet_log hg hpos).pd_pd_pd_pd_rho i j k l x, mul_div_cancel_left₀ _ (hpos x).ne']
  ring

/-! ### The divergences of the fluxes -/

/-- The divergence term of P1: `∂ᵢ Vᵢ = g · pDFlux1 g i`. -/
theorem pd_fluxP1_eq {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ y, 0 < g y) (i : Fin d)
    (x : E d) : pd (fluxP1 g i) i x = g x * pDFlux1 g i x :=
  ((isLogJet_log hg hpos).pd_fluxP1 i x).trans (by simp only [pDFlux1, pFlux1]; ring)

/-- The divergence term of P2: `∂ₖ Wₖ = g · pDFlux2 g k`. -/
theorem pd_fluxP2_eq {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ y, 0 < g y) (k : Fin d)
    (x : E d) : pd (fluxP2 g k) k x = g x * pDFlux2 g k x :=
  ((isLogJet_log hg hpos).pd_fluxP2 k x).trans (by simp only [pDFlux2, pFlux2, pHess]; ring)

/-- `g K_g = g · pKernel g`. -/
theorem mul_kernelK_eq (g : E d → ℝ) (x : E d) : g x * kernelK g x = g x * pKernel g x := by
  rw [kernelK_eq_log, pKernel]

/-- Differentiability of the flux of P1, for abstract jets. -/
theorem differentiableAt_fluxP1_aux {ρ : E d → ℝ} {w : Fin d → E d → ℝ}
    {A : Fin d → Fin d → E d → ℝ} (hρ : Differentiable ℝ ρ) (hw : ∀ i, Differentiable ℝ (w i))
    (hA : ∀ i j, Differentiable ℝ (A i j)) (i : Fin d) (x : E d) :
    DifferentiableAt ℝ (fun y => ρ y * ((∑ k, w k y ^ 2) * w i y / 2 + ∑ j, A i j y * w j y))
      x := by
  fun_prop

/-- Differentiability of the flux of P2, for abstract jets. -/
theorem differentiableAt_fluxP2_aux {ρ : E d → ℝ} {w : Fin d → E d → ℝ}
    {A : Fin d → Fin d → E d → ℝ} {B : Fin d → Fin d → Fin d → E d → ℝ}
    (hρ : Differentiable ℝ ρ) (hw : ∀ i, Differentiable ℝ (w i))
    (hA : ∀ i j, Differentiable ℝ (A i j)) (hB : ∀ i j k, Differentiable ℝ (B i j k))
    (k : Fin d) (x : E d) :
    DifferentiableAt ℝ (fun y => ρ y * ((∑ i, ∑ j, A i j y ^ 2) * w k y / 2
      + ∑ i, ∑ j, A i j y * B i j k y)) x := by
  fun_prop

/-- The flux of P1 of a smooth positive function is differentiable. -/
theorem differentiableAt_fluxP1 {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ y, 0 < g y)
    (i : Fin d) (x : E d) : DifferentiableAt ℝ (fluxP1 g i) x := by
  have J := isLogJet_log hg hpos
  exact differentiableAt_fluxP1_aux J.diff_rho J.diff_w J.diff_A i x

/-- The flux of P2 of a smooth positive function is differentiable. -/
theorem differentiableAt_fluxP2 {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ y, 0 < g y)
    (k : Fin d) (x : E d) : DifferentiableAt ℝ (fluxP2 g k) x := by
  have J := isLogJet_log hg hpos
  exact differentiableAt_fluxP2_aux J.diff_rho J.diff_w J.diff_A J.diff_T k x

/-! ### Integrals of divergences -/

/-- **Integrals of partial derivatives vanish**: if `V` is differentiable and `V`, `∂ᵢ V` are
integrable, then `∫ ∂ᵢ V = 0` (integration by parts against the constant `1`). -/
theorem integral_pd_eq_zero {V : E d → ℝ} (hV : ∀ x, DifferentiableAt ℝ V x)
    (hVi : Integrable V) (i : Fin d) (hdV : Integrable (pd V i)) : ∫ x, pd V i x = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (E d)))
    (f := fun _ => (1 : ℝ)) (g := V) (v := EuclideanSpace.single i (1 : ℝ))
    (by simp) (by simp only [one_mul]; exact hdV) (by simpa only [one_mul] using hVi)
    (fun x _ => differentiableAt_const _) (fun x _ => hV x)
  simpa [pd] using h

/-! ### Domination along the heat flow -/

section Flow

variable {T c Q : ℝ} {q f : E d → ℝ}

/-- The ratios `∂ˡρ s / ρ s`, `|l| ≤ 4`, are uniformly polynomially bounded on `(0, t₁]`. -/
theorem upoly_ratio (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) {l : List (Fin d)}
    (hl : l.length ≤ 4) :
    UPoly (Set.Ioc 0 t₁) (fun s x => pdList (heat f s) l x / heat f s x) := by
  obtain ⟨K, m, hK⟩ := H.exists_abs_pdList_flow_div_le t₁ hl
  exact ⟨fun s hs => (H.contDiff_pdList_flow hs.1 l).continuous.measurable.fun_div
    (H.contDiff_flow hs.1).continuous.measurable, K, m, hK⟩

/-- The first logarithmic derivatives of the heat flow are uniformly polynomially bounded. -/
theorem upoly_logW (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (i : Fin d) :
    UPoly (Set.Ioc 0 t₁) (fun s x => logW (heat f s) i x) :=
  (upoly_ratio H t₁ (l := [i]) (by simp)).congr fun _ hs x =>
    logW_eq_div (H.flow_pos hs.1) i x

/-- The second logarithmic derivatives of the heat flow are uniformly polynomially bounded. -/
theorem upoly_logA (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (i j : Fin d) :
    UPoly (Set.Ioc 0 t₁) (fun s x => logA (heat f s) i j x) :=
  ((upoly_ratio H t₁ (l := [i, j]) (by simp)).sub
    ((upoly_logW H t₁ i).mul (upoly_logW H t₁ j))).congr fun _ hs x =>
      logA_eq_ratio (H.contDiff_flow hs.1) (H.flow_pos hs.1) i j x

/-- The third logarithmic derivatives of the heat flow are uniformly polynomially bounded. -/
theorem upoly_logT (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (i j k : Fin d) :
    UPoly (Set.Ioc 0 t₁) (fun s x => logT (heat f s) i j k x) := by
  have hw := upoly_logW H t₁
  have hA := upoly_logA H t₁
  exact ((upoly_ratio H t₁ (l := [i, j, k]) (by simp)).sub
    (((hw k).mul ((hA i j).add ((hw i).mul (hw j)))).add
      (((hA i k).mul (hw j)).add ((hw i).mul (hA j k))))).congr fun _ hs x =>
        logT_eq_ratio (H.contDiff_flow hs.1) (H.flow_pos hs.1) i j k x

/-- The fourth logarithmic derivatives of the heat flow are uniformly polynomially bounded. -/
theorem upoly_logQ (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (i j k l : Fin d) :
    UPoly (Set.Ioc 0 t₁) (fun s x => logQ (heat f s) i j k l x) := by
  have hw := upoly_logW H t₁
  have hA := upoly_logA H t₁
  have hT3 := upoly_logT H t₁
  exact ((upoly_ratio H t₁ (l := [i, j, k, l]) (by simp)).sub
    (((hw l).mul (((hw k).mul ((hA i j).add ((hw i).mul (hw j)))).add
        ((hT3 i j k).add (((hA i k).mul (hw j)).add ((hw i).mul (hA j k)))))).add
      ((((hA k l).mul ((hA i j).add ((hw i).mul (hw j)))).add
          ((hw k).mul ((hT3 i j l).add (((hA i l).mul (hw j)).add ((hw i).mul (hA j l)))))).add
        ((((hT3 i k l).mul (hw j)).add ((hA i k).mul (hA j l))).add
          (((hA i l).mul (hA j k)).add ((hw i).mul (hT3 j k l))))))).congr fun _ hs x =>
    logQ_eq_ratio (H.contDiff_flow hs.1) (H.flow_pos hs.1) i j k l x

/-- `|∇ log ρ s|²` is uniformly polynomially bounded. -/
theorem upoly_sq_logW (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    UPoly (Set.Ioc 0 t₁) (fun s x => ∑ i, logW (heat f s) i x ^ 2) :=
  UPoly.sum Finset.univ fun i _ => (upoly_logW H t₁ i).pow 2

/-- The polynomial part of the flux of P1 is uniformly polynomially bounded. -/
theorem upoly_pFlux1 (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (i : Fin d) :
    UPoly (Set.Ioc 0 t₁) (fun s x => pFlux1 (heat f s) i x) := by
  have hw := upoly_logW H t₁
  have hA := upoly_logA H t₁
  exact (((upoly_sq_logW H t₁).mul (hw i)).div_const 2).add
    (UPoly.sum Finset.univ fun j _ => (hA i j).mul (hw j))

/-- The polynomial part of the divergence of the flux of P1 is uniformly polynomially bounded. -/
theorem upoly_pDFlux1 (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (i : Fin d) :
    UPoly (Set.Ioc 0 t₁) (fun s x => pDFlux1 (heat f s) i x) := by
  have hw := upoly_logW H t₁
  have hA := upoly_logA H t₁
  have hT3 := upoly_logT H t₁
  exact ((hw i).mul (upoly_pFlux1 H t₁ i)).add
    ((((UPoly.sum Finset.univ fun k _ => (hw k).mul (hA k i)).mul (hw i)).add
        (((upoly_sq_logW H t₁).mul (hA i i)).div_const 2)).add
      (UPoly.sum Finset.univ fun j _ => ((hT3 i j i).mul (hw j)).add ((hA i j).mul (hA j i))))

/-- `|∇² log ρ s|²` is uniformly polynomially bounded. -/
theorem upoly_pHess (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    UPoly (Set.Ioc 0 t₁) (fun s x => pHess (heat f s) x) := by
  have hA := upoly_logA H t₁
  exact UPoly.sum Finset.univ fun i _ => UPoly.sum Finset.univ fun j _ => (hA i j).pow 2

/-- The polynomial part of the flux of P2 is uniformly polynomially bounded. -/
theorem upoly_pFlux2 (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (k : Fin d) :
    UPoly (Set.Ioc 0 t₁) (fun s x => pFlux2 (heat f s) k x) := by
  have hw := upoly_logW H t₁
  have hA := upoly_logA H t₁
  have hT3 := upoly_logT H t₁
  exact (((upoly_pHess H t₁).mul (hw k)).div_const 2).add
    (UPoly.sum Finset.univ fun i _ => UPoly.sum Finset.univ fun j _ => (hA i j).mul (hT3 i j k))

/-- The polynomial part of the divergence of the flux of P2 is uniformly polynomially bounded. -/
theorem upoly_pDFlux2 (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (k : Fin d) :
    UPoly (Set.Ioc 0 t₁) (fun s x => pDFlux2 (heat f s) k x) := by
  have hw := upoly_logW H t₁
  have hA := upoly_logA H t₁
  have hT3 := upoly_logT H t₁
  have hQ4 := upoly_logQ H t₁
  exact ((hw k).mul (upoly_pFlux2 H t₁ k)).add
    ((((UPoly.sum Finset.univ fun i _ => UPoly.sum Finset.univ fun j _ =>
          (hA i j).mul (hT3 i j k)).mul (hw k)).add
        (((upoly_pHess H t₁).mul (hA k k)).div_const 2)).add
      (UPoly.sum Finset.univ fun i _ => UPoly.sum Finset.univ fun j _ =>
        ((hT3 i j k).pow 2).add ((hA i j).mul (hQ4 i j k k))))

/-- `K_{ρ s}` is uniformly polynomially bounded. -/
theorem upoly_pKernel (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    UPoly (Set.Ioc 0 t₁) (fun s x => pKernel (heat f s) x) := by
  have hA := upoly_logA H t₁
  have hT3 := upoly_logT H t₁
  exact (UPoly.sum Finset.univ fun i _ => UPoly.sum Finset.univ fun j _ =>
      UPoly.sum Finset.univ fun k _ => (hT3 i j k).pow 2).sub
    ((UPoly.const (Set.Ioc 0 t₁) 2).mul (UPoly.sum Finset.univ fun i _ =>
      UPoly.sum Finset.univ fun j _ => UPoly.sum Finset.univ fun k _ =>
        ((hA i j).mul (hA j k)).mul (hA k i)))

/-- **From polynomial bounds to Gaussian domination**: if `G` is uniformly polynomially bounded
on `(0, t₁]`, then `ρ s G s` is dominated by `C (1 + ‖x‖)^m γ_{T+t₁}(x)` on `(0, t₁]`. -/
theorem dom_of_upoly (H : DensityFlowHyp d T c Q q f) {t₁ : ℝ} {F G : ℝ → E d → ℝ}
    (hG : UPoly (Set.Ioc 0 t₁) G)
    (hF : ∀ s ∈ Set.Ioc 0 t₁, ∀ x, F s x = heat f s x * G s x) : Dom T t₁ F := by
  obtain ⟨hGm, K, m, hK⟩ := hG
  refine ⟨fun s hs => ?_, c * Q * ((T + t₁) / T) ^ ((d : ℝ) / 2) * K, m, fun s hs x => ?_⟩
  · rw [show F s = fun x => heat f s x * G s x from funext (hF s hs)]
    exact (H.contDiff_flow hs.1).continuous.measurable.fun_mul (hGm s hs)
  · have hρ := H.flow_pos hs.1 x
    have h1 := H.flow_le_mul_gaussian hs.1 x
    have h2 := gaussian_add_le_mul_gaussian_add H.hT hs.1.le hs.2 x
    have h3 := hK s hs x
    have hcQ : 0 ≤ c * Q := mul_nonneg H.hc.le (zero_le_one.trans H.one_le_Q)
    have hr : 0 ≤ ((T + t₁) / T) ^ ((d : ℝ) / 2) :=
      Real.rpow_nonneg (div_nonneg (by linarith [H.hT, hs.1, hs.2]) H.hT.le) _
    have hγ : 0 ≤ gaussian d (T + t₁) x :=
      (gaussian_pos (by linarith [H.hT, hs.1, hs.2]) x).le
    rw [hF s hs x, abs_mul, abs_of_pos hρ]
    calc heat f s x * |G s x|
        ≤ c * Q * (((T + t₁) / T) ^ ((d : ℝ) / 2) * gaussian d (T + t₁) x) *
            (K * (1 + ‖x‖) ^ m) :=
          mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hcQ)) h3 (abs_nonneg _)
            (mul_nonneg hcQ (mul_nonneg hr hγ))
      _ = c * Q * ((T + t₁) / T) ^ ((d : ℝ) / 2) * K * (1 + ‖x‖) ^ m *
            gaussian d (T + t₁) x := by ring

/-- Domination of the Fisher integrand `ρ |∇ log ρ|²`. -/
theorem dom_fisherDensity (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    Dom T t₁ (fun s => fisherDensity (heat f s)) :=
  dom_of_upoly H (upoly_sq_logW H t₁) fun _ _ _ => rfl

/-- Domination of the flux of P1. -/
theorem dom_fluxP1 (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (i : Fin d) :
    Dom T t₁ (fun s => fluxP1 (heat f s) i) :=
  dom_of_upoly H (upoly_pFlux1 H t₁ i) fun _ _ _ => rfl

/-- Domination of the divergence terms of P1. -/
theorem dom_pd_fluxP1 (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (i : Fin d) :
    Dom T t₁ (fun s => pd (fluxP1 (heat f s) i) i) :=
  dom_of_upoly H (upoly_pDFlux1 H t₁ i) fun _ hs x =>
    pd_fluxP1_eq (H.contDiff_flow hs.1) (H.flow_pos hs.1) i x

/-- Domination of `ρ |∇² log ρ|²`. -/
theorem dom_hessDensity (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    Dom T t₁ (fun s => hessDensity (heat f s)) :=
  dom_of_upoly H (upoly_pHess H t₁) fun _ _ _ => rfl

/-- Domination of the flux of P2. -/
theorem dom_fluxP2 (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (k : Fin d) :
    Dom T t₁ (fun s => fluxP2 (heat f s) k) :=
  dom_of_upoly H (upoly_pFlux2 H t₁ k) fun _ _ _ => rfl

/-- Domination of the divergence terms of P2. -/
theorem dom_pd_fluxP2 (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) (k : Fin d) :
    Dom T t₁ (fun s => pd (fluxP2 (heat f s) k) k) :=
  dom_of_upoly H (upoly_pDFlux2 H t₁ k) fun _ hs x =>
    pd_fluxP2_eq (H.contDiff_flow hs.1) (H.flow_pos hs.1) k x

/-- Domination of `ρ K_ρ`. -/
theorem dom_mul_kernelK (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    Dom T t₁ (fun s x => heat f s x * kernelK (heat f s) x) :=
  dom_of_upoly H (upoly_pKernel H t₁) fun s _ x => mul_kernelK_eq (heat f s) x

/-- Domination of the time derivative of the Fisher integrand. -/
theorem dom_dFisherDensity (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    Dom T t₁ (fun s => dFisherDensity (heat f s)) :=
  ((Dom.sum H.hT.le Finset.univ fun i _ => dom_pd_fluxP1 H t₁ i).sub H.hT.le
    (dom_hessDensity H t₁)).congr fun _ _ _ => rfl

/-- Domination of the time derivative of `ρ |∇² log ρ|²`. -/
theorem dom_dHessDensity (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    Dom T t₁ (fun s => dHessDensity (heat f s)) :=
  ((Dom.sum H.hT.le Finset.univ fun k _ => dom_pd_fluxP2 H t₁ k).sub H.hT.le
    (dom_mul_kernelK H t₁)).congr fun _ _ _ => rfl

/-! ### Pointwise time derivatives -/

/-- The heat flow stays positive near a positive time. -/
theorem eventually_flow_pos (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ r in 𝓝 s, ∀ y, 0 < heat f r y := by
  filter_upwards [lt_mem_nhds hs] with r hr using H.flow_pos hr

/-- The heat flow is `C²` near a positive time. -/
theorem eventually_contDiffAt_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s)
    (x : E d) : ∀ᶠ r in 𝓝 s, ContDiffAt ℝ 2 (heat f r) x := by
  filter_upwards [lt_mem_nhds hs] with r hr using
    (contDiff_infty.1 (H.contDiff_flow hr) 2).contDiffAt

/-- P1 along the heat flow: `∂ₛ (ρ |∇ log ρ|²) = Σᵢ ∂ᵢ Vᵢ - ρ |∇² log ρ|²`. -/
theorem hasDerivAt_fisherDensity_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s)
    (x : E d) :
    HasDerivAt (fun r => fisherDensity (heat f r) x) (dFisherDensity (heat f s) x) s :=
  Identities.hasDerivAt_fisher_aux (ρ := heat f) (x := x) (eventually_flow_pos H hs)
    (H.contDiff_flow hs) (H.hasDerivAt_flow hs x) (fun i => H.hasDerivAt_pd_flow hs i x)

/-- P2 along the heat flow: `∂ₛ (ρ |∇² log ρ|²) = Σₖ ∂ₖ Wₖ - ρ K_ρ`. -/
theorem hasDerivAt_hessDensity_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s)
    (x : E d) :
    HasDerivAt (fun r => hessDensity (heat f r) x) (dHessDensity (heat f s) x) s :=
  Identities.hasDerivAt_hess_aux (ρ := heat f) (x := x) (eventually_flow_pos H hs)
    (eventually_contDiffAt_flow H hs x) (H.contDiff_flow hs) (H.hasDerivAt_flow hs x)
    (fun i => H.hasDerivAt_pd_flow hs i x) (fun i j => H.hasDerivAt_pd_pd_flow hs i j x)

/-! ### Differentiation under the integral sign -/

/-- **Differentiation under the integral sign along the heat flow**: if `F` and `F'` are
dominated on `(0, 2t]` and `∂ₛ F s x = F' s x` for all `s > 0`, then
`∂ₛ ∫ F s = ∫ F' t` at `t > 0`. -/
theorem hasDerivAt_integral_of_dom (H : DensityFlowHyp d T c Q q f) {F F' : ℝ → E d → ℝ}
    {t : ℝ} (ht : 0 < t) (hF : Dom T (2 * t) F) (hF' : Dom T (2 * t) F')
    (hd : ∀ s, 0 < s → ∀ x, HasDerivAt (fun r => F r x) (F' s x) s) :
    HasDerivAt (fun s => ∫ x, F s x) (∫ x, F' t x) t := by
  obtain ⟨hm, C, m, hC⟩ := hF'
  have h2t : t < 2 * t := by linarith
  have hS : Set.Ioo 0 (2 * t) ∈ 𝓝 t := Ioo_mem_nhds ht h2t
  have htS : t ∈ Set.Ioc 0 (2 * t) := ⟨ht, h2t.le⟩
  have hTt : 0 < T + 2 * t := by linarith [H.hT]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (bound := fun x => C * ((1 + ‖x‖) ^ m * gaussian d (T + 2 * t) x)) hS
    (Filter.eventually_of_mem hS fun s hs => (hF.1 s ⟨hs.1, hs.2.le⟩).aestronglyMeasurable)
    (hF.integrable H.hT htS) (hm t htS).aestronglyMeasurable
    (ae_of_all _ fun x s hs => (Real.norm_eq_abs _).trans_le
      ((hC s ⟨hs.1, hs.2.le⟩ x).trans_eq (mul_assoc _ _ _)))
    ((integrable_one_add_norm_pow_mul_gaussian m hTt).const_mul C)
    (ae_of_all _ fun x s hs => hd s hs.1 x)).2

/-! ### Integrating the divergence identities -/

/-- `∫ (Σᵢ ∂ᵢ Vᵢ - ρ |∇² log ρ|²) = -∫ ρ |∇² log ρ|²` at positive times. -/
theorem integral_dFisherDensity (H : DensityFlowHyp d T c Q q f) {t : ℝ} (ht : 0 < t) :
    ∫ x, dFisherDensity (heat f t) x =
      -∫ x, heat f t x * ∑ i, ∑ j, (pd (pd (fun z => Real.log (heat f t z)) i) j x) ^ 2 := by
  have htS : t ∈ Set.Ioc 0 t := Set.right_mem_Ioc.2 ht
  have hdV : ∀ i, Integrable (pd (fluxP1 (heat f t) i) i) := fun i =>
    (dom_pd_fluxP1 H t i).integrable H.hT htS
  have hzero : ∀ i, ∫ x, pd (fluxP1 (heat f t) i) i x = 0 := fun i =>
    integral_pd_eq_zero
      (fun x => differentiableAt_fluxP1 (H.contDiff_flow ht) (H.flow_pos ht) i x)
      ((dom_fluxP1 H t i).integrable H.hT htS) i (hdV i)
  have hA : Integrable (hessDensity (heat f t)) := (dom_hessDensity H t).integrable H.hT htS
  calc ∫ x, dFisherDensity (heat f t) x
      = ∫ x, ((∑ i, pd (fluxP1 (heat f t) i) i x) - hessDensity (heat f t) x) := rfl
    _ = (∑ i, ∫ x, pd (fluxP1 (heat f t) i) i x) - ∫ x, hessDensity (heat f t) x := by
        rw [integral_sub (integrable_finsetSum Finset.univ fun i _ => hdV i) hA,
          integral_finsetSum Finset.univ fun i _ => hdV i]
    _ = -∫ x, heat f t x * ∑ i, ∑ j, (pd (pd (fun z => Real.log (heat f t z)) i) j x) ^ 2 := by
        simp only [hzero, Finset.sum_const_zero, zero_sub]
        rfl

/-- `∫ (Σₖ ∂ₖ Wₖ - ρ K_ρ) = -D(ρ)` at positive times. -/
theorem integral_dHessDensity (H : DensityFlowHyp d T c Q q f) {t : ℝ} (ht : 0 < t) :
    ∫ x, dHessDensity (heat f t) x = -Dfun (heat f t) := by
  have htS : t ∈ Set.Ioc 0 t := Set.right_mem_Ioc.2 ht
  have hdW : ∀ k, Integrable (pd (fluxP2 (heat f t) k) k) := fun k =>
    (dom_pd_fluxP2 H t k).integrable H.hT htS
  have hzero : ∀ k, ∫ x, pd (fluxP2 (heat f t) k) k x = 0 := fun k =>
    integral_pd_eq_zero
      (fun x => differentiableAt_fluxP2 (H.contDiff_flow ht) (H.flow_pos ht) k x)
      ((dom_fluxP2 H t k).integrable H.hT htS) k (hdW k)
  have hK : Integrable (fun x => heat f t x * kernelK (heat f t) x) :=
    (dom_mul_kernelK H t).integrable H.hT htS
  calc ∫ x, dHessDensity (heat f t) x
      = ∫ x, ((∑ k, pd (fluxP2 (heat f t) k) k x) - heat f t x * kernelK (heat f t) x) := rfl
    _ = (∑ k, ∫ x, pd (fluxP2 (heat f t) k) k x) - ∫ x, heat f t x * kernelK (heat f t) x := by
        rw [integral_sub (integrable_finsetSum Finset.univ fun k _ => hdW k) hK,
          integral_finsetSum Finset.univ fun k _ => hdW k]
    _ = -Dfun (heat f t) := by
        simp only [hzero, Finset.sum_const_zero, zero_sub]
        rfl

end Flow

end Derivatives

/-! ### Main results -/

namespace DensityFlowHyp

open Derivatives

variable {d : ℕ} {T c Q : ℝ} {q f : E d → ℝ}

/-- The Fisher integrand `ρ |∇ log ρ|²` of the heat flow `ρ = heat f` is integrable at every
positive time. -/
theorem integrable_fisherDensity_flow (H : DensityFlowHyp d T c Q q f) {t : ℝ} (ht : 0 < t) :
    Integrable (fisherDensity (heat f t)) :=
  (dom_fisherDensity H t).integrable H.hT (Set.right_mem_Ioc.2 ht)

/-- The integrand `ρ |∇² log ρ|²` of the heat flow `ρ = heat f` is integrable at every positive
time. -/
theorem integrable_hessDensity_flow (H : DensityFlowHyp d T c Q q f) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => heat f t x *
      ∑ i, ∑ j, (pd (pd (fun z => Real.log (heat f t z)) i) j x) ^ 2) :=
  (dom_hessDensity H t).integrable H.hT (Set.right_mem_Ioc.2 ht)

/-- The integrand `ρ K_ρ` of `Dfun` along the heat flow `ρ = heat f` is integrable at every
positive time. -/
theorem integrable_mul_kernelK_flow (H : DensityFlowHyp d T c Q q f) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => heat f t x * kernelK (heat f t) x) :=
  (dom_mul_kernelK H t).integrable H.hT (Set.right_mem_Ioc.2 ht)

/-- **`I' = -Q`**: along the heat flow `ρ = heat f`, the Fisher information has derivative
`-∫ ρ t |∇² log ρ t|²` at every positive time `t`. -/
theorem hasDerivAt_fisher_flow (H : DensityFlowHyp d T c Q q f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => fisher (heat f s))
      (-∫ x, heat f t x * ∑ i, ∑ j, (pd (pd (fun z => Real.log (heat f t z)) i) j x) ^ 2) t :=
  (hasDerivAt_integral_of_dom H ht (dom_fisherDensity H (2 * t)) (dom_dFisherDensity H (2 * t))
    fun _ hs x => hasDerivAt_fisherDensity_flow H hs x).congr_deriv
    (integral_dFisherDensity H ht)

/-- **`Q' = -D`**: along the heat flow `ρ = heat f`, `Q(s) = ∫ ρ s |∇² log ρ s|²` has derivative
`-Dfun (ρ t)` at every positive time `t`. -/
theorem hasDerivAt_hessFisher_flow (H : DensityFlowHyp d T c Q q f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => ∫ x, heat f s x * ∑ i, ∑ j, (pd (pd (fun z => Real.log (heat f s z)) i) j x) ^ 2)
      (-Dfun (heat f t)) t :=
  (hasDerivAt_integral_of_dom H ht (dom_hessDensity H (2 * t)) (dom_dHessDensity H (2 * t))
    fun _ hs x => hasDerivAt_hessDensity_flow H hs x).congr_deriv
    (integral_dHessDensity H ht)

end DensityFlowHyp

end Fisher41
