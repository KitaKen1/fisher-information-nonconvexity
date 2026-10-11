/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Heat.DensityFlow
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The heat flow at the initial time

For a density `f` satisfying the standing hypotheses `Fisher41.DensityFlowHyp d T c Q q f`
(`f = c q γ_T`), this file shows that the heat flow `ρ s = heat f s`, its derivatives of order at
most `4`, and the functional `D(ρ) = ∫ ρ K_ρ` are continuous at the initial time `s = 0⁺`. It
also records the elementary criterion by which a negative second derivative near `0` rules out
convexity.

## Main results

* `Fisher41.tendsto_heat_nhdsGT_zero`: for a continuous bounded `g`, `heat g s x → g x` as
  `s → 0⁺` (Tau Ceti's `TauCeti.tendsto_heatKernel_convolution`, since
  `heat g s = K_{s/2} ⋆ g`).
* `Fisher41.DensityFlowHyp.tendsto_pdList_flow`: `∂ˡ(heat f s)(x) → ∂ˡf(x)` for `|l| ≤ 4`.
* `Fisher41.Limit.pd_log`, `Fisher41.Limit.pd_pd_log`, `Fisher41.Limit.negHess_eq`,
  `Fisher41.Limit.pd_negHess_eq`: the derivatives of `log ρ` of order at most three in terms of
  those of `ρ` (quotient rule).
* `Fisher41.Limit.kernelK_eq`, `Fisher41.Limit.continuousOn_kernelJet`: `K_ρ(x)` is an explicit
  function `Fisher41.Limit.kernelJet` of the `3`-jet `(ρ, ∂ρ, ∂²ρ, ∂³ρ)(x)`, continuous where
  `ρ(x) ≠ 0`.
* `Fisher41.DensityFlowHyp.tendsto_Dfun_flow`: `D(heat f s) → D(f)` as `s → 0⁺`.
* `Fisher41.DensityFlowHyp.exists_Dfun_flow_neg`: if `D(f) < 0`, then `D(heat f s) < 0` for all
  `s ∈ (0, ε)`.
* `Fisher41.not_convexOn_Ioi_of_deriv2_neg`: a function with a negative second derivative on
  some interval `(0, ε)` is not convex on `(0, ∞)`.

## Implementation notes

`K_ρ` is written through the ratios `∂ˡρ / ρ`, `|l| ≤ 3` (`Fisher41.Limit.kernelR`). Along the
heat flow these ratios have polynomial growth uniformly in `s ∈ (0, 1]`
(`Fisher41.DensityFlowHyp.exists_abs_pdList_flow_div_le`); the closure properties of
`Fisher41.Limit.UPoly` propagate this to `K_{ρ s}`. Together with the Gaussian bound
`ρ s ≤ c Q γ_{T+s} ≤ c Q ((T + 1)/T)^(d/2) γ_{T+1}`, this dominates `ρ s K_{ρ s}` by
`C (1 + ‖x‖)^m γ_{T+1}(x)` for `s ∈ (0, 1]`, and dominated convergence applies.

Partial derivatives of composite expressions are computed along coordinate lines
(`Fisher41.Limit.hasDerivAt_line`), where Mathlib's one-variable rules apply; quotients are
written with `⁻¹`, so that the resulting identities are proved by `ring` alone.
-/

open MeasureTheory Real Filter Topology
open scoped ContDiff Convolution

noncomputable section

namespace Fisher41

variable {d : ℕ}

/-! ### Initial values of the heat flow -/

/-- **Initial values of the heat flow**: if `g` is continuous and bounded, then
`heat g s x → g x` as `s → 0⁺`. -/
theorem tendsto_heat_nhdsGT_zero {g : E d → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) (x : E d) :
    Tendsto (fun s => heat g s x) (𝓝[>] 0) (𝓝 (g x)) := by
  have hK := TauCeti.tendsto_heatKernel_convolution (E := E d) (x₀ := x) (M := M)
    hg.aestronglyMeasurable (ae_of_all _ fun y => (Real.norm_eq_abs (g y)).trans_le (hM y))
    hg.continuousAt
  have h₂ : Tendsto (fun s : ℝ => s / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_id.div_const (2 : ℝ)).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s) using half_pos hs
  refine (hK.comp (h₂.prodMk tendsto_const_nhds)).congr fun s => ?_
  exact (heat_eq_convolution g s x).symm

namespace Limit

/-! ### Partial derivatives along coordinate lines -/

/-- Along the coordinate line `t ↦ x + t • eₖ`, a function differentiable at `x` has derivative
`∂ₖ g x` at `t = 0`. -/
theorem hasDerivAt_line {g : E d → ℝ} {x : E d} (hg : DifferentiableAt ℝ g x) (k : Fin d) :
    HasDerivAt (fun t : ℝ => g (x + t • EuclideanSpace.single k (1 : ℝ))) (pd g k x) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single k (1 : ℝ))
      (EuclideanSpace.single k (1 : ℝ)) 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).smul_const
      (EuclideanSpace.single k (1 : ℝ) : E d)).const_add x
    rwa [one_smul] at h
  exact hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

/-- A partial derivative of a function differentiable at `x` is its derivative along the
coordinate line through `x`. -/
theorem pd_eq_of_hasDerivAt {g : E d → ℝ} {x : E d} (hg : DifferentiableAt ℝ g x) {k : Fin d}
    {a : ℝ} (h : HasDerivAt (fun t : ℝ => g (x + t • EuclideanSpace.single k (1 : ℝ))) a 0) :
    pd g k x = a :=
  (hasDerivAt_line hg k).unique h

/-! ### Logarithmic derivatives -/

/-- **The logarithmic derivative**: `∂ᵢ log ρ = ∂ᵢρ / ρ`. -/
theorem pd_log {ρ : E d → ℝ} {x : E d} (hρ : DifferentiableAt ℝ ρ x) (hx : ρ x ≠ 0)
    (i : Fin d) : pd (fun y => Real.log (ρ y)) i x = pd ρ i x / ρ x := by
  have hx' : ρ (x + (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) ≠ 0 := by
    rwa [zero_smul, add_zero]
  have h := (hasDerivAt_line hρ i).log hx'
  simp only [zero_smul, add_zero] at h
  exact pd_eq_of_hasDerivAt (hρ.log hx) h

/-- **Second logarithmic derivatives**: `∂ⱼ∂ᵢ log ρ = ∂ⱼ∂ᵢρ / ρ - ∂ᵢρ ∂ⱼρ / ρ²`. -/
theorem pd_pd_log {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ y, 0 < ρ y) (i j : Fin d)
    (x : E d) :
    pd (pd (fun y => Real.log (ρ y)) i) j x =
      pd (pd ρ i) j x / ρ x - pd ρ i x * pd ρ j x / ρ x ^ 2 := by
  have hne : ∀ y, ρ y ≠ 0 := fun y => (hpos y).ne'
  have hd : Differentiable ℝ ρ := DensityFlow.differentiable_of_contDiff hρ
  have hdi : Differentiable ℝ (pd ρ i) :=
    DensityFlow.differentiable_of_contDiff (DensityFlow.contDiff_pd hρ i)
  have h₁ : pd (fun y => Real.log (ρ y)) i = fun y => pd ρ i y * (ρ y)⁻¹ := by
    funext y
    rw [pd_log (hd y) (hne y) i, div_eq_mul_inv]
  have hG : Differentiable ℝ (pd (fun y => Real.log (ρ y)) i) :=
    DensityFlow.differentiable_of_contDiff (DensityFlow.contDiff_pd (hρ.log hne) i)
  rw [h₁] at hG
  have hx' : ρ (x + (0 : ℝ) • EuclideanSpace.single j (1 : ℝ)) ≠ 0 := by
    rw [zero_smul, add_zero]
    exact hne x
  have h := (hasDerivAt_line (hdi x) j).fun_mul ((hasDerivAt_line (hd x) j).fun_inv hx')
  simp only [zero_smul, add_zero] at h
  rw [h₁, pd_eq_of_hasDerivAt (hG x) h]
  ring

/-- `Hᵢⱼ = -∂ⱼ∂ᵢ log ρ = -(∂ⱼ∂ᵢρ / ρ - ∂ᵢρ ∂ⱼρ / ρ²)`. -/
theorem negHess_eq {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ y, 0 < ρ y) (i j : Fin d)
    (x : E d) :
    negHess ρ i j x = -(pd (pd ρ i) j x / ρ x - pd ρ i x * pd ρ j x / ρ x ^ 2) := by
  rw [negHess, pd_pd_log hρ hpos i j x]

/-- `Hᵢⱼ` as a function, in the form `(∂ᵢρ ρ⁻¹)(∂ⱼρ ρ⁻¹) - ∂ⱼ∂ᵢρ ρ⁻¹` used to differentiate it
once more. -/
theorem negHess_eq_fun {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ y, 0 < ρ y)
    (i j : Fin d) :
    negHess ρ i j = fun y =>
      pd ρ i y * (ρ y)⁻¹ * (pd ρ j y * (ρ y)⁻¹) - pd (pd ρ i) j y * (ρ y)⁻¹ := by
  funext y
  rw [negHess_eq hρ hpos i j y]
  ring

/-! ### The kernel `K` as a function of the `3`-jet -/

/-- `Hᵢⱼ` in terms of the ratios `a i = ∂ᵢρ / ρ` and `b i j = ∂ⱼ∂ᵢρ / ρ`. -/
def hessR (a : Fin d → ℝ) (b : Fin d → Fin d → ℝ) (i j : Fin d) : ℝ :=
  a i * a j - b i j

/-- `∂ₖHᵢⱼ` in terms of the ratios `a i = ∂ᵢρ / ρ`, `b i j = ∂ⱼ∂ᵢρ / ρ` and
`c i j k = ∂ₖ∂ⱼ∂ᵢρ / ρ`. -/
def dhessR (a : Fin d → ℝ) (b : Fin d → Fin d → ℝ) (c : Fin d → Fin d → Fin d → ℝ)
    (i j k : Fin d) : ℝ :=
  b i j * a k + b i k * a j + a i * b j k - 2 * a i * a j * a k - c i j k

/-- `K_ρ` in terms of the ratios `a i = ∂ᵢρ / ρ`, `b i j = ∂ⱼ∂ᵢρ / ρ` and
`c i j k = ∂ₖ∂ⱼ∂ᵢρ / ρ`. -/
def kernelR (a : Fin d → ℝ) (b : Fin d → Fin d → ℝ) (c : Fin d → Fin d → Fin d → ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ k, dhessR a b c i j k ^ 2) +
    2 * ∑ i, ∑ j, ∑ k, hessR a b i j * hessR a b j k * hessR a b k i

/-- `K_ρ(x)` as a function of the `3`-jet `(r, g, h, t) = (ρ, ∂ρ, ∂²ρ, ∂³ρ)(x)`, with
`g i = ∂ᵢρ(x)`, `h i j = ∂ⱼ∂ᵢρ(x)` and `t i j k = ∂ₖ∂ⱼ∂ᵢρ(x)`. -/
def kernelJet (r : ℝ) (g : Fin d → ℝ) (h : Fin d → Fin d → ℝ)
    (t : Fin d → Fin d → Fin d → ℝ) : ℝ :=
  kernelR (fun i => g i / r) (fun i j => h i j / r) (fun i j k => t i j k / r)

/-- The space of `3`-jets `(ρ, ∂ρ, ∂²ρ, ∂³ρ)(x)` of a function on `E d` at a point. -/
abbrev Jet (d : ℕ) : Type :=
  ℝ × (Fin d → ℝ) × (Fin d → Fin d → ℝ) × (Fin d → Fin d → Fin d → ℝ)

/-- `Hᵢⱼ` in terms of the ratios `∂ˡρ / ρ`. -/
theorem negHess_eq_hessR {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ y, 0 < ρ y)
    (i j : Fin d) (x : E d) :
    negHess ρ i j x =
      hessR (fun i => pd ρ i x / ρ x) (fun i j => pd (pd ρ i) j x / ρ x) i j := by
  rw [negHess_eq hρ hpos i j x]
  simp only [hessR]
  ring

/-- `∂ₖHᵢⱼ` in terms of the ratios `∂ˡρ / ρ`. -/
theorem pd_negHess_eq_dhessR {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ y, 0 < ρ y)
    (i j k : Fin d) (x : E d) :
    pd (negHess ρ i j) k x =
      dhessR (fun i => pd ρ i x / ρ x) (fun i j => pd (pd ρ i) j x / ρ x)
        (fun i j k => pd (pd (pd ρ i) j) k x / ρ x) i j k := by
  have hne : ∀ y, ρ y ≠ 0 := fun y => (hpos y).ne'
  have hρi := DensityFlow.contDiff_pd hρ i
  have hρj := DensityFlow.contDiff_pd hρ j
  have hρij := DensityFlow.contDiff_pd hρi j
  have hG : Differentiable ℝ (negHess ρ i j) :=
    DensityFlow.differentiable_of_contDiff
      (DensityFlow.contDiff_pd (DensityFlow.contDiff_pd (hρ.log hne) i) j).neg
  rw [negHess_eq_fun hρ hpos i j] at hG
  have hx' : ρ (x + (0 : ℝ) • EuclideanSpace.single k (1 : ℝ)) ≠ 0 := by
    rw [zero_smul, add_zero]
    exact hne x
  have hR := (hasDerivAt_line (DensityFlow.differentiable_of_contDiff hρ x) k).fun_inv hx'
  have hI := hasDerivAt_line (DensityFlow.differentiable_of_contDiff hρi x) k
  have hJ := hasDerivAt_line (DensityFlow.differentiable_of_contDiff hρj x) k
  have hIJ := hasDerivAt_line (DensityFlow.differentiable_of_contDiff hρij x) k
  have h := ((hI.fun_mul hR).fun_mul (hJ.fun_mul hR)).fun_sub (hIJ.fun_mul hR)
  simp only [zero_smul, add_zero] at h
  rw [negHess_eq_fun hρ hpos i j, pd_eq_of_hasDerivAt (hG x) h]
  simp only [dhessR]
  ring

/-- **Third logarithmic derivatives**: `∂ₖHᵢⱼ = -∂ₖ∂ⱼ∂ᵢ log ρ` is
`-(∂ₖ∂ⱼ∂ᵢρ / ρ - ∂ⱼ∂ᵢρ ∂ₖρ / ρ² - (∂ₖ∂ᵢρ ∂ⱼρ + ∂ᵢρ ∂ₖ∂ⱼρ) / ρ² + 2 ∂ᵢρ ∂ⱼρ ∂ₖρ / ρ³)`. -/
theorem pd_negHess_eq {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ y, 0 < ρ y)
    (i j k : Fin d) (x : E d) :
    pd (negHess ρ i j) k x =
      -(pd (pd (pd ρ i) j) k x / ρ x - pd (pd ρ i) j x * pd ρ k x / ρ x ^ 2 -
        (pd (pd ρ i) k x * pd ρ j x + pd ρ i x * pd (pd ρ j) k x) / ρ x ^ 2 +
        2 * pd ρ i x * pd ρ j x * pd ρ k x / ρ x ^ 3) := by
  rw [pd_negHess_eq_dhessR hρ hpos i j k x]
  simp only [dhessR]
  ring

/-- **The kernel as a function of the `3`-jet**: for a smooth positive `ρ`,
`K_ρ(x) = kernelJet (ρ x) (∂ρ x) (∂²ρ x) (∂³ρ x)`. -/
theorem kernelK_eq {ρ : E d → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ y, 0 < ρ y) (x : E d) :
    kernelK ρ x = kernelJet (ρ x) (fun i => pd ρ i x) (fun i j => pd (pd ρ i) j x)
      (fun i j k => pd (pd (pd ρ i) j) k x) := by
  simp only [kernelK, kernelJet, kernelR, negHess_eq_hessR hρ hpos,
    pd_negHess_eq_dhessR hρ hpos]

/-- Limits of `kernelR`: it is a polynomial in the ratios. -/
theorem tendsto_kernelR {α : Type*} {l : Filter α} {a : α → Fin d → ℝ}
    {b : α → Fin d → Fin d → ℝ} {c : α → Fin d → Fin d → Fin d → ℝ} {a₀ : Fin d → ℝ}
    {b₀ : Fin d → Fin d → ℝ} {c₀ : Fin d → Fin d → Fin d → ℝ}
    (ha : ∀ i, Tendsto (fun s => a s i) l (𝓝 (a₀ i)))
    (hb : ∀ i j, Tendsto (fun s => b s i j) l (𝓝 (b₀ i j)))
    (hc : ∀ i j k, Tendsto (fun s => c s i j k) l (𝓝 (c₀ i j k))) :
    Tendsto (fun s => kernelR (a s) (b s) (c s)) l (𝓝 (kernelR a₀ b₀ c₀)) := by
  have hH : ∀ i j, Tendsto (fun s => hessR (a s) (b s) i j) l (𝓝 (hessR a₀ b₀ i j)) :=
    fun i j => ((ha i).mul (ha j)).sub (hb i j)
  have hD : ∀ i j k, Tendsto (fun s => dhessR (a s) (b s) (c s) i j k) l
      (𝓝 (dhessR a₀ b₀ c₀ i j k)) := fun i j k =>
    (((((hb i j).mul (ha k)).add ((hb i k).mul (ha j))).add ((ha i).mul (hb j k))).sub
      ((((ha i).const_mul 2).mul (ha j)).mul (ha k))).sub (hc i j k)
  have h₁ : Tendsto (fun s => ∑ i, ∑ j, ∑ k, dhessR (a s) (b s) (c s) i j k ^ 2) l
      (𝓝 (∑ i, ∑ j, ∑ k, dhessR a₀ b₀ c₀ i j k ^ 2)) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      tendsto_finsetSum _ fun k _ => (hD i j k).pow 2
  have h₂ : Tendsto (fun s => ∑ i, ∑ j, ∑ k,
      hessR (a s) (b s) i j * hessR (a s) (b s) j k * hessR (a s) (b s) k i) l
      (𝓝 (∑ i, ∑ j, ∑ k, hessR a₀ b₀ i j * hessR a₀ b₀ j k * hessR a₀ b₀ k i)) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      tendsto_finsetSum _ fun k _ => ((hH i j).mul (hH j k)).mul (hH k i)
  exact h₁.add (h₂.const_mul 2)

/-- Limits of `kernelJet` at jets with `r ≠ 0`. -/
theorem tendsto_kernelJet {α : Type*} {l : Filter α} {r : α → ℝ} {g : α → Fin d → ℝ}
    {h : α → Fin d → Fin d → ℝ} {t : α → Fin d → Fin d → Fin d → ℝ} {r₀ : ℝ}
    {g₀ : Fin d → ℝ} {h₀ : Fin d → Fin d → ℝ} {t₀ : Fin d → Fin d → Fin d → ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (hr₀ : r₀ ≠ 0) (hg : ∀ i, Tendsto (fun s => g s i) l (𝓝 (g₀ i)))
    (hh : ∀ i j, Tendsto (fun s => h s i j) l (𝓝 (h₀ i j)))
    (ht : ∀ i j k, Tendsto (fun s => t s i j k) l (𝓝 (t₀ i j k))) :
    Tendsto (fun s => kernelJet (r s) (g s) (h s) (t s)) l (𝓝 (kernelJet r₀ g₀ h₀ t₀)) :=
  tendsto_kernelR (a := fun s i => g s i / r s) (b := fun s i j => h s i j / r s)
    (c := fun s i j k => t s i j k / r s) (fun i => (hg i).div hr hr₀)
    (fun i j => (hh i j).div hr hr₀) (fun i j k => (ht i j k).div hr hr₀)

/-- **Continuity of the kernel in the jet**: `kernelJet` is continuous on the jets with
`r ≠ 0`, in particular on those with `r > 0`. -/
theorem continuousOn_kernelJet :
    ContinuousOn (fun p : Jet d => kernelJet p.1 p.2.1 p.2.2.1 p.2.2.2) {p | p.1 ≠ 0} :=
  fun p hp => ContinuousAt.continuousWithinAt <|
    tendsto_kernelJet (continuous_fst.tendsto p) hp
      (fun i => (show Continuous fun q : Jet d => q.2.1 i by fun_prop).tendsto p)
      (fun i j => (show Continuous fun q : Jet d => q.2.2.1 i j by fun_prop).tendsto p)
      (fun i j k => (show Continuous fun q : Jet d => q.2.2.2 i j k by fun_prop).tendsto p)

/-! ### Uniform polynomial growth -/

/-- `UPoly F`: the functions `F s` have polynomial growth, uniformly in `s ∈ (0, 1]`. -/
def UPoly (F : ℝ → E d → ℝ) : Prop :=
  ∃ K : ℝ, ∃ m : ℕ, ∀ s ∈ Set.Ioc (0 : ℝ) 1, ∀ x, |F s x| ≤ K * (1 + ‖x‖) ^ m

namespace UPoly

variable {F G : ℝ → E d → ℝ}

/-- `UPoly` only depends on the values for `s ∈ (0, 1]`. -/
theorem congr (hF : UPoly F) (hFG : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ∀ x, F s x = G s x) :
    UPoly G := by
  obtain ⟨K, m, h⟩ := hF
  exact ⟨K, m, fun s hs x => by rw [← hFG s hs x]; exact h s hs x⟩

/-- Constants have uniform polynomial growth. -/
theorem const (a : ℝ) : UPoly (fun (_ : ℝ) (_ : E d) => a) :=
  ⟨|a|, 0, fun _ _ x => by simp⟩

/-- Sums of families of uniform polynomial growth. -/
theorem add (hF : UPoly F) (hG : UPoly G) : UPoly (fun s x => F s x + G s x) := by
  obtain ⟨K₁, m₁, h₁⟩ := hF
  obtain ⟨K₂, m₂, h₂⟩ := hG
  refine ⟨|K₁| + |K₂|, max m₁ m₂, fun s hs x => ?_⟩
  have hx : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have key : ∀ (K : ℝ) (k : ℕ), k ≤ max m₁ m₂ →
      K * (1 + ‖x‖) ^ k ≤ |K| * (1 + ‖x‖) ^ max m₁ m₂ := fun K k hk =>
    mul_le_mul (le_abs_self K) (pow_le_pow_right₀ hx hk) (by positivity) (abs_nonneg K)
  calc |F s x + G s x| ≤ |F s x| + |G s x| := abs_add_le _ _
    _ ≤ K₁ * (1 + ‖x‖) ^ m₁ + K₂ * (1 + ‖x‖) ^ m₂ := add_le_add (h₁ s hs x) (h₂ s hs x)
    _ ≤ |K₁| * (1 + ‖x‖) ^ max m₁ m₂ + |K₂| * (1 + ‖x‖) ^ max m₁ m₂ :=
        add_le_add (key K₁ m₁ (le_max_left _ _)) (key K₂ m₂ (le_max_right _ _))
    _ = (|K₁| + |K₂|) * (1 + ‖x‖) ^ max m₁ m₂ := by ring

/-- Products of families of uniform polynomial growth. -/
theorem mul (hF : UPoly F) (hG : UPoly G) : UPoly (fun s x => F s x * G s x) := by
  obtain ⟨K₁, m₁, h₁⟩ := hF
  obtain ⟨K₂, m₂, h₂⟩ := hG
  refine ⟨K₁ * K₂, m₁ + m₂, fun s hs x => ?_⟩
  calc |F s x * G s x| = |F s x| * |G s x| := abs_mul _ _
    _ ≤ K₁ * (1 + ‖x‖) ^ m₁ * (K₂ * (1 + ‖x‖) ^ m₂) :=
        mul_le_mul (h₁ s hs x) (h₂ s hs x) (abs_nonneg _) ((abs_nonneg _).trans (h₁ s hs x))
    _ = K₁ * K₂ * (1 + ‖x‖) ^ (m₁ + m₂) := by ring

/-- Negatives of families of uniform polynomial growth. -/
theorem neg (hF : UPoly F) : UPoly (fun s x => -F s x) := by
  obtain ⟨K, m, h⟩ := hF
  exact ⟨K, m, fun s hs x => (abs_neg (F s x)).trans_le (h s hs x)⟩

/-- Differences of families of uniform polynomial growth. -/
theorem sub (hF : UPoly F) (hG : UPoly G) : UPoly (fun s x => F s x - G s x) :=
  (hF.add hG.neg).congr fun s _ x => (sub_eq_add_neg (F s x) (G s x)).symm

/-- Powers of families of uniform polynomial growth. -/
theorem pow (hF : UPoly F) : ∀ n : ℕ, UPoly (fun s x => F s x ^ n)
  | 0 => (UPoly.const 1).congr fun s _ x => (pow_zero (F s x)).symm
  | n + 1 => ((UPoly.pow hF n).mul hF).congr fun s _ x => (pow_succ (F s x) n).symm

/-- Finite sums of families of uniform polynomial growth. -/
theorem sum {ι : Type*} (S : Finset ι) {Fs : ι → ℝ → E d → ℝ} (h : ∀ i ∈ S, UPoly (Fs i)) :
    UPoly (fun s x => ∑ i ∈ S, Fs i s x) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact (UPoly.const 0).congr fun s _ x => by simp
  | insert a S ha ih =>
    exact ((h a (Finset.mem_insert_self a S)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).congr fun s _ x => by
        rw [Finset.sum_insert ha]

end UPoly

/-- `kernelR` preserves uniform polynomial growth. -/
theorem upoly_kernelR {a : ℝ → E d → Fin d → ℝ} {b : ℝ → E d → Fin d → Fin d → ℝ}
    {c : ℝ → E d → Fin d → Fin d → Fin d → ℝ} (ha : ∀ i, UPoly fun s x => a s x i)
    (hb : ∀ i j, UPoly fun s x => b s x i j) (hc : ∀ i j k, UPoly fun s x => c s x i j k) :
    UPoly fun s x => kernelR (a s x) (b s x) (c s x) := by
  have hH : ∀ i j, UPoly fun s x => hessR (a s x) (b s x) i j := fun i j =>
    ((ha i).mul (ha j)).sub (hb i j)
  have hD : ∀ i j k, UPoly fun s x => dhessR (a s x) (b s x) (c s x) i j k := fun i j k =>
    (((((hb i j).mul (ha k)).add ((hb i k).mul (ha j))).add ((ha i).mul (hb j k))).sub
      ((((UPoly.const 2).mul (ha i)).mul (ha j)).mul (ha k))).sub (hc i j k)
  have h₁ : UPoly fun s x => ∑ i, ∑ j, ∑ k, dhessR (a s x) (b s x) (c s x) i j k ^ 2 :=
    UPoly.sum _ fun i _ => UPoly.sum _ fun j _ => UPoly.sum _ fun k _ => (hD i j k).pow 2
  have h₂ : UPoly fun s x => ∑ i, ∑ j, ∑ k,
      hessR (a s x) (b s x) i j * hessR (a s x) (b s x) j k * hessR (a s x) (b s x) k i :=
    UPoly.sum _ fun i _ => UPoly.sum _ fun j _ => UPoly.sum _ fun k _ =>
      ((hH i j).mul (hH j k)).mul (hH k i)
  exact h₁.add ((UPoly.const 2).mul h₂)

/-! ### Measurability -/

/-- Partial derivatives are measurable (`pd` is total). -/
theorem measurable_pd (g : E d → ℝ) (i : Fin d) : Measurable (pd g i) :=
  measurable_fderiv_apply_const ℝ g (EuclideanSpace.single i (1 : ℝ))

/-- The kernel `K_ρ` is measurable for every `ρ`. -/
theorem measurable_kernelK (ρ : E d → ℝ) : Measurable (kernelK ρ) := by
  have hN : ∀ i j, Measurable (negHess ρ i j) := fun i j =>
    (measurable_pd (pd (fun y => Real.log (ρ y)) i) j).neg
  have h₁ : Measurable fun x => ∑ i, ∑ j, ∑ k, pd (negHess ρ i j) k x ^ 2 :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => (measurable_pd _ k).pow_const 2
  have h₂ : Measurable fun x => ∑ i, ∑ j, ∑ k,
      negHess ρ i j x * negHess ρ j k x * negHess ρ k i x :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => ((hN i j).mul (hN j k)).mul (hN k i)
  exact h₁.add (h₂.const_mul 2)

end Limit

/-! ### The heat flow of a Gaussian-dominated density at the initial time -/

namespace DensityFlowHyp

variable {T c Q : ℝ} {q f : E d → ℝ}

/-- **Initial values of the derivatives**: `∂ˡ(heat f s)(x) → ∂ˡf(x)` as `s → 0⁺`, for
`|l| ≤ 4`. -/
theorem tendsto_pdList_flow (H : DensityFlowHyp d T c Q q f) {l : List (Fin d)}
    (hl : l.length ≤ 4) (x : E d) :
    Tendsto (fun s => pdList (heat f s) l x) (𝓝[>] 0) (𝓝 (pdList f l x)) := by
  obtain ⟨M, hM⟩ := DensityFlow.exists_abs_le_of_polyGauss H.hT (H.polyGauss_pdList hl)
  refine (tendsto_heat_nhdsGT_zero (H.contDiff_pdList l).continuous hM x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [H.pdList_flow hs hl]

/-- The kernel converges at the initial time: `K_{heat f s}(x) → K_f(x)` as `s → 0⁺`. -/
theorem tendsto_kernelK_flow (H : DensityFlowHyp d T c Q q f) (x : E d) :
    Tendsto (fun s => kernelK (heat f s) x) (𝓝[>] 0) (𝓝 (kernelK f x)) := by
  have h₀ : Tendsto (fun s => heat f s x) (𝓝[>] 0) (𝓝 (f x)) :=
    H.tendsto_pdList_flow (l := []) (by simp) x
  have h₁ : ∀ i, Tendsto (fun s => pd (heat f s) i x) (𝓝[>] 0) (𝓝 (pd f i x)) := fun i =>
    H.tendsto_pdList_flow (l := [i]) (by simp) x
  have h₂ : ∀ i j, Tendsto (fun s => pd (pd (heat f s) i) j x) (𝓝[>] 0)
      (𝓝 (pd (pd f i) j x)) := fun i j =>
    H.tendsto_pdList_flow (l := [i, j]) (by simp) x
  have h₃ : ∀ i j k, Tendsto (fun s => pd (pd (pd (heat f s) i) j) k x) (𝓝[>] 0)
      (𝓝 (pd (pd (pd f i) j) k x)) := fun i j k =>
    H.tendsto_pdList_flow (l := [i, j, k]) (by simp) x
  rw [Limit.kernelK_eq H.contDiff H.pos x]
  refine (Limit.tendsto_kernelJet h₀ (H.pos x).ne' h₁ h₂ h₃).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  exact (Limit.kernelK_eq (H.contDiff_flow hs) (H.flow_pos hs) x).symm

/-- The kernel of the heat flow has polynomial growth, uniformly for `s ∈ (0, 1]`. -/
theorem upoly_kernelK_flow (H : DensityFlowHyp d T c Q q f) :
    Limit.UPoly (fun s x => kernelK (heat f s) x) := by
  have hA : ∀ i, Limit.UPoly (fun s x => pd (heat f s) i x / heat f s x) := fun i =>
    H.exists_abs_pdList_flow_div_le 1 (l := [i]) (by simp)
  have hB : ∀ i j, Limit.UPoly (fun s x => pd (pd (heat f s) i) j x / heat f s x) :=
    fun i j => H.exists_abs_pdList_flow_div_le 1 (l := [i, j]) (by simp)
  have hC : ∀ i j k,
      Limit.UPoly (fun s x => pd (pd (pd (heat f s) i) j) k x / heat f s x) :=
    fun i j k => H.exists_abs_pdList_flow_div_le 1 (l := [i, j, k]) (by simp)
  refine (Limit.upoly_kernelR hA hB hC).congr fun s hs x => ?_
  exact (Limit.kernelK_eq (H.contDiff_flow hs.1) (H.flow_pos hs.1) x).symm

/-- **Continuity of `D` at the initial time**: `D(heat f s) → D(f)` as `s → 0⁺`. -/
theorem tendsto_Dfun_flow (H : DensityFlowHyp d T c Q q f) :
    Tendsto (fun s => Dfun (heat f s)) (𝓝[>] 0) (𝓝 (Dfun f)) := by
  obtain ⟨K, m, hK⟩ := H.upoly_kernelK_flow
  have hT₁ : 0 < T + 1 := by linarith [H.hT]
  have hcQ : 0 ≤ c * Q := mul_nonneg H.hc.le (zero_le_one.trans H.one_le_Q)
  have hA : 0 ≤ ((T + 1) / T) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (div_nonneg hT₁.le H.hT.le) _
  show Tendsto (fun s => ∫ x, heat f s x * kernelK (heat f s) x) (𝓝[>] 0)
    (𝓝 (∫ x, f x * kernelK f x))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => c * Q * ((T + 1) / T) ^ ((d : ℝ) / 2) * K *
      ((1 + ‖x‖) ^ m * gaussian d (T + 1) x)) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    exact ((H.contDiff_flow hs).continuous.measurable.mul
      (Limit.measurable_kernelK _)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
    refine ae_of_all _ fun x => ?_
    have hρ := H.flow_pos hs.1 x
    have hb : heat f s x ≤ c * Q * (((T + 1) / T) ^ ((d : ℝ) / 2) * gaussian d (T + 1) x) :=
      (H.flow_le_mul_gaussian hs.1 x).trans (mul_le_mul_of_nonneg_left
        (gaussian_add_le_mul_gaussian_add H.hT hs.1.le hs.2 x) hcQ)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ]
    calc heat f s x * |kernelK (heat f s) x|
        ≤ c * Q * (((T + 1) / T) ^ ((d : ℝ) / 2) * gaussian d (T + 1) x) *
            (K * (1 + ‖x‖) ^ m) :=
          mul_le_mul hb (hK s hs x) (abs_nonneg _)
            (mul_nonneg hcQ (mul_nonneg hA (gaussian_pos hT₁ x).le))
      _ = c * Q * ((T + 1) / T) ^ ((d : ℝ) / 2) * K *
            ((1 + ‖x‖) ^ m * gaussian d (T + 1) x) := by ring
  · exact (integrable_one_add_norm_pow_mul_gaussian m hT₁).const_mul _
  · exact ae_of_all _ fun x =>
      (H.tendsto_pdList_flow (l := []) (by simp) x).mul (H.tendsto_kernelK_flow x)

/-- **Negative `D` persists for short times**: if `D(f) < 0`, then `D(heat f s) < 0` for all
`s ∈ (0, ε)`, for some `ε > 0`. -/
theorem exists_Dfun_flow_neg (H : DensityFlowHyp d T c Q q f) (hD : Dfun f < 0) :
    ∃ ε > 0, ∀ s ∈ Set.Ioo 0 ε, Dfun (heat f s) < 0 := by
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (H.tendsto_Dfun_flow.eventually (gt_mem_nhds hD))
  exact ⟨ε, hε, fun s hs => hsub hs⟩

end DensityFlowHyp

/-! ### Non-convexity from a negative second derivative -/

/-- **Abstract non-convexity**: if `I' = I₁` and `I₁' = I₂ < 0` on some interval `(0, ε)`, then
`I` is not convex on `(0, ∞)`. (On `(0, ε)`, `I` is strictly concave, which is incompatible with
convexity at a midpoint.) -/
theorem not_convexOn_Ioi_of_deriv2_neg {ε : ℝ} (hε : 0 < ε) {I I₁ I₂ : ℝ → ℝ}
    (h : ∀ t ∈ Set.Ioo 0 ε, HasDerivAt I (I₁ t) t ∧ HasDerivAt I₁ (I₂ t) t ∧ I₂ t < 0) :
    ¬ ConvexOn ℝ (Set.Ioi 0) I := by
  intro hconv
  have hcont : ContinuousOn I (Set.Ioo 0 ε) := fun t ht =>
    (h t ht).1.continuousAt.continuousWithinAt
  have hdd : ∀ t ∈ interior (Set.Ioo (0 : ℝ) ε), deriv^[2] I t < 0 := by
    intro t ht
    rw [interior_Ioo] at ht
    have hev : deriv I =ᶠ[𝓝 t] I₁ := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu using (h u hu).1.deriv
    simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp,
      Function.comp_apply]
    rw [hev.deriv_eq, (h t ht).2.1.deriv]
    exact (h t ht).2.2
  have hconc := strictConcaveOn_of_deriv2_neg (convex_Ioo 0 ε) hcont hdd
  have hconv' := hconv.subset Set.Ioo_subset_Ioi_self (convex_Ioo 0 ε)
  have hx : ε / 3 ∈ Set.Ioo 0 ε := ⟨by linarith, by linarith⟩
  have hy : 2 * ε / 3 ∈ Set.Ioo 0 ε := ⟨by linarith, by linarith⟩
  have hxy : ε / 3 ≠ 2 * ε / 3 := by
    intro hxy
    linarith
  have h₁ := hconc.2 hx hy hxy (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  have h₂ := hconv'.2 hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  exact lt_irrefl _ (h₁.trans_le h₂)

end Fisher41
