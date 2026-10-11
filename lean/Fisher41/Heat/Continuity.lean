/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Heat.Limit

/-!
# Continuity of `D` along the heat flow at positive times

For a density `f` satisfying the standing hypotheses `Fisher41.DensityFlowHyp d T c Q q f`
(`f = c q γ_T`), this file shows that `s ↦ D(ρ s) = ∫ ρ s K_{ρ s}`, where `ρ s = heat f s`, is
continuous on `(0, ∞)`. Continuity at the initial time `s = 0⁺` is
`Fisher41.DensityFlowHyp.tendsto_Dfun_flow`.

## Main results

* `Fisher41.DensityFlowHyp.continuousAt_pdList_flow`: for `t₀ > 0` and `|l| ≤ 4`,
  `s ↦ ∂ˡ(heat f s)(x)` is continuous at `t₀`.
* `Fisher41.DensityFlowHyp.continuousAt_kernelK_flow`: `s ↦ K_{heat f s}(x)` is continuous at
  every `t₀ > 0`.
* `Fisher41.DensityFlowHyp.exists_abs_kernelK_flow_le`: `K_{heat f s}` has polynomial growth,
  uniformly for `s ∈ (0, t₁]`.
* `Fisher41.DensityFlowHyp.exists_abs_flow_mul_kernelK_le`: the integrand of `D` is dominated,
  `|ρ s(x) K_{ρ s}(x)| ≤ C (1 + ‖x‖)^m γ_{T+t₁}(x)` for `s ∈ (0, t₁]`.
* `Fisher41.DensityFlowHyp.continuousAt_Dfun_flow`,
  `Fisher41.DensityFlowHyp.continuousOn_Dfun_flow`: `s ↦ D(heat f s)` is continuous at every
  `t₀ > 0`, hence on `(0, ∞)`.

## Implementation notes

Pointwise continuity of the `3`-jet in time comes from the heat equation
(`Fisher41.hasDerivAt_heat`) for the bounded continuous functions `∂ˡf`, since
`∂ˡ(heat f s) = heat (∂ˡf) s` (`Fisher41.DensityFlowHyp.pdList_flow`); `K` is a continuous
function of the jet where `ρ ≠ 0` (`Fisher41.Limit.tendsto_kernelJet`).

Uniform polynomial growth for `s ∈ (0, t₁]` is reduced to `Fisher41.Limit.UPoly`, which is about
`s ∈ (0, 1]`, by the time change `s ↦ s t₁` (`Fisher41.Continuity.upoly_comp_mul`,
`Fisher41.Continuity.exists_abs_le_of_upoly_comp_mul`), so that the closure properties of
`Fisher41.Limit.UPoly` (`Fisher41.Limit.upoly_kernelR`) apply unchanged. Continuity of `D` at
`t₀` then follows by dominated convergence, with the bound `C (1 + ‖x‖)^m γ_{T+2t₀}(x)` valid for
`s ∈ (0, 2t₀)`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Fisher41

variable {d : ℕ}

namespace Continuity

/-! ### Time changes in uniform polynomial bounds -/

/-- **Time change into `Fisher41.Limit.UPoly`**: if the functions `F s` have polynomial growth
uniformly for `s ∈ (0, t₁]`, then `s ↦ F (s * t₁)` has polynomial growth uniformly for
`s ∈ (0, 1]`. -/
theorem upoly_comp_mul {F : ℝ → E d → ℝ} {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hF : ∃ K : ℝ, ∃ m : ℕ, ∀ s ∈ Set.Ioc 0 t₁, ∀ x, |F s x| ≤ K * (1 + ‖x‖) ^ m) :
    Limit.UPoly fun s x => F (s * t₁) x := by
  obtain ⟨K, m, h⟩ := hF
  exact ⟨K, m, fun s hs x =>
    h (s * t₁) ⟨mul_pos hs.1 ht₁, mul_le_of_le_one_left ht₁.le hs.2⟩ x⟩

/-- **Time change out of `Fisher41.Limit.UPoly`**: if `s ↦ F (s * t₁)` has polynomial growth
uniformly for `s ∈ (0, 1]`, then the functions `F s` have polynomial growth uniformly for
`s ∈ (0, t₁]`. -/
theorem exists_abs_le_of_upoly_comp_mul {F : ℝ → E d → ℝ} {t₁ : ℝ} (ht₁ : 0 < t₁)
    (hF : Limit.UPoly fun s x => F (s * t₁) x) :
    ∃ K : ℝ, ∃ m : ℕ, ∀ s ∈ Set.Ioc 0 t₁, ∀ x, |F s x| ≤ K * (1 + ‖x‖) ^ m := by
  obtain ⟨K, m, h⟩ := hF
  refine ⟨K, m, fun s hs x => ?_⟩
  have h' : |F (s / t₁ * t₁) x| ≤ K * (1 + ‖x‖) ^ m :=
    h (s / t₁) ⟨div_pos hs.1 ht₁, (div_le_one ht₁).2 hs.2⟩ x
  rwa [div_mul_cancel₀ s ht₁.ne'] at h'

end Continuity

namespace DensityFlowHyp

variable {T c Q : ℝ} {q f : E d → ℝ}

/-! ### Pointwise continuity in time -/

/-- **Continuity in time of the derivatives**: for `t₀ > 0` and `|l| ≤ 4`,
`s ↦ ∂ˡ(heat f s)(x)` is continuous at `t₀`. -/
theorem continuousAt_pdList_flow (H : DensityFlowHyp d T c Q q f) {t₀ : ℝ} (ht₀ : 0 < t₀)
    {l : List (Fin d)} (hl : l.length ≤ 4) (x : E d) :
    ContinuousAt (fun s => pdList (heat f s) l x) t₀ := by
  obtain ⟨M, hM⟩ := DensityFlow.exists_abs_le_of_polyGauss H.hT (H.polyGauss_pdList hl)
  refine (hasDerivAt_heat (H.contDiff_pdList l).continuous.aestronglyMeasurable
    (ae_of_all _ fun y => (Real.norm_eq_abs _).trans_le (hM y)) ht₀ x).continuousAt.congr ?_
  filter_upwards [lt_mem_nhds ht₀] with s hs
  rw [H.pdList_flow hs hl]

/-- **Continuity in time of the kernel**: for `t₀ > 0`, `s ↦ K_{heat f s}(x)` is continuous at
`t₀`. -/
theorem continuousAt_kernelK_flow (H : DensityFlowHyp d T c Q q f) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (x : E d) : ContinuousAt (fun s => kernelK (heat f s) x) t₀ := by
  have h₀ : Tendsto (fun s => heat f s x) (𝓝 t₀) (𝓝 (heat f t₀ x)) :=
    H.continuousAt_pdList_flow ht₀ (l := []) (by simp) x
  have h₁ : ∀ i, Tendsto (fun s => pd (heat f s) i x) (𝓝 t₀) (𝓝 (pd (heat f t₀) i x)) :=
    fun i => H.continuousAt_pdList_flow ht₀ (l := [i]) (by simp) x
  have h₂ : ∀ i j, Tendsto (fun s => pd (pd (heat f s) i) j x) (𝓝 t₀)
      (𝓝 (pd (pd (heat f t₀) i) j x)) := fun i j =>
    H.continuousAt_pdList_flow ht₀ (l := [i, j]) (by simp) x
  have h₃ : ∀ i j k, Tendsto (fun s => pd (pd (pd (heat f s) i) j) k x) (𝓝 t₀)
      (𝓝 (pd (pd (pd (heat f t₀) i) j) k x)) := fun i j k =>
    H.continuousAt_pdList_flow ht₀ (l := [i, j, k]) (by simp) x
  show Tendsto (fun s => kernelK (heat f s) x) (𝓝 t₀) (𝓝 (kernelK (heat f t₀) x))
  rw [Limit.kernelK_eq (H.contDiff_flow ht₀) (H.flow_pos ht₀) x]
  refine (Limit.tendsto_kernelJet h₀ (H.flow_pos ht₀ x).ne' h₁ h₂ h₃).congr' ?_
  filter_upwards [lt_mem_nhds ht₀] with s hs
  exact (Limit.kernelK_eq (H.contDiff_flow hs) (H.flow_pos hs) x).symm

/-! ### Uniform domination -/

/-- The kernel of the heat flow has polynomial growth, uniformly for `s ∈ (0, t₁]`: there are
`K` and `m` with `|K_{heat f s}(x)| ≤ K (1 + ‖x‖)^m` for all `s ∈ (0, t₁]` and all `x`. -/
theorem exists_abs_kernelK_flow_le (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    ∃ K : ℝ, ∃ m : ℕ, ∀ s ∈ Set.Ioc 0 t₁, ∀ x, |kernelK (heat f s) x| ≤ K * (1 + ‖x‖) ^ m := by
  rcases le_or_gt t₁ 0 with ht₁ | ht₁
  · exact ⟨0, 0, fun s hs => (lt_irrefl (0 : ℝ) (hs.1.trans_le (hs.2.trans ht₁))).elim⟩
  have hU : ∀ l : List (Fin d), l.length ≤ 4 →
      Limit.UPoly fun s x => pdList (heat f (s * t₁)) l x / heat f (s * t₁) x := fun l hl =>
    Continuity.upoly_comp_mul (F := fun s x => pdList (heat f s) l x / heat f s x) ht₁
      (H.exists_abs_pdList_flow_div_le t₁ hl)
  have hA : ∀ i, Limit.UPoly fun s x => pd (heat f (s * t₁)) i x / heat f (s * t₁) x :=
    fun i => hU [i] (by simp)
  have hB : ∀ i j,
      Limit.UPoly fun s x => pd (pd (heat f (s * t₁)) i) j x / heat f (s * t₁) x :=
    fun i j => hU [i, j] (by simp)
  have hC : ∀ i j k,
      Limit.UPoly fun s x => pd (pd (pd (heat f (s * t₁)) i) j) k x / heat f (s * t₁) x :=
    fun i j k => hU [i, j, k] (by simp)
  refine Continuity.exists_abs_le_of_upoly_comp_mul (F := fun s x => kernelK (heat f s) x) ht₁
    ((Limit.upoly_kernelR hA hB hC).congr fun s hs x => ?_)
  have hs' : 0 < s * t₁ := mul_pos hs.1 ht₁
  exact (Limit.kernelK_eq (H.contDiff_flow hs') (H.flow_pos hs') x).symm

/-- **Uniform domination of the integrand of `D`**: for every `t₁` there are `C` and `m` with
`|heat f s x * K_{heat f s}(x)| ≤ C (1 + ‖x‖)^m γ_{T+t₁}(x)` for all `s ∈ (0, t₁]` and all `x`. -/
theorem exists_abs_flow_mul_kernelK_le (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ) :
    ∃ C : ℝ, ∃ m : ℕ, ∀ s ∈ Set.Ioc 0 t₁, ∀ x,
      |heat f s x * kernelK (heat f s) x| ≤ C * ((1 + ‖x‖) ^ m * gaussian d (T + t₁) x) := by
  obtain ⟨K, m, hK⟩ := H.exists_abs_kernelK_flow_le t₁
  refine ⟨c * Q * ((T + t₁) / T) ^ ((d : ℝ) / 2) * K, m, fun s hs x => ?_⟩
  have hTt₁ : 0 < T + t₁ := by linarith [H.hT, hs.1, hs.2]
  have hcQ : 0 ≤ c * Q := mul_nonneg H.hc.le (zero_le_one.trans H.one_le_Q)
  have hA : 0 ≤ ((T + t₁) / T) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (div_nonneg hTt₁.le H.hT.le) _
  have hρ := H.flow_pos hs.1 x
  have hb : heat f s x ≤ c * Q * (((T + t₁) / T) ^ ((d : ℝ) / 2) * gaussian d (T + t₁) x) :=
    (H.flow_le_mul_gaussian hs.1 x).trans (mul_le_mul_of_nonneg_left
      (gaussian_add_le_mul_gaussian_add H.hT hs.1.le hs.2 x) hcQ)
  rw [abs_mul, abs_of_pos hρ]
  calc heat f s x * |kernelK (heat f s) x|
      ≤ c * Q * (((T + t₁) / T) ^ ((d : ℝ) / 2) * gaussian d (T + t₁) x) *
          (K * (1 + ‖x‖) ^ m) :=
        mul_le_mul hb (hK s hs x) (abs_nonneg _)
          (mul_nonneg hcQ (mul_nonneg hA (gaussian_pos hTt₁ x).le))
    _ = c * Q * ((T + t₁) / T) ^ ((d : ℝ) / 2) * K *
          ((1 + ‖x‖) ^ m * gaussian d (T + t₁) x) := by ring

/-! ### Continuity of `D` -/

/-- **Continuity of `D` at positive times**: for `t₀ > 0`, `s ↦ D(heat f s)` is continuous at
`t₀`. -/
theorem continuousAt_Dfun_flow (H : DensityFlowHyp d T c Q q f) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ContinuousAt (fun s => Dfun (heat f s)) t₀ := by
  obtain ⟨C, m, hC⟩ := H.exists_abs_flow_mul_kernelK_le (2 * t₀)
  have hT₁ : 0 < T + 2 * t₀ := by linarith [H.hT]
  show ContinuousAt (fun s => ∫ x, heat f s x * kernelK (heat f s) x) t₀
  refine continuousAt_of_dominated
    (bound := fun x => C * ((1 + ‖x‖) ^ m * gaussian d (T + 2 * t₀) x)) ?_ ?_ ?_ ?_
  · filter_upwards [lt_mem_nhds ht₀] with s hs
    exact ((H.contDiff_flow hs).continuous.measurable.mul
      (Limit.measurable_kernelK _)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds ht₀ (by linarith : t₀ < 2 * t₀)] with s hs
    exact ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hC s ⟨hs.1, hs.2.le⟩ x)
  · exact (integrable_one_add_norm_pow_mul_gaussian m hT₁).const_mul C
  · exact ae_of_all _ fun x =>
      (H.continuousAt_pdList_flow ht₀ (l := []) (by simp) x).mul
        (H.continuousAt_kernelK_flow ht₀ x)

/-- **Continuity of `D` along the heat flow**: `s ↦ D(heat f s)` is continuous on `(0, ∞)`. -/
theorem continuousOn_Dfun_flow (H : DensityFlowHyp d T c Q q f) :
    ContinuousOn (fun s => Dfun (heat f s)) (Set.Ioi 0) := fun _ ht =>
  (H.continuousAt_Dfun_flow ht).continuousWithinAt

end DensityFlowHyp

end Fisher41
