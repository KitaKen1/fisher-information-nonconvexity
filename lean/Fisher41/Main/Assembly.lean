/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Heat.Limit

/-!
# From the derivative identities to non-convexity

Abstract assembly step: if along the heat flow the Fisher information satisfies `I′ = -Q` and
`Q′ = -D(f_t)` at every positive time, and `D(f) < 0` at time `0`, then `I` has a negative
second derivative on some `(0, ε)` and is not convex on `(0, ∞)`.
-/

open MeasureTheory Real Filter Topology

noncomputable section

namespace Fisher41

variable {d : ℕ} {T c Q₀ : ℝ} {q f : E d → ℝ}

/-- **Negative second derivative near `0`** from the identities `I′ = -Q`, `Q′ = -D(f_t)` and
`D(f) < 0`. -/
theorem exists_deriv2_neg_of_identities (H : DensityFlowHyp d T c Q₀ q f) (hD : Dfun f < 0)
    {Qf : ℝ → ℝ}
    (hI : ∀ t : ℝ, 0 < t → HasDerivAt (fun s => fisher (heat f s)) (-Qf t) t)
    (hQ : ∀ t : ℝ, 0 < t → HasDerivAt Qf (-Dfun (heat f t)) t) :
    ∃ ε > 0, ∃ I₁ I₂ : ℝ → ℝ, ∀ t ∈ Set.Ioo 0 ε,
      HasDerivAt (fun s => fisher (heat f s)) (I₁ t) t ∧
      HasDerivAt I₁ (I₂ t) t ∧ I₂ t < 0 := by
  obtain ⟨ε, hε, hneg⟩ := H.exists_Dfun_flow_neg hD
  refine ⟨ε, hε, fun s => -Qf s, fun s => Dfun (heat f s), fun t ht =>
    ⟨hI t ht.1, ?_, hneg t ht⟩⟩
  have h := (hQ t ht.1).neg
  rw [neg_neg] at h
  exact h

/-- **Non-convexity** from the identities `I′ = -Q`, `Q′ = -D(f_t)` and `D(f) < 0`. -/
theorem not_convexOn_of_identities (H : DensityFlowHyp d T c Q₀ q f) (hD : Dfun f < 0)
    {Qf : ℝ → ℝ}
    (hI : ∀ t : ℝ, 0 < t → HasDerivAt (fun s => fisher (heat f s)) (-Qf t) t)
    (hQ : ∀ t : ℝ, 0 < t → HasDerivAt Qf (-Dfun (heat f t)) t) :
    ¬ ConvexOn ℝ (Set.Ioi 0) (fun t => fisher (heat f t)) := by
  obtain ⟨ε, hε, I₁, I₂, h⟩ := exists_deriv2_neg_of_identities H hD hI hQ
  exact not_convexOn_Ioi_of_deriv2_neg hε h

/-- **`C²` regularity on `(0, ∞)`** from `I′ = -Q`, `Q′ = -D_t` and continuity of `t ↦ D_t`;
moreover `I'' = D_t` there. -/
theorem contDiffOn_two_of_identities {I Qf Dt : ℝ → ℝ}
    (hI : ∀ t : ℝ, 0 < t → HasDerivAt I (-Qf t) t)
    (hQ : ∀ t : ℝ, 0 < t → HasDerivAt Qf (-Dt t) t)
    (hD : ContinuousOn Dt (Set.Ioi 0)) :
    ContDiffOn ℝ 2 I (Set.Ioi 0) ∧ ∀ t : ℝ, 0 < t → deriv (deriv I) t = Dt t := by
  have hderI : ∀ t : ℝ, 0 < t → deriv I t = -Qf t := fun t ht => (hI t ht).deriv
  have hnegQ : ∀ t : ℝ, 0 < t → HasDerivAt (fun s => -Qf s) (Dt t) t := fun t ht => by
    have h := (hQ t ht).neg
    rw [neg_neg] at h
    exact h
  refine ⟨?_, fun t ht => ?_⟩
  · have hC1 : ContDiffOn ℝ 1 (fun s => -Qf s) (Set.Ioi 0) := by
      have key := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := 0)
        (f := fun s => -Qf s) isOpen_Ioi).2
        ⟨fun t ht => (hnegQ t ht).differentiableAt.differentiableWithinAt, by simp,
          contDiffOn_zero.2 (hD.congr fun t ht => (hnegQ t ht).deriv)⟩
      rwa [zero_add] at key
    have key := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := 1) (f := I) isOpen_Ioi).2
      ⟨fun t ht => (hI t ht).differentiableAt.differentiableWithinAt, by simp,
        hC1.congr fun t ht => hderI t ht⟩
    rwa [one_add_one_eq_two] at key
  · have hEq : deriv I =ᶠ[𝓝 t] fun s => -Qf s := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using hderI s hs
    rw [hEq.deriv_eq]
    exact (hnegQ t ht).deriv

end Fisher41
