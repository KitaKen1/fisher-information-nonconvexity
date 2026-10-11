/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Static.DensityNeg
import Fisher41.Heat.DensityFlow

/-!
# The densities `f_R` satisfy the standing hypotheses of the heat-flow analysis

`f_R = Z_R⁻¹ q γ_{R²}` where `q = e^U` is smooth, `1 ≤ q`, and every iterated derivative of `q`
is bounded: it is continuous and invariant under the lattice `20 ℤ⁴¹`, hence bounded by its
maximum on the compact fundamental cell.
-/

open MeasureTheory Real
open scoped ContDiff

noncomputable section

namespace Fisher41

namespace FlowHyp

/-- The iterated derivatives of `q` are invariant under the lattice translations. -/
theorem iteratedFDeriv_qper_add_latt (k : ℕ) (x : E 41) (z : Fin 41 → ℤ) :
    iteratedFDeriv ℝ k qper (x + latt z) = iteratedFDeriv ℝ k qper x := by
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext y
  exact qper_add_latt y z

/-- The iterated derivatives of `q` are bounded. -/
theorem exists_norm_iteratedFDeriv_qper_le (k : ℕ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k qper x‖ ≤ C := by
  obtain ⟨M, hM⟩ := DensityNeg.exists_abs_le_of_add_latt
    (g := fun x => ‖iteratedFDeriv ℝ k qper x‖)
    (contDiff_infty.1 contDiff_qper k).continuous_iteratedFDeriv'.norm
    (fun x z => by simp only [iteratedFDeriv_qper_add_latt])
  exact ⟨M, fun x => (le_abs_self _).trans (hM x)⟩

/-- `q` is bounded above. -/
theorem exists_qper_le : ∃ Q, ∀ x, qper x ≤ Q := by
  obtain ⟨C, hC⟩ := exists_abs_qper_le
  exact ⟨C, fun x => (le_abs_self _).trans (hC x)⟩

end FlowHyp

/-- **Standing hypotheses for `f_R`**: `f_R = c q γ_{R²}` with `c = Z_R⁻¹`. -/
theorem exists_densityFlowHyp_fR {R : ℝ} (hR : 0 < R) :
    ∃ Q, DensityFlowHyp 41 (R ^ 2) (∫ x, qper x * gaussian 41 (R ^ 2) x)⁻¹ Q qper (fR R) := by
  obtain ⟨Q, hQ⟩ := FlowHyp.exists_qper_le
  have hZ := one_le_integral_qper_mul_gaussian hR
  exact ⟨Q, DensityFlowHyp.of_iteratedFDeriv (by positivity) (inv_pos.2 (by linarith))
    contDiff_qper one_le_qper hQ (fun k _ => FlowHyp.exists_norm_iteratedFDeriv_qper_le k)
    (fun x => congrFun (fR_eq R) x)⟩

end Fisher41
