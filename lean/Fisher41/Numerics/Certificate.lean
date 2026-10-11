/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Fisher41.Numerics.JetSound
import Fisher41.Numerics.Midpoint
import Fisher41.Numerics.CellCheck

/-!
# From kernel-checked cells to a bound on the real integral

`cellOK_sound`: if the Boolean cell check passes, the integral of the radial integrand
over the cell `[A/D, B/D]` is at most `q`.  The proof combines the jet enclosures
(`radial?_sound`) on the one-point cell of the midpoint and on the whole cell with the
midpoint-rule error bound.  `integral_le_add` chains consecutive cells.
-/

namespace Fisher41.Num

open MeasureTheory

theorem D_pos : (0 : ℤ) < D := by unfold D; norm_num

theorem D_pos' : (0 : ℝ) < (D : ℝ) := by exact_mod_cast D_pos

theorem radialC2_continuous : Continuous radialC2.f :=
  continuous_iff_continuousAt.2 fun x => (radialC2.hf x).continuousAt

theorem radialC2_intervalIntegrable (a b : ℝ) : IntervalIntegrable radialC2.f volume a b :=
  radialC2_continuous.intervalIntegrable a b

/-- The midpoint jet is the identity jet on the one-point cell. -/
theorem jetOn_point (n d : ℤ) (hd : 0 < d) :
    JetOn ⟨IV.rat n d, IV.rat 1, IV.rat 0⟩ C2F.id {(n : ℝ) / d} := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨IV.rat_mem n d hd, ?_, ?_⟩
  · show (IV.rat 1).mem 1
    simpa using IV.rat_one_mem 1
  · show (IV.rat 0).mem (0 / 2)
    simpa using IV.rat_one_mem 0

/-- The cell jet is the identity jet on `[A/D, B/D]`. -/
theorem jetOn_cell (A B : ℤ) :
    JetOn ⟨⟨(IV.rat A D).lo, (IV.rat B D).hi⟩, IV.rat 1, IV.rat 0⟩ C2F.id
      (Set.Icc ((A : ℝ) / D) ((B : ℝ) / D)) := by
  intro x hx
  obtain ⟨hA, -⟩ := IV.rat_mem A D D_pos
  obtain ⟨-, hB⟩ := IV.rat_mem B D D_pos
  refine ⟨⟨hA.trans hx.1, hx.2.trans hB⟩, ?_, ?_⟩
  · show (IV.rat 1).mem 1
    simpa using IV.rat_one_mem 1
  · show (IV.rat 0).mem (0 / 2)
    simpa using IV.rat_one_mem 0

/-- **Soundness of one cell.** -/
theorem cellOK_sound {A B : ℕ} {q : ℤ} (h : cellOK A B q = true) :
    ∫ x in ((A : ℝ) / D)..((B : ℝ) / D), radialC2.f x ≤ q := by
  have hS := S_pos
  have hD := D_pos'
  unfold cellOK at h
  generalize hMdef : radial? (midJet A B) = oM at h
  generalize hKdef : radial? (cellJet A B) = oK at h
  cases oM with
  | none => simp [cellDecide] at h
  | some M =>
  cases oK with
  | none => simp [cellDecide] at h
  | some K =>
  simp only [cellDecide, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hAB, hineq⟩ := h
  -- the two enclosures
  have hmid := radial?_sound (J := midJet A B)
    (jetOn_point ((A : ℤ) + B) (2 * D) (by have := D_pos; omega)) hMdef
  have hcell := radial?_sound (J := cellJet A B) (jetOn_cell A B) hKdef
  set m : ℝ := (((A : ℤ) + B : ℤ) : ℝ) / ((2 * D : ℤ) : ℝ) with hm
  obtain ⟨⟨-, hFm⟩, -, -⟩ := hmid m (Set.mem_singleton m)
  -- bound on the second derivative on the cell
  have hF2 : ∀ x ∈ Set.Icc ((A : ℝ) / D) ((B : ℝ) / D),
      |radialC2.f2 x| ≤ 2 * (K.e.absUpper : ℝ) / S := by
    intro x hx
    obtain ⟨-, -, he⟩ := hcell x (by simpa using hx)
    have h1 := IV.abs_le_absUpper he
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
    have h2 : |radialC2.f2 x| ≤ 2 * ((K.e.absUpper : ℝ) / S) := by linarith
    simpa [mul_div_assoc] using h2
  have hABr : (A : ℝ) / D ≤ (B : ℝ) / D := by
    have : (A : ℝ) ≤ B := by exact_mod_cast hAB.le
    gcongr
  have hmid_eq : ((A : ℝ) / D + (B : ℝ) / D) / 2 = m := by
    rw [hm]; push_cast; field_simp
  have hint := integral_le_midpoint_add radialC2.hf radialC2.hf1 hABr hF2
  rw [hmid_eq] at hint
  -- arithmetic
  have hh0 : (0 : ℝ) ≤ (B : ℝ) - A := by
    have : (A : ℝ) ≤ B := by exact_mod_cast hAB.le
    linarith
  have hwidth : (B : ℝ) / D - (A : ℝ) / D = ((B : ℝ) - A) / D := by ring
  rw [hwidth] at hint
  have hstep : ((B : ℝ) - A) / D * radialC2.f m ≤ ((B : ℝ) - A) / D * ((M.v.hi : ℝ) / S) :=
    mul_le_mul_of_nonneg_left hFm (by positivity)
  have hcast : (12 * ((B : ℝ) - A) * (D : ℝ) ^ 2 * (M.v.hi : ℝ) +
      ((B : ℝ) - A) ^ 3 * (K.e.absUpper : ℝ)) ≤ 12 * (S : ℝ) * (D : ℝ) ^ 3 * q := by
    exact_mod_cast hineq
  have heq : ((B : ℝ) - A) / D * ((M.v.hi : ℝ) / S) +
      2 * (K.e.absUpper : ℝ) / S * (((B : ℝ) - A) / D) ^ 3 / 24 =
      (12 * ((B : ℝ) - A) * (D : ℝ) ^ 2 * (M.v.hi : ℝ) +
        ((B : ℝ) - A) ^ 3 * (K.e.absUpper : ℝ)) / (12 * (S : ℝ) * (D : ℝ) ^ 3) := by
    field_simp
    ring
  have hfinal : ((B : ℝ) - A) / D * ((M.v.hi : ℝ) / S) +
      2 * (K.e.absUpper : ℝ) / S * (((B : ℝ) - A) / D) ^ 3 / 24 ≤ (q : ℝ) := by
    rw [heq, div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- Adding bounds over adjacent intervals. -/
theorem integral_le_add {a b c s₁ s₂ : ℝ} (h₁ : ∫ x in a..b, radialC2.f x ≤ s₁)
    (h₂ : ∫ x in b..c, radialC2.f x ≤ s₂) : ∫ x in a..c, radialC2.f x ≤ s₁ + s₂ := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (radialC2_intervalIntegrable a b)
    (radialC2_intervalIntegrable b c)]
  linarith

end Fisher41.Num
