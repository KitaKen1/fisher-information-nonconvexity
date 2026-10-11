/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Density
import Fisher41.Static.RadialTensor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The periodic log-density `U`: smoothness, periodicity and the cell integral

Recall the cut-off profile `ũ(s) = η(s/16) u(s)`, the bump `w(x) = ũ(|x|²/2)`, the lattice
points `20 z` (`z ∈ ℤ⁴¹`), the periodic sum `U(x) = Σ_z w(x - 20 z)` and `q = e^U`
(`Fisher41.ucut`, `Fisher41.bump`, `Fisher41.latt`, `Fisher41.Uper`, `Fisher41.qper`).

## Main results

* `Fisher41.contDiff_ucut`, `Fisher41.contDiff_bump`, `Fisher41.contDiff_Uper`,
  `Fisher41.contDiff_qper`: smoothness.
* `Fisher41.Periodic.ucut_eq_zero`, `Fisher41.bump_eq_zero`: `ũ = 0` on `[32, ∞)` and `w(x) = 0` for
  `|x| ≥ 8`; `Fisher41.ucut_nonneg`, `Fisher41.bump_nonneg`.
* `Fisher41.twenty_le_norm_latt_sub`, `Fisher41.nine_le_norm_sub_latt`: lattice geometry.
* `Fisher41.locallyFinite_support_bump`: the translated bumps form a locally finite family.
* `Fisher41.Uper_add_latt`, `Fisher41.Uper_add_single`, `Fisher41.qper_add_latt`,
  `Fisher41.qper_add_single`: periodicity.
* `Fisher41.Uper_nonneg`, `Fisher41.one_le_qper`, `Fisher41.exists_abs_Uper_le`,
  `Fisher41.exists_abs_qper_le`: sign and boundedness.
* `Fisher41.Uper_eq_bump`, `Fisher41.kernelK_qper_eq`: on the open box `(-11, 11)⁴¹` one has
  `U = w`, hence `K_q = K_{e^w}` there.
* `Fisher41.cell_integral_eq`: the integral of `q K_q` over the period cell `[-10, 10]⁴¹`
  (`Fisher41.cell`) in polar coordinates.

## Proof sketch

Distinct lattice points are `20` apart while each bump is supported in the ball of radius `8`,
so every point has a neighbourhood meeting at most one of the supports, and on the box
`(-11, 11)⁴¹` only the bump centred at the origin survives. Since `pd` is built from `fderiv`,
functions agreeing on an open set have the same iterated partial derivatives there; hence on the
cell `q K_q = e^w K_{e^w}`, which is the radial function `G(|x|)` given by
`Fisher41.kernelK_exp_radial`. As `G(r) = 0` for `r ≥ 8`, the cell integral is the integral over
all of `ℝ⁴¹`, and `MeasureTheory.integral_fun_norm_addHaar` turns it into
`41 |B₁| ∫₀⁸ r⁴⁰ G(r) dr`.

Auxiliary lemmas live in the namespace `Fisher41.Periodic`.
-/

open MeasureTheory Metric Filter Topology
open scoped ContDiff

noncomputable section

namespace Fisher41

/-- The closed period cell `[-10, 10]⁴¹` of the lattice `20 ℤ⁴¹`. -/
def cell : Set (E 41) := {x | ∀ i, x i ∈ Set.Icc (-10 : ℝ) 10}

namespace Periodic

/-! ### The radial profile -/

/-- `V` is smooth. -/
theorem contDiff_Vfun : ContDiff ℝ ∞ Vfun := by
  show ContDiff ℝ ∞ fun s : ℝ => 15 - 2 * s - s ^ 2
  fun_prop

/-- `u` is smooth. -/
theorem contDiff_uprof : ContDiff ℝ ∞ uprof := by
  have h1 : ContDiff ℝ ∞ fun s => 1 + Real.exp (Vfun s) := contDiff_const.add contDiff_Vfun.exp
  have h2 : ContDiff ℝ ∞ fun s => Real.log (1 + Real.exp (Vfun s)) :=
    h1.log fun s => (add_pos one_pos (Real.exp_pos (Vfun s))).ne'
  exact contDiff_const.mul h2

/-- `u ≥ 0`. -/
theorem uprof_nonneg (s : ℝ) : 0 ≤ uprof s :=
  mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [Real.exp_pos (Vfun s)]))

end Periodic

open Periodic

/-! ### Smoothness, support and sign of the bump -/

/-- `ũ` is smooth. -/
theorem contDiff_ucut : ContDiff ℝ ∞ ucut := by
  have h : ContDiff ℝ ∞ fun s : ℝ => eta (s / 16) := contDiff_eta.comp (contDiff_id.div_const 16)
  exact h.mul contDiff_uprof

/-- The bump `w(x) = ũ(|x|²/2)` is smooth. -/
theorem contDiff_bump : ContDiff ℝ ∞ bump := by
  have h : ContDiff ℝ ∞ fun x : E 41 => ‖x‖ ^ 2 / 2 := (contDiff_norm_sq ℝ).div_const 2
  exact contDiff_ucut.comp h

/-- `ũ` vanishes on `[32, ∞)`. -/
theorem Periodic.ucut_eq_zero {s : ℝ} (hs : 32 ≤ s) : ucut s = 0 := by
  rw [ucut, eta_of_two_le (show (2 : ℝ) ≤ s / 16 by linarith), zero_mul]

/-- The bump vanishes outside the open ball of radius `8`. -/
theorem bump_eq_zero {x : E 41} (hx : 8 ≤ ‖x‖) : bump x = 0 :=
  Periodic.ucut_eq_zero (by nlinarith [norm_nonneg x])

/-- `ũ ≥ 0`. -/
theorem ucut_nonneg (s : ℝ) : 0 ≤ ucut s :=
  mul_nonneg (eta_nonneg _) (uprof_nonneg s)

/-- `w ≥ 0`. -/
theorem bump_nonneg (x : E 41) : 0 ≤ bump x :=
  ucut_nonneg _

/-- The bump has compact support (contained in the closed ball of radius `8`). -/
theorem hasCompactSupport_bump : HasCompactSupport bump :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E 41) 8) fun x hx => bump_eq_zero (by
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact hx.le)

/-! ### Lattice geometry -/

namespace Periodic

/-- Coordinates of the lattice point `20 z`. -/
theorem latt_apply (z : Fin 41 → ℤ) (i : Fin 41) : latt z i = 20 * (z i : ℝ) := rfl

/-- `latt 0 = 0`. -/
theorem latt_zero : latt 0 = 0 := by
  ext i
  simp [latt_apply]

/-- `latt` is additive. -/
theorem latt_add (z z' : Fin 41 → ℤ) : latt (z + z') = latt z + latt z' := by
  ext i
  simp only [PiLp.add_apply, latt_apply, Pi.add_apply, Int.cast_add]
  ring

/-- The lattice vector `20 eᵢ`. -/
theorem latt_single (i : Fin 41) :
    latt (Pi.single i 1) = (20 : ℝ) • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [latt_apply]
  · simp [latt_apply, h]

/-- A coordinate is bounded by the Euclidean norm. -/
theorem abs_apply_le_norm (x : E 41) (i : Fin 41) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i

end Periodic

/-- Distinct lattice points are at distance at least `20` (some coordinate differs by at least
`1`). -/
theorem twenty_le_norm_latt_sub {z z' : Fin 41 → ℤ} (h : z ≠ z') : 20 ≤ ‖latt z - latt z'‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have h1 : (1 : ℝ) ≤ |(z i : ℝ) - z' i| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hi)
  have h2 := abs_apply_le_norm (latt z - latt z') i
  rw [PiLp.sub_apply, latt_apply, latt_apply, ← mul_sub, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 20)] at h2
  linarith

/-- A point of the open box `(-11, 11)⁴¹` is at distance at least `9` from every nonzero lattice
point. -/
theorem nine_le_norm_sub_latt {x : E 41} (hx : ∀ i, |x i| < 11) {z : Fin 41 → ℤ} (hz : z ≠ 0) :
    9 ≤ ‖x - latt z‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
  have hi' : z i ≠ 0 := hi
  have h1 : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  have h2 := abs_apply_le_norm (x - latt z) i
  rw [PiLp.sub_apply, latt_apply] at h2
  have h3 : |(20 : ℝ) * z i| - |x i| ≤ |x i - 20 * z i| :=
    (abs_sub_abs_le_abs_sub _ _).trans (abs_sub_comm _ _).le
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 20)] at h3
  linarith [hx i]

namespace Periodic

/-- A point where a bump does not vanish lies within distance `8` of its center. -/
theorem norm_lt_of_bump_ne_zero {y : E 41} (h : bump y ≠ 0) : ‖y‖ < 8 :=
  not_le.1 fun h' => h (bump_eq_zero h')

/-- If the bumps centred at `20 z` and `20 z'` do not vanish at two points at distance `< 4`,
then `z = z'`. -/
theorem eq_of_bump_ne_zero {y y' : E 41} {z z' : Fin 41 → ℤ} (h : bump (y - latt z) ≠ 0)
    (h' : bump (y' - latt z') ≠ 0) (hyy : dist y y' < 4) : z = z' := by
  by_contra hne
  have h20 := twenty_le_norm_latt_sub hne
  have a1 := norm_lt_of_bump_ne_zero h
  have a2 := norm_lt_of_bump_ne_zero h'
  have key : latt z - latt z' = (y' - latt z') - (y - latt z) + (y - y') := by abel
  have n1 := norm_add_le ((y' - latt z') - (y - latt z)) (y - y')
  have n2 := norm_sub_le (y' - latt z') (y - latt z)
  rw [← key] at n1
  rw [dist_eq_norm] at hyy
  linarith

/-- At every point at most one translated bump is nonzero, so `U x` is either `0` or a single
term `w (x - 20 z)`. -/
theorem Uper_eq_zero_or_bump (x : E 41) : Uper x = 0 ∨ ∃ z, Uper x = bump (x - latt z) := by
  by_cases h : ∃ z, bump (x - latt z) ≠ 0
  · obtain ⟨z, hz⟩ := h
    refine Or.inr ⟨z, finsum_eq_single (fun w => bump (x - latt w)) z fun w hw => ?_⟩
    show bump (x - latt w) = 0
    by_contra hne
    exact hw (eq_of_bump_ne_zero hne hz (by rw [dist_self]; norm_num))
  · push Not at h
    exact Or.inl (finsum_eq_zero_of_forall_eq_zero h)

end Periodic

/-! ### Local finiteness and smoothness of `U` -/

/-- The supports of the translated bumps `x ↦ w (x - 20 z)` form a locally finite family: the
unit ball around any point meets at most one of them. -/
theorem locallyFinite_support_bump :
    LocallyFinite fun z : Fin 41 → ℤ => Function.support fun x : E 41 => bump (x - latt z) := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x one_pos, Set.Subsingleton.finite ?_⟩
  rintro z ⟨y, hy, hyx⟩ z' ⟨y', hy', hyx'⟩
  refine eq_of_bump_ne_zero (Function.mem_support.1 hy) (Function.mem_support.1 hy') ?_
  rw [mem_ball] at hyx hyx'
  have h := dist_triangle y x y'
  rw [dist_comm x y'] at h
  linarith

/-- `U` is smooth. -/
theorem contDiff_Uper : ContDiff ℝ ∞ Uper := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum locallyFinite_support_bump x
  have h : ContDiffAt ℝ ∞ (fun y => ∑ z ∈ s, bump (y - latt z)) x :=
    ContDiffAt.sum fun z _ => (contDiff_bump.comp (contDiff_id.sub contDiff_const)).contDiffAt
  exact h.congr_of_eventuallyEq hs

/-- `q = e^U` is smooth. -/
theorem contDiff_qper : ContDiff ℝ ∞ qper :=
  contDiff_Uper.exp

/-! ### Periodicity -/

/-- `U` is invariant under the lattice translations `x ↦ x + 20 z`. -/
theorem Uper_add_latt (x : E 41) (z : Fin 41 → ℤ) : Uper (x + latt z) = Uper x := by
  have h : ∀ w : Fin 41 → ℤ,
      bump (x + latt z - latt (Equiv.addRight z w)) = bump (x - latt w) := by
    intro w
    show bump (x + latt z - latt (w + z)) = bump (x - latt w)
    rw [latt_add]
    congr 1
    abel
  calc Uper (x + latt z) = ∑ᶠ w, bump (x + latt z - latt (Equiv.addRight z w)) :=
        (finsum_comp_equiv (Equiv.addRight z) (f := fun w => bump (x + latt z - latt w))).symm
    _ = ∑ᶠ w, bump (x - latt w) := finsum_congr h
    _ = Uper x := rfl

/-- `U` is `20`-periodic in each coordinate direction. -/
theorem Uper_add_single (x : E 41) (i : Fin 41) :
    Uper (x + (20 : ℝ) • EuclideanSpace.single i (1 : ℝ)) = Uper x := by
  rw [← latt_single, Uper_add_latt]

/-- `q` is invariant under the lattice translations `x ↦ x + 20 z`. -/
theorem qper_add_latt (x : E 41) (z : Fin 41 → ℤ) : qper (x + latt z) = qper x := by
  simp only [qper, Uper_add_latt]

/-- `q` is `20`-periodic in each coordinate direction. -/
theorem qper_add_single (x : E 41) (i : Fin 41) :
    qper (x + (20 : ℝ) • EuclideanSpace.single i (1 : ℝ)) = qper x := by
  simp only [qper, Uper_add_single]

/-! ### Sign and boundedness -/

/-- `U ≥ 0`. -/
theorem Uper_nonneg (x : E 41) : 0 ≤ Uper x :=
  finsum_nonneg fun _ => bump_nonneg _

/-- `q > 0`. -/
theorem qper_pos (x : E 41) : 0 < qper x :=
  Real.exp_pos _

/-- `q ≥ 1`. -/
theorem one_le_qper (x : E 41) : 1 ≤ qper x :=
  Real.one_le_exp (Uper_nonneg x)

namespace Periodic

/-- The bump is bounded (continuous with compact support). -/
theorem exists_abs_bump_le : ∃ C, ∀ x, |bump x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    contDiff_bump.continuous.bounded_above_of_compact_support hasCompactSupport_bump
  exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩

end Periodic

/-- `U` is bounded. -/
theorem exists_abs_Uper_le : ∃ C, ∀ x, |Uper x| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_bump_le
  refine ⟨C, fun x => ?_⟩
  rcases Uper_eq_zero_or_bump x with h | ⟨z, h⟩
  · rw [h, abs_zero]
    exact (abs_nonneg _).trans (hC 0)
  · rw [h]
    exact hC _

/-- `q` is bounded. -/
theorem exists_abs_qper_le : ∃ C, ∀ x, |qper x| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_Uper_le
  refine ⟨Real.exp C, fun x => ?_⟩
  rw [abs_of_pos (qper_pos x)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (hC x))

/-! ### Local equality on the box `(-11, 11)⁴¹` -/

/-- On the open box `(-11, 11)⁴¹` only the bump at the origin contributes: `U = w`. -/
theorem Uper_eq_bump {x : E 41} (hx : ∀ i, |x i| < 11) : Uper x = bump x := by
  have h : Uper x = bump (x - latt 0) :=
    finsum_eq_single (fun w => bump (x - latt w)) 0 fun z hz =>
      bump_eq_zero (le_trans (by norm_num) (nine_le_norm_sub_latt hx hz))
  rw [h, latt_zero, sub_zero]

namespace Periodic

/-- The open box `(-11, 11)⁴¹`, a neighbourhood of the cell on which `U = w`. -/
def box : Set (E 41) := {x | ∀ i, |x i| < 11}

/-- The box is open. -/
theorem isOpen_box : IsOpen box := by
  have h : box = ⋂ i : Fin 41, {x : E 41 | |x i| < 11} := by
    ext x
    simp only [box, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin 41 => ℝ) i))
      continuous_const

/-- Functions agreeing on an open set have the same partial derivatives there. -/
theorem pd_eqOn {d : ℕ} {g g' : E d → ℝ} {s : Set (E d)} (hs : IsOpen s)
    (h : Set.EqOn g g' s) (i : Fin d) : Set.EqOn (pd g i) (pd g' i) s := by
  intro x hx
  have hev : g =ᶠ[𝓝 x] g' := eventuallyEq_of_mem (hs.mem_nhds hx) h
  unfold pd
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev]

/-- Densities agreeing on an open set have the same kernel `K` there. -/
theorem kernelK_eqOn {d : ℕ} {ρ ρ' : E d → ℝ} {s : Set (E d)} (hs : IsOpen s)
    (h : Set.EqOn ρ ρ' s) : Set.EqOn (kernelK ρ) (kernelK ρ') s := by
  have hlog : Set.EqOn (fun y => Real.log (ρ y)) (fun y => Real.log (ρ' y)) s :=
    fun y hy => by simp only [h hy]
  have hH : ∀ i j, Set.EqOn (negHess ρ i j) (negHess ρ' i j) s := fun i j y hy => by
    simp only [negHess, pd_eqOn hs (pd_eqOn hs hlog i) j hy]
  intro x hx
  have e1 : ∀ i j, negHess ρ i j x = negHess ρ' i j x := fun i j => hH i j hx
  have e2 : ∀ i j k, pd (negHess ρ i j) k x = pd (negHess ρ' i j) k x :=
    fun i j k => pd_eqOn hs (hH i j) k hx
  simp only [kernelK, e1, e2]

end Periodic

/-- On the open box `(-11, 11)⁴¹`, `K_q = K_{e^w}`. -/
theorem kernelK_qper_eq {x : E 41} (hx : ∀ i, |x i| < 11) :
    kernelK qper x = kernelK (fun y => Real.exp (bump y)) x :=
  kernelK_eqOn isOpen_box
    (fun y hy => by simp only [qper, Uper_eq_bump (show ∀ i, |y i| < 11 from hy)])
    (show x ∈ box from hx)

/-! ### The cell integral -/

/-- The cell is closed. -/
theorem isClosed_cell : IsClosed cell := by
  have h : cell = ⋂ i : Fin 41, (fun x : E 41 => x i) ⁻¹' Set.Icc (-10) 10 := by
    ext x
    simp only [cell, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isClosed_iInter fun i =>
    isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin 41 => ℝ) i)

/-- The cell is measurable. -/
theorem measurableSet_cell : MeasurableSet cell :=
  isClosed_cell.measurableSet

namespace Periodic

/-- The radial profile `G(r) = e^{ũ(r²/2)} Kd 41 (r²/2) (-U₁(r²/2)) U₂(r²/2) U₃(r²/2)`, so that
`e^w K_{e^w} = G(|x|)` when `U₁, U₂, U₃` are the derivatives of `ũ`. -/
def radialG (U1 U2 U3 : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.exp (ucut (r ^ 2 / 2)) *
    Kd 41 (r ^ 2 / 2) (-U1 (r ^ 2 / 2)) (U2 (r ^ 2 / 2)) (U3 (r ^ 2 / 2))

/-- `G(r) = 0` for `r ≥ 8`. -/
theorem radialG_eq_zero {U1 U2 U3 : ℝ → ℝ}
    (hvan : ∀ s, 32 ≤ s → U1 s = 0 ∧ U2 s = 0 ∧ U3 s = 0) {r : ℝ} (hr : 8 ≤ r) :
    radialG U1 U2 U3 r = 0 := by
  have hs : 32 ≤ r ^ 2 / 2 := by nlinarith
  obtain ⟨h1, h2, h3⟩ := hvan _ hs
  simp only [radialG, Kd, h1, h2, h3]
  ring

/-- The radial tensor identity for `e^w`: `K_{e^w}(x) = Kd 41 s (-U₁ s) (U₂ s) (U₃ s)`,
`s = |x|²/2`. -/
theorem kernelK_exp_bump {U1 U2 U3 : ℝ → ℝ} (hU : ∀ s, HasDerivAt ucut (U1 s) s)
    (hU1 : ∀ s, HasDerivAt U1 (U2 s) s) (hU2 : ∀ s, HasDerivAt U2 (U3 s) s) (x : E 41) :
    kernelK (fun y => Real.exp (bump y)) x =
      Kd 41 (‖x‖ ^ 2 / 2) (-U1 (‖x‖ ^ 2 / 2)) (U2 (‖x‖ ^ 2 / 2)) (U3 (‖x‖ ^ 2 / 2)) :=
  kernelK_exp_radial hU hU1 hU2 x

/-- On the cell, `q K_q = G(|x|)`. -/
theorem qper_mul_kernelK_qper_of_mem_cell {U1 U2 U3 : ℝ → ℝ}
    (hU : ∀ s, HasDerivAt ucut (U1 s) s) (hU1 : ∀ s, HasDerivAt U1 (U2 s) s)
    (hU2 : ∀ s, HasDerivAt U2 (U3 s) s) {x : E 41} (hx : x ∈ cell) :
    qper x * kernelK qper x = radialG U1 U2 U3 ‖x‖ := by
  have hx' : ∀ i, x i ∈ Set.Icc (-10 : ℝ) 10 := hx
  have hbox : ∀ i, |x i| < 11 := fun i =>
    abs_lt.2 ⟨by linarith [(hx' i).1], by linarith [(hx' i).2]⟩
  rw [kernelK_qper_eq hbox, kernelK_exp_bump hU hU1 hU2, qper, Uper_eq_bump hbox]
  rfl

/-- Outside the cell, `|x| ≥ 8`. -/
theorem eight_le_norm_of_notMem_cell {x : E 41} (hx : x ∉ cell) : 8 ≤ ‖x‖ := by
  simp only [cell, Set.mem_ofPred_eq, not_forall, Set.mem_Icc, not_and_or, not_le] at hx
  obtain ⟨i, hi⟩ := hx
  have h1 := abs_apply_le_norm x i
  have h2 := le_abs_self (x i)
  have h3 := neg_abs_le (x i)
  rcases hi with hi | hi <;> linarith

/-- Polar coordinates in `E 41` for a radial function vanishing for `r ≥ 8`. -/
theorem integral_radial_eq {G : ℝ → ℝ} (hG : ∀ r, 8 ≤ r → G r = 0) :
    ∫ x : E 41, G ‖x‖ =
      41 * (volume (ball (0 : E 41) 1)).toReal * ∫ r in (0 : ℝ)..8, r ^ 40 * G r := by
  have hzero : ∀ y ∈ Set.Ioi (0 : ℝ) \ Set.Ioc 0 8, y ^ 40 * G y = 0 := by
    intro y hy
    rw [hG y (le_of_lt (not_le.1 fun h => hy.2 ⟨hy.1, h⟩)), mul_zero]
  have hI : ∫ y in Set.Ioi (0 : ℝ), y ^ 40 * G y = ∫ r in (0 : ℝ)..8, r ^ 40 * G r :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Set.Ioc_subset_Ioi_self (a := (8 : ℝ))) hzero).trans
      (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 8)).symm
  have hpolar := integral_fun_norm_addHaar (volume : Measure (E 41)) G
  rw [finrank_euclideanSpace_fin, nsmul_eq_mul, measureReal_def] at hpolar
  calc ∫ x : E 41, G ‖x‖
      = 41 * ((volume (ball (0 : E 41) 1)).toReal *
          ∫ y in Set.Ioi (0 : ℝ), y ^ 40 * G y) := hpolar
    _ = 41 * (volume (ball (0 : E 41) 1)).toReal * ∫ r in (0 : ℝ)..8, r ^ 40 * G r := by
      rw [hI]
      ring

end Periodic

/-- **The cell integral in polar coordinates.** If `U₁, U₂, U₃` are the first three derivatives
of `ũ` and vanish on `[32, ∞)`, then
`∫_{[-10, 10]⁴¹} q K_q = 41 |B₁| ∫₀⁸ r⁴⁰ e^{ũ(r²/2)} Kd 41 (r²/2) (-U₁) U₂ U₃ dr`
(with `U₁, U₂, U₃` evaluated at `r²/2`). -/
theorem cell_integral_eq {U1 U2 U3 : ℝ → ℝ} (hU : ∀ s, HasDerivAt ucut (U1 s) s)
    (hU1 : ∀ s, HasDerivAt U1 (U2 s) s) (hU2 : ∀ s, HasDerivAt U2 (U3 s) s)
    (hvan : ∀ s, 32 ≤ s → U1 s = 0 ∧ U2 s = 0 ∧ U3 s = 0) :
    ∫ x in cell, qper x * kernelK qper x =
      41 * (volume (Metric.ball (0 : E 41) 1)).toReal *
        ∫ r in (0 : ℝ)..8, r ^ 40 * Real.exp (ucut (r ^ 2 / 2)) *
          Kd 41 (r ^ 2 / 2) (-U1 (r ^ 2 / 2)) (U2 (r ^ 2 / 2)) (U3 (r ^ 2 / 2)) := by
  have h1 : ∫ x in cell, qper x * kernelK qper x = ∫ x in cell, radialG U1 U2 U3 ‖x‖ :=
    setIntegral_congr_fun measurableSet_cell fun x hx =>
      qper_mul_kernelK_qper_of_mem_cell hU hU1 hU2 hx
  have h2 : ∫ x in cell, radialG U1 U2 U3 ‖x‖ = ∫ x, radialG U1 U2 U3 ‖x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      radialG_eq_zero hvan (eight_le_norm_of_notMem_cell hx)
  rw [h1, h2, integral_radial_eq (G := radialG U1 U2 U3) fun r hr => radialG_eq_zero hvan hr]
  simp only [radialG, mul_assoc]

end Fisher41
