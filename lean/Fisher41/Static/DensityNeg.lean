/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Static.Periodic
import Fisher41.Static.Jcut
import Fisher41.Static.AveragingND
import Fisher41.Static.Envelope
import Fisher41.Heat.Domination

/-!
# The enveloped density `f_R` is admissible and has `D(f_R) < 0` for large `R`

Let `q = e^U` be the periodic density (`Fisher41.qper`), `γ = gaussian 41 (R²)` the Gaussian of
variance `R²`, `Z_R = ∫ q γ` and `f_R = q γ / Z_R` (`Fisher41.fR`). With `H = -∇² log q` we use
the four continuous, bounded functions

`g₁ = q K_q`, `g₂ = q ∑ᵢⱼ Hᵢⱼ²`, `g₃ = q ∑ᵢ Hᵢᵢ`, `g₄ = q`

(`Fisher41.DensityNeg.g1`, `Fisher41.DensityNeg.g2`, `Fisher41.DensityNeg.g3`, `Fisher41.qper`),
which are invariant under the lattice `20 ℤ⁴¹`.

## Main results

* `Fisher41.integral_cell_qper_mul_kernelK_eq`, `Fisher41.integral_cell_qper_mul_kernelK_le`,
  `Fisher41.integral_cell_qper_mul_kernelK_neg`: over the period cell `[-10, 10]⁴¹`,
  `∫ q K_q = ω J_cut ≤ ω (-5·10¹⁸ + 16) < 0`, where `ω = 41 |B₁|`.
* `Fisher41.abs_integral_mul_gaussian_sub_cell_le_of_add_latt`: Gaussian averaging of a
  continuous, `20 ℤ⁴¹`-invariant function `g` with `|g| ≤ M`,
  `|∫ g γ - 20⁻⁴¹ ∫_{cell} g| ≤ 8 · 41 · M · 20² / R²`.
* `Fisher41.one_le_integral_qper_mul_gaussian`, `Fisher41.fR_pos`, `Fisher41.contDiff_fR`,
  `Fisher41.integrable_fR`, `Fisher41.integral_fR`, `Fisher41.integrable_fisherDensity_fR`,
  `Fisher41.admissible_fR`: `f_R` is admissible for every `R > 0`.
* `Fisher41.kernelK_fR`, `Fisher41.mul_Dfun_fR_eq`: the correction formula
  `Z_R D(f_R) = E g₁ + 6 R⁻² E g₂ + 6 R⁻⁴ E g₃ + 82 R⁻⁶ Z_R`, where `E g = ∫ g γ`.
* `Fisher41.mul_Dfun_fR_le`, `Fisher41.Dfun_fR_neg_of_bounds`: for `R ≥ 1` and `|gₖ| ≤ Mₖ`,
  `Z_R D(f_R) ≤ 20⁻⁴¹ ∫_{cell} g₁ + (8 · 41 · M₁ · 20² + 6 M₂ + 6 M₃ + 82 M₄) / R²`, so
  `D(f_R) < 0` as soon as the second term is smaller than `-20⁻⁴¹ ∫_{cell} g₁`.
* `Fisher41.exists_forall_ge_Dfun_fR_neg`, `Fisher41.exists_Dfun_fR_neg`: `D(f_R) < 0` for all
  sufficiently large `R`.

## Proof sketch

Partial derivatives commute with translations, so `log q`, `H`, `∂H` and `K_q` inherit the
lattice invariance of `q`; they are continuous since `q` is smooth and positive, hence bounded
(every point has a lattice translate in the compact cell). The envelope only shifts `H` by
`R⁻² Id` (`Fisher41.kernelK_mul_gaussian`), which gives the correction formula by linearity of
the integral. Gaussian averaging (`Fisher41.abs_integral_mul_gaussian_sub_cell_le`) and the
polar-coordinate computation of the cell integral (`Fisher41.cell_integral_eq`,
`Fisher41.integral_Fcut_le_neg`) show that `E g₁` is close to the negative cell average of `g₁`,
while the remaining terms are `O(R⁻²)`.

Auxiliary lemmas live in the namespace `Fisher41.DensityNeg`.
-/

open MeasureTheory Real
open scoped ContDiff

noncomputable section

namespace Fisher41

namespace DensityNeg

/-! ### Translation invariance of derived quantities -/

section Translation

variable {d : ℕ}

/-- If `h` is invariant under the translation by `a`, so is each partial derivative `∂ᵢ h`. -/
theorem pd_add_of_forall_add {h : E d → ℝ} {a : E d} (ha : ∀ y, h (y + a) = h y) (i : Fin d)
    (x : E d) : pd h i (x + a) = pd h i x := by
  have hfun : (fun y => h (y + a)) = h := funext ha
  have hd : fderiv ℝ h (x + a) = fderiv ℝ h x := by
    rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := h) (x := x) a, hfun]
  unfold pd
  rw [hd]

/-- If `ρ` is invariant under the translation by `a`, so is `H = -∇² log ρ`. -/
theorem negHess_add_of_forall_add {ρ : E d → ℝ} {a : E d} (ha : ∀ y, ρ (y + a) = ρ y)
    (i j : Fin d) (x : E d) : negHess ρ i j (x + a) = negHess ρ i j x := by
  have hlog : ∀ y, Real.log (ρ (y + a)) = Real.log (ρ y) := fun y => by rw [ha]
  have h1 : ∀ y, pd (fun y => Real.log (ρ y)) i (y + a) = pd (fun y => Real.log (ρ y)) i y :=
    pd_add_of_forall_add (h := fun y => Real.log (ρ y)) hlog i
  show -pd (pd (fun y => Real.log (ρ y)) i) j (x + a) =
    -pd (pd (fun y => Real.log (ρ y)) i) j x
  rw [pd_add_of_forall_add (h := pd (fun y => Real.log (ρ y)) i) h1 j x]

/-- If `ρ` is invariant under the translation by `a`, so is `K_ρ`. -/
theorem kernelK_add_of_forall_add {ρ : E d → ℝ} {a : E d} (ha : ∀ y, ρ (y + a) = ρ y)
    (x : E d) : kernelK ρ (x + a) = kernelK ρ x := by
  have h1 : ∀ i j, negHess ρ i j (x + a) = negHess ρ i j x := fun i j =>
    negHess_add_of_forall_add ha i j x
  have h2 : ∀ i j k, pd (negHess ρ i j) k (x + a) = pd (negHess ρ i j) k x := fun i j k =>
    pd_add_of_forall_add (h := negHess ρ i j) (negHess_add_of_forall_add ha i j) k x
  simp only [kernelK, h1, h2]

end Translation

/-! ### Smoothness and continuity -/

/-- `log q` is smooth. -/
theorem contDiff_log_qper : ContDiff ℝ ∞ fun y => Real.log (qper y) :=
  contDiff_qper.log fun y => (qper_pos y).ne'

/-- The entries of `H = -∇² log q` are smooth. -/
theorem contDiff_negHess_qper (i j : Fin 41) : ContDiff ℝ ∞ (negHess qper i j) := by
  show ContDiff ℝ ∞ fun x => -pd (pd (fun y => Real.log (qper y)) i) j x
  exact (Envelope.contDiff_pd (Envelope.contDiff_pd contDiff_log_qper i) j).neg

/-- The entries of `H = -∇² log q` are continuous. -/
theorem continuous_negHess_qper (i j : Fin 41) : Continuous (negHess qper i j) :=
  (contDiff_negHess_qper i j).continuous

/-- `K_q` is continuous. -/
theorem continuous_kernelK_qper : Continuous (kernelK qper) := by
  have hH := continuous_negHess_qper
  have hdH : ∀ i j k, Continuous (pd (negHess qper i j) k) := fun i j k =>
    (Envelope.contDiff_pd (contDiff_negHess_qper i j) k).continuous
  show Continuous fun x => (∑ i, ∑ j, ∑ k, (pd (negHess qper i j) k x) ^ 2) +
    2 * ∑ i, ∑ j, ∑ k, negHess qper i j x * negHess qper j k x * negHess qper k i x
  refine Continuous.add ?_ (continuous_const.mul ?_)
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => (hdH i j k).pow 2
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => ((hH i j).mul (hH j k)).mul (hH k i)

/-- The Gaussian is smooth. -/
theorem contDiff_gaussian (d : ℕ) (t : ℝ) : ContDiff ℝ ∞ (gaussian d t) := by
  show ContDiff ℝ ∞ fun x : E d => (2 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * t))
  exact contDiff_const.mul ((contDiff_norm_sq ℝ).neg.div_const _).exp

/-! ### Continuous lattice-invariant functions are bounded -/

/-- The period cell `[-10, 10]⁴¹` is compact. -/
theorem isCompact_cell : IsCompact cell := by
  have h : cell = WithLp.toLp 2 '' Set.univ.pi fun _ : Fin 41 => Set.Icc (-10 : ℝ) 10 := by
    ext x
    refine ⟨fun hx => ⟨WithLp.ofLp x, fun i _ => hx i, WithLp.toLp_ofLp _ x⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩ i
    exact hy i (Set.mem_univ i)
  rw [h]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

/-- Every point has a lattice translate in the period cell. -/
theorem exists_sub_latt_mem_cell (x : E 41) : ∃ z : Fin 41 → ℤ, x - latt z ∈ cell := by
  refine ⟨fun i => round (x i / 20), ?_⟩
  intro i
  have h1 : x i - 20 * ((round (x i / 20) : ℤ) : ℝ) = 20 * (x i / 20 - round (x i / 20)) := by
    ring
  have h2 : |x i - 20 * ((round (x i / 20) : ℤ) : ℝ)| ≤ 10 := by
    rw [h1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 20)]
    calc 20 * |x i / 20 - round (x i / 20)| ≤ 20 * (1 / 2) :=
          mul_le_mul_of_nonneg_left (abs_sub_round _) (by norm_num)
      _ = 10 := by norm_num
  simp only [PiLp.sub_apply, Periodic.latt_apply, Set.mem_Icc]
  exact abs_le.1 h2

/-- A continuous function invariant under the lattice `20 ℤ⁴¹` is bounded. -/
theorem exists_abs_le_of_add_latt {g : E 41 → ℝ} (hc : Continuous g)
    (hper : ∀ x z, g (x + latt z) = g x) : ∃ M, ∀ x, |g x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_cell.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨z, hz⟩ := exists_sub_latt_mem_cell x
  have h := hM _ hz
  rw [Real.norm_eq_abs, ← hper (x - latt z) z, sub_add_cancel] at h
  exact h

/-- Invariance under `20 ℤ⁴¹` gives the coordinatewise periodicity used in
`Fisher41.abs_integral_mul_gaussian_sub_cell_le`. -/
theorem add_single_of_add_latt {g : E 41 → ℝ} (hper : ∀ x z, g (x + latt z) = g x)
    (x : E 41) (i : Fin 41) : g (x + (20 : ℝ) • EuclideanSpace.single i 1) = g x := by
  rw [← Periodic.latt_single, hper]

/-! ### The periodic functions `g₁, g₂, g₃` -/

/-- `g₁ = q K_q`. -/
def g1 (x : E 41) : ℝ := qper x * kernelK qper x

/-- `g₂ = q ∑ᵢⱼ Hᵢⱼ²`, where `H = -∇² log q`. -/
def g2 (x : E 41) : ℝ := qper x * ∑ i, ∑ j, (negHess qper i j x) ^ 2

/-- `g₃ = q ∑ᵢ Hᵢᵢ`, where `H = -∇² log q`. -/
def g3 (x : E 41) : ℝ := qper x * ∑ i, negHess qper i i x

/-- `g₁` is invariant under the lattice `20 ℤ⁴¹`. -/
theorem g1_add_latt (x : E 41) (z : Fin 41 → ℤ) : g1 (x + latt z) = g1 x := by
  simp only [g1, qper_add_latt,
    kernelK_add_of_forall_add (ρ := qper) (a := latt z) fun y => qper_add_latt y z]

/-- `g₂` is invariant under the lattice `20 ℤ⁴¹`. -/
theorem g2_add_latt (x : E 41) (z : Fin 41 → ℤ) : g2 (x + latt z) = g2 x := by
  simp only [g2, qper_add_latt,
    negHess_add_of_forall_add (ρ := qper) (a := latt z) fun y => qper_add_latt y z]

/-- `g₃` is invariant under the lattice `20 ℤ⁴¹`. -/
theorem g3_add_latt (x : E 41) (z : Fin 41 → ℤ) : g3 (x + latt z) = g3 x := by
  simp only [g3, qper_add_latt,
    negHess_add_of_forall_add (ρ := qper) (a := latt z) fun y => qper_add_latt y z]

/-- `g₁` is `20`-periodic in each coordinate direction. -/
theorem g1_add_single (x : E 41) (i : Fin 41) :
    g1 (x + (20 : ℝ) • EuclideanSpace.single i 1) = g1 x :=
  add_single_of_add_latt g1_add_latt x i

/-- `g₂` is `20`-periodic in each coordinate direction. -/
theorem g2_add_single (x : E 41) (i : Fin 41) :
    g2 (x + (20 : ℝ) • EuclideanSpace.single i 1) = g2 x :=
  add_single_of_add_latt g2_add_latt x i

/-- `g₃` is `20`-periodic in each coordinate direction. -/
theorem g3_add_single (x : E 41) (i : Fin 41) :
    g3 (x + (20 : ℝ) • EuclideanSpace.single i 1) = g3 x :=
  add_single_of_add_latt g3_add_latt x i

/-- `g₁` is continuous. -/
theorem continuous_g1 : Continuous g1 := by
  show Continuous fun x => qper x * kernelK qper x
  exact contDiff_qper.continuous.mul continuous_kernelK_qper

/-- `g₂` is continuous. -/
theorem continuous_g2 : Continuous g2 := by
  show Continuous fun x => qper x * ∑ i, ∑ j, (negHess qper i j x) ^ 2
  exact contDiff_qper.continuous.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (continuous_negHess_qper i j).pow 2)

/-- `g₃` is continuous. -/
theorem continuous_g3 : Continuous g3 := by
  show Continuous fun x => qper x * ∑ i, negHess qper i i x
  exact contDiff_qper.continuous.mul
    (continuous_finsetSum _ fun i _ => continuous_negHess_qper i i)

/-- `g₁` is bounded. -/
theorem exists_abs_g1_le : ∃ M, ∀ x, |g1 x| ≤ M :=
  exists_abs_le_of_add_latt continuous_g1 g1_add_latt

/-- `g₂` is bounded. -/
theorem exists_abs_g2_le : ∃ M, ∀ x, |g2 x| ≤ M :=
  exists_abs_le_of_add_latt continuous_g2 g2_add_latt

/-- `g₃` is bounded. -/
theorem exists_abs_g3_le : ∃ M, ∀ x, |g3 x| ≤ M :=
  exists_abs_le_of_add_latt continuous_g3 g3_add_latt

/-- `|∇ log q|² = ∑ᵢ (∂ᵢ log q)²` is bounded. -/
theorem exists_abs_sum_sq_pd_log_qper_le :
    ∃ M, ∀ x, |∑ i, (pd (fun y => Real.log (qper y)) i x) ^ 2| ≤ M := by
  have hper : ∀ (y : E 41) (z : Fin 41 → ℤ), Real.log (qper (y + latt z)) = Real.log (qper y) :=
    fun y z => by rw [qper_add_latt]
  refine exists_abs_le_of_add_latt
    (g := fun x => ∑ i, (pd (fun y => Real.log (qper y)) i x) ^ 2)
    (continuous_finsetSum _ fun i _ =>
      (Envelope.contDiff_pd contDiff_log_qper i).continuous.pow 2) fun x z => ?_
  simp only [pd_add_of_forall_add (h := fun y => Real.log (qper y)) (a := latt z) (hper · z)]

/-! ### Integrals against the Gaussian -/

/-- `ω₄₁ = 41 |B₁|` is positive. -/
theorem volume_ball_toReal_pos : 0 < (volume (Metric.ball (0 : E 41) 1)).toReal :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : E 41) one_pos).ne'
    measure_ball_lt_top.ne

/-- A bounded continuous function times `γ_{R²}` is integrable. -/
theorem integrable_mul_gaussian {g : E 41 → ℝ} {M R : ℝ} (hR : 0 < R) (hc : Continuous g)
    (hM : ∀ x, |g x| ≤ M) : Integrable fun x => g x * gaussian 41 (R ^ 2) x :=
  (integrable_gaussian (d := 41) (t := R ^ 2) (by positivity)).bdd_mul hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

/-- If `|g| ≤ M`, then `|∫ g γ_{R²}| ≤ M`. -/
theorem abs_integral_mul_gaussian_le {g : E 41 → ℝ} {M R : ℝ} (hR : 0 < R)
    (hM : ∀ x, |g x| ≤ M) : |∫ x, g x * gaussian 41 (R ^ 2) x| ≤ M := by
  have hR2 : 0 < R ^ 2 := by positivity
  rw [← Real.norm_eq_abs]
  calc ‖∫ x, g x * gaussian 41 (R ^ 2) x‖ ≤ ∫ x, M * gaussian 41 (R ^ 2) x :=
        norm_integral_le_of_norm_le ((integrable_gaussian hR2).const_mul M)
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussian_pos hR2 x)]
            exact mul_le_mul_of_nonneg_right (hM x) (gaussian_pos hR2 x).le)
    _ = M := by rw [integral_const_mul, integral_gaussian_eq_one hR2, mul_one]

end DensityNeg

/-- **Gaussian averaging** for a continuous function `g` invariant under the lattice `20 ℤ⁴¹`
with `|g| ≤ M`: `|∫ g γ_{R²} - 20⁻⁴¹ ∫_{[-10, 10]⁴¹} g| ≤ 8 · 41 · M · 20² / R²`. -/
theorem abs_integral_mul_gaussian_sub_cell_le_of_add_latt {g : E 41 → ℝ} {M R : ℝ}
    (hR : 0 < R) (hc : Continuous g) (hper : ∀ x z, g (x + latt z) = g x)
    (hM : ∀ x, |g x| ≤ M) :
    |(∫ x, g x * gaussian 41 (R ^ 2) x) - (∫ x in cell, g x) / 20 ^ 41| ≤
      8 * 41 * M * 20 ^ 2 / R ^ 2 := by
  have h := abs_integral_mul_gaussian_sub_cell_le (d := 41) (L := 20) (a := -10) (M := M)
    (by norm_num) hR hc (DensityNeg.add_single_of_add_latt hper) hM
  rw [show (-10 : ℝ) + 20 = 10 by norm_num] at h
  refine h.trans (le_of_eq ?_)
  norm_num

namespace DensityNeg

/-- Gaussian averaging for `g₁ = q K_q`. -/
theorem abs_integral_g1_mul_gaussian_sub_cell_le {M R : ℝ} (hR : 0 < R)
    (hM : ∀ x, |g1 x| ≤ M) :
    |(∫ x, g1 x * gaussian 41 (R ^ 2) x) - (∫ x in cell, g1 x) / 20 ^ 41| ≤
      8 * 41 * M * 20 ^ 2 / R ^ 2 :=
  abs_integral_mul_gaussian_sub_cell_le_of_add_latt hR continuous_g1 g1_add_latt hM

/-- Gaussian averaging for `g₂ = q ∑ᵢⱼ Hᵢⱼ²`. -/
theorem abs_integral_g2_mul_gaussian_sub_cell_le {M R : ℝ} (hR : 0 < R)
    (hM : ∀ x, |g2 x| ≤ M) :
    |(∫ x, g2 x * gaussian 41 (R ^ 2) x) - (∫ x in cell, g2 x) / 20 ^ 41| ≤
      8 * 41 * M * 20 ^ 2 / R ^ 2 :=
  abs_integral_mul_gaussian_sub_cell_le_of_add_latt hR continuous_g2 g2_add_latt hM

/-- Gaussian averaging for `g₃ = q ∑ᵢ Hᵢᵢ`. -/
theorem abs_integral_g3_mul_gaussian_sub_cell_le {M R : ℝ} (hR : 0 < R)
    (hM : ∀ x, |g3 x| ≤ M) :
    |(∫ x, g3 x * gaussian 41 (R ^ 2) x) - (∫ x in cell, g3 x) / 20 ^ 41| ≤
      8 * 41 * M * 20 ^ 2 / R ^ 2 :=
  abs_integral_mul_gaussian_sub_cell_le_of_add_latt hR continuous_g3 g3_add_latt hM

/-- Gaussian averaging for `g₄ = q`. -/
theorem abs_integral_qper_mul_gaussian_sub_cell_le {M R : ℝ} (hR : 0 < R)
    (hM : ∀ x, |qper x| ≤ M) :
    |(∫ x, qper x * gaussian 41 (R ^ 2) x) - (∫ x in cell, qper x) / 20 ^ 41| ≤
      8 * 41 * M * 20 ^ 2 / R ^ 2 :=
  abs_integral_mul_gaussian_sub_cell_le_of_add_latt hR contDiff_qper.continuous qper_add_latt hM

end DensityNeg

/-! ### The cell average of `q K_q` is negative -/

/-- **The cell integral of `q K_q`** in polar coordinates:
`∫_{[-10, 10]⁴¹} q K_q = 41 |B₁| ∫₀⁸ Fcut`. -/
theorem integral_cell_qper_mul_kernelK_eq :
    ∫ x in cell, qper x * kernelK qper x =
      41 * (volume (Metric.ball (0 : E 41) 1)).toReal * ∫ r in (0 : ℝ)..8, Fcut r :=
  cell_integral_eq hasDerivAt_ucut hasDerivAt_uc1 hasDerivAt_uc2 fun _ hs =>
    ⟨uc1_eq_zero hs, uc2_eq_zero hs, uc3_eq_zero hs⟩

/-- `∫_{[-10, 10]⁴¹} q K_q ≤ 41 |B₁| (-5·10¹⁸ + 16)`. -/
theorem integral_cell_qper_mul_kernelK_le :
    ∫ x in cell, qper x * kernelK qper x ≤
      41 * (volume (Metric.ball (0 : E 41) 1)).toReal * (-5000000000000000000 + 16) := by
  rw [integral_cell_qper_mul_kernelK_eq]
  exact mul_le_mul_of_nonneg_left integral_Fcut_le_neg
    (mul_pos (by norm_num) DensityNeg.volume_ball_toReal_pos).le

/-- **The cell average of `q K_q` is negative.** -/
theorem integral_cell_qper_mul_kernelK_neg : ∫ x in cell, qper x * kernelK qper x < 0 := by
  have h := integral_cell_qper_mul_kernelK_le
  have hω := DensityNeg.volume_ball_toReal_pos
  linarith

/-! ### Admissibility of `f_R` -/

/-- `Z_R = ∫ q γ_{R²} ≥ 1`. -/
theorem one_le_integral_qper_mul_gaussian {R : ℝ} (hR : 0 < R) :
    1 ≤ ∫ x, qper x * gaussian 41 (R ^ 2) x := by
  have hR2 : 0 < R ^ 2 := by positivity
  obtain ⟨C, hC⟩ := exists_abs_qper_le
  calc (1 : ℝ) = ∫ x, gaussian 41 (R ^ 2) x := (integral_gaussian_eq_one hR2).symm
    _ ≤ ∫ x, qper x * gaussian 41 (R ^ 2) x :=
      integral_mono (integrable_gaussian hR2)
        (DensityNeg.integrable_mul_gaussian hR contDiff_qper.continuous hC) fun x =>
          le_mul_of_one_le_left (gaussian_pos hR2 x).le (one_le_qper x)

/-- `f_R > 0`. -/
theorem fR_pos {R : ℝ} (hR : 0 < R) (x : E 41) : 0 < fR R x := by
  have hZ := one_le_integral_qper_mul_gaussian hR
  rw [fR]
  exact div_pos (mul_pos (qper_pos x) (gaussian_pos (by positivity) x)) (by linarith)

/-- `f_R` is smooth. -/
theorem contDiff_fR (R : ℝ) : ContDiff ℝ ∞ (fR R) := by
  show ContDiff ℝ ∞ fun x => qper x * gaussian 41 (R ^ 2) x / ∫ y, qper y * gaussian 41 (R ^ 2) y
  exact (contDiff_qper.mul (DensityNeg.contDiff_gaussian 41 _)).div_const _

/-- `f_R` is integrable. -/
theorem integrable_fR {R : ℝ} (hR : 0 < R) : Integrable (fR R) := by
  obtain ⟨C, hC⟩ := exists_abs_qper_le
  show Integrable fun x => qper x * gaussian 41 (R ^ 2) x / ∫ y, qper y * gaussian 41 (R ^ 2) y
  exact (DensityNeg.integrable_mul_gaussian hR contDiff_qper.continuous hC).div_const _

/-- `f_R` has mass one. -/
theorem integral_fR {R : ℝ} (hR : 0 < R) : ∫ x, fR R x = 1 := by
  have hZ := one_le_integral_qper_mul_gaussian hR
  show ∫ x, qper x * gaussian 41 (R ^ 2) x / (∫ y, qper y * gaussian 41 (R ^ 2) y) = 1
  rw [integral_div]
  exact div_self (lt_of_lt_of_le one_pos hZ).ne'

/-- `f_R = Z_R⁻¹ q γ_{R²}`, the form used in `Fisher41.Static.Envelope`. -/
theorem fR_eq (R : ℝ) :
    fR R = fun y => (∫ x, qper x * gaussian 41 (R ^ 2) x)⁻¹ * qper y * gaussian 41 (R ^ 2) y := by
  funext y
  rw [fR]
  ring

/-- The Fisher integrand of `f_R` is continuous. -/
theorem continuous_fisherDensity_fR {R : ℝ} (hR : 0 < R) :
    Continuous (fisherDensity (fR R)) := by
  have hlog : ContDiff ℝ ∞ fun y => Real.log (fR R y) :=
    (contDiff_fR R).log fun y => (fR_pos hR y).ne'
  show Continuous fun x => fR R x * ∑ i, (pd (fun y => Real.log (fR R y)) i x) ^ 2
  exact (contDiff_fR R).continuous.mul (continuous_finsetSum _ fun i _ =>
    (Envelope.contDiff_pd hlog i).continuous.pow 2)

/-- The Fisher integrand of `f_R` is integrable: it is dominated by
`C (1 + ‖x‖)² γ_{R²}(x)`. -/
theorem integrable_fisherDensity_fR {R : ℝ} (hR : 0 < R) :
    Integrable (fisherDensity (fR R)) := by
  have hR2 : 0 < R ^ 2 := by positivity
  have hZ1 := one_le_integral_qper_mul_gaussian hR
  have hZpos : 0 < (∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ := inv_pos.2 (by linarith)
  have hZinv : (∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hZ1
  obtain ⟨MS, hMS⟩ := DensityNeg.exists_abs_sum_sq_pd_log_qper_le
  obtain ⟨M4, hM4⟩ := exists_abs_qper_le
  have hMS0 : 0 ≤ MS := (abs_nonneg _).trans (hMS 0)
  have hM40 : 0 ≤ M4 := (abs_nonneg _).trans (hM4 0)
  refine PolyGauss.integrable hR2 ⟨M4 * (82 * (MS + 1 / (R ^ 2) ^ 2)), 2, fun x => ?_⟩
    (continuous_fisherDensity_fR hR).aestronglyMeasurable
  have hγ := gaussian_pos hR2 x
  have hqM : qper x ≤ M4 := (le_abs_self _).trans (hM4 x)
  have hP : (1 : ℝ) ≤ (1 + ‖x‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg x])
  have hterm : ∀ i, 2 * ((pd (fun y => Real.log (qper y)) i x) ^ 2 + (x i / R ^ 2) ^ 2) ≤
      2 * (MS + 1 / (R ^ 2) ^ 2) * (1 + ‖x‖) ^ 2 := by
    intro i
    have h1 : (pd (fun y => Real.log (qper y)) i x) ^ 2 ≤ MS :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (pd (fun y => Real.log (qper y)) j x))
        (Finset.mem_univ i)).trans ((le_abs_self _).trans (hMS x))
    have hxi : |x i| ≤ 1 + ‖x‖ := by linarith [Periodic.abs_apply_le_norm x i]
    have h3 : x i ^ 2 ≤ (1 + ‖x‖) ^ 2 := sq_le_sq' (abs_le.1 hxi).1 (abs_le.1 hxi).2
    have h2 : (x i / R ^ 2) ^ 2 ≤ 1 / (R ^ 2) ^ 2 * (1 + ‖x‖) ^ 2 :=
      calc (x i / R ^ 2) ^ 2 = 1 / (R ^ 2) ^ 2 * x i ^ 2 := by ring
        _ ≤ 1 / (R ^ 2) ^ 2 * (1 + ‖x‖) ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    have h4 : MS ≤ MS * (1 + ‖x‖) ^ 2 := le_mul_of_one_le_right hMS0 hP
    calc 2 * ((pd (fun y => Real.log (qper y)) i x) ^ 2 + (x i / R ^ 2) ^ 2)
        ≤ 2 * (MS * (1 + ‖x‖) ^ 2 + 1 / (R ^ 2) ^ 2 * (1 + ‖x‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add (h1.trans h4) h2) (by norm_num)
      _ = 2 * (MS + 1 / (R ^ 2) ^ 2) * (1 + ‖x‖) ^ 2 := by ring
  have hsum : ∑ i, 2 * ((pd (fun y => Real.log (qper y)) i x) ^ 2 + (x i / R ^ 2) ^ 2) ≤
      82 * (MS + 1 / (R ^ 2) ^ 2) * (1 + ‖x‖) ^ 2 := by
    calc _ ≤ ∑ _i : Fin 41, 2 * (MS + 1 / (R ^ 2) ^ 2) * (1 + ‖x‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 82 * (MS + 1 / (R ^ 2) ^ 2) * (1 + ‖x‖) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hS0 : 0 ≤ ∑ i, 2 * ((pd (fun y => Real.log (qper y)) i x) ^ 2 + (x i / R ^ 2) ^ 2) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hF : |fisherDensity (fR R) x| ≤ (∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ * qper x *
      gaussian 41 (R ^ 2) x *
        ∑ i, 2 * ((pd (fun y => Real.log (qper y)) i x) ^ 2 + (x i / R ^ 2) ^ 2) := by
    rw [fR_eq]
    exact abs_fisherDensity_mul_gaussian_le contDiff_qper qper_pos hZpos hR x
  calc |fisherDensity (fR R) x|
      ≤ (∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ * qper x * gaussian 41 (R ^ 2) x *
          ∑ i, 2 * ((pd (fun y => Real.log (qper y)) i x) ^ 2 + (x i / R ^ 2) ^ 2) := hF
    _ ≤ 1 * M4 * gaussian 41 (R ^ 2) x * (82 * (MS + 1 / (R ^ 2) ^ 2) * (1 + ‖x‖) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul hZinv hqM (qper_pos x).le zero_le_one) hγ.le) hsum hS0
          (mul_nonneg (mul_nonneg zero_le_one hM40) hγ.le)
    _ = M4 * (82 * (MS + 1 / (R ^ 2) ^ 2)) * (1 + ‖x‖) ^ 2 * gaussian 41 (R ^ 2) x := by ring

/-- **`f_R` is an admissible density** for every `R > 0`. -/
theorem admissible_fR {R : ℝ} (hR : 0 < R) : Admissible (fR R) where
  pos := fR_pos hR
  smooth := contDiff_fR R
  integrable := integrable_fR hR
  mass_one := integral_fR hR
  fisher_integrable := integrable_fisherDensity_fR hR

/-! ### The correction formula -/

/-- **The kernel of `f_R`**: `K_{f_R} = K_q + 6 R⁻² ∑ᵢⱼ Hᵢⱼ² + 6 R⁻⁴ ∑ᵢ Hᵢᵢ + 82 R⁻⁶`, where
`H = -∇² log q`. -/
theorem kernelK_fR {R : ℝ} (hR : 0 < R) (x : E 41) :
    kernelK (fR R) x = kernelK qper x + 6 / R ^ 2 * (∑ i, ∑ j, (negHess qper i j x) ^ 2) +
      6 / R ^ 4 * (∑ i, negHess qper i i x) + 2 * 41 / R ^ 6 := by
  have hZ : 0 < (∫ x, qper x * gaussian 41 (R ^ 2) x)⁻¹ :=
    inv_pos.2 (lt_of_lt_of_le one_pos (one_le_integral_qper_mul_gaussian hR))
  rw [fR_eq, kernelK_mul_gaussian contDiff_qper qper_pos hZ hR x]
  norm_num

/-- **The correction formula**: with `E g = ∫ g γ_{R²}` and `Z_R = ∫ q γ_{R²}`,
`Z_R D(f_R) = E g₁ + 6 R⁻² E g₂ + 6 R⁻⁴ E g₃ + 82 R⁻⁶ Z_R`. -/
theorem mul_Dfun_fR_eq {R : ℝ} (hR : 0 < R) :
    (∫ x, qper x * gaussian 41 (R ^ 2) x) * Dfun (fR R) =
      (∫ x, DensityNeg.g1 x * gaussian 41 (R ^ 2) x) +
        6 / R ^ 2 * (∫ x, DensityNeg.g2 x * gaussian 41 (R ^ 2) x) +
        6 / R ^ 4 * (∫ x, DensityNeg.g3 x * gaussian 41 (R ^ 2) x) +
        2 * 41 / R ^ 6 * ∫ x, qper x * gaussian 41 (R ^ 2) x := by
  have hZ : (∫ x, qper x * gaussian 41 (R ^ 2) x) ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_integral_qper_mul_gaussian hR)).ne'
  obtain ⟨M1, hM1⟩ := DensityNeg.exists_abs_g1_le
  obtain ⟨M2, hM2⟩ := DensityNeg.exists_abs_g2_le
  obtain ⟨M3, hM3⟩ := DensityNeg.exists_abs_g3_le
  obtain ⟨M4, hM4⟩ := exists_abs_qper_le
  have i1 : Integrable fun x => DensityNeg.g1 x * gaussian 41 (R ^ 2) x :=
    DensityNeg.integrable_mul_gaussian hR DensityNeg.continuous_g1 hM1
  have i2 : Integrable fun x => 6 / R ^ 2 * (DensityNeg.g2 x * gaussian 41 (R ^ 2) x) :=
    (DensityNeg.integrable_mul_gaussian hR DensityNeg.continuous_g2 hM2).const_mul _
  have i3 : Integrable fun x => 6 / R ^ 4 * (DensityNeg.g3 x * gaussian 41 (R ^ 2) x) :=
    (DensityNeg.integrable_mul_gaussian hR DensityNeg.continuous_g3 hM3).const_mul _
  have i4 : Integrable fun x => 2 * 41 / R ^ 6 * (qper x * gaussian 41 (R ^ 2) x) :=
    (DensityNeg.integrable_mul_gaussian hR contDiff_qper.continuous hM4).const_mul _
  have i34 : Integrable fun x => 6 / R ^ 4 * (DensityNeg.g3 x * gaussian 41 (R ^ 2) x) +
      2 * 41 / R ^ 6 * (qper x * gaussian 41 (R ^ 2) x) := i3.add i4
  have i234 : Integrable fun x => 6 / R ^ 2 * (DensityNeg.g2 x * gaussian 41 (R ^ 2) x) +
      (6 / R ^ 4 * (DensityNeg.g3 x * gaussian 41 (R ^ 2) x) +
        2 * 41 / R ^ 6 * (qper x * gaussian 41 (R ^ 2) x)) := i2.add i34
  have hpt : ∀ x, fR R x * kernelK (fR R) x = (∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ *
      (DensityNeg.g1 x * gaussian 41 (R ^ 2) x +
        (6 / R ^ 2 * (DensityNeg.g2 x * gaussian 41 (R ^ 2) x) +
          (6 / R ^ 4 * (DensityNeg.g3 x * gaussian 41 (R ^ 2) x) +
            2 * 41 / R ^ 6 * (qper x * gaussian 41 (R ^ 2) x)))) := by
    intro x
    rw [kernelK_fR hR x, fR, DensityNeg.g1, DensityNeg.g2, DensityNeg.g3]
    ring
  have hD : Dfun (fR R) = (∫ y, qper y * gaussian 41 (R ^ 2) y)⁻¹ *
      ((∫ x, DensityNeg.g1 x * gaussian 41 (R ^ 2) x) +
        ((6 / R ^ 2 * ∫ x, DensityNeg.g2 x * gaussian 41 (R ^ 2) x) +
          ((6 / R ^ 4 * ∫ x, DensityNeg.g3 x * gaussian 41 (R ^ 2) x) +
            2 * 41 / R ^ 6 * ∫ x, qper x * gaussian 41 (R ^ 2) x))) := by
    simp only [Dfun, hpt]
    rw [integral_const_mul, integral_add i1 i234, integral_add i2 i34, integral_add i3 i4,
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hD, ← mul_assoc, mul_inv_cancel₀ hZ, one_mul]
  ring

/-! ### Negativity of `D(f_R)` -/

/-- **Quantitative bound.** For `R ≥ 1` and bounds `|g₁| ≤ M₁`, `|g₂| ≤ M₂`, `|g₃| ≤ M₃`,
`|q| ≤ M₄`: `Z_R D(f_R) ≤ 20⁻⁴¹ ∫_{cell} g₁ + (8 · 41 · M₁ · 20² + 6 M₂ + 6 M₃ + 82 M₄) / R²`. -/
theorem mul_Dfun_fR_le {R M1 M2 M3 M4 : ℝ} (hR : 1 ≤ R)
    (hM1 : ∀ x, |DensityNeg.g1 x| ≤ M1) (hM2 : ∀ x, |DensityNeg.g2 x| ≤ M2)
    (hM3 : ∀ x, |DensityNeg.g3 x| ≤ M3) (hM4 : ∀ x, |qper x| ≤ M4) :
    (∫ x, qper x * gaussian 41 (R ^ 2) x) * Dfun (fR R) ≤
      (∫ x in cell, DensityNeg.g1 x) / 20 ^ 41 +
        (8 * 41 * M1 * 20 ^ 2 + 6 * M2 + 6 * M3 + 2 * 41 * M4) / R ^ 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hR2 : 0 < R ^ 2 := by positivity
  have hM3' : 0 ≤ M3 := (abs_nonneg _).trans (hM3 0)
  have hM4' : 0 ≤ M4 := (abs_nonneg _).trans (hM4 0)
  have hE1 : ∫ x, DensityNeg.g1 x * gaussian 41 (R ^ 2) x ≤
      (∫ x in cell, DensityNeg.g1 x) / 20 ^ 41 + 8 * 41 * M1 * 20 ^ 2 / R ^ 2 :=
    sub_le_iff_le_add'.1 (abs_le.1
      (DensityNeg.abs_integral_g1_mul_gaussian_sub_cell_le hR0 hM1)).2
  have h2 : 6 / R ^ 2 * ∫ x, DensityNeg.g2 x * gaussian 41 (R ^ 2) x ≤ 6 / R ^ 2 * M2 :=
    mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (DensityNeg.abs_integral_mul_gaussian_le hR0 hM2)) (by positivity)
  have h3 : 6 / R ^ 4 * ∫ x, DensityNeg.g3 x * gaussian 41 (R ^ 2) x ≤ 6 / R ^ 2 * M3 :=
    (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (DensityNeg.abs_integral_mul_gaussian_le hR0 hM3))
        (by positivity)).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hR2 (pow_le_pow_right₀ hR (by norm_num)))
        hM3')
  have h4 : 2 * 41 / R ^ 6 * ∫ x, qper x * gaussian 41 (R ^ 2) x ≤ 2 * 41 / R ^ 2 * M4 :=
    (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (DensityNeg.abs_integral_mul_gaussian_le hR0 hM4))
        (by positivity)).trans
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hR2 (pow_le_pow_right₀ hR (by norm_num)))
        hM4')
  rw [mul_Dfun_fR_eq hR0]
  calc _ ≤ (∫ x in cell, DensityNeg.g1 x) / 20 ^ 41 + 8 * 41 * M1 * 20 ^ 2 / R ^ 2 +
          6 / R ^ 2 * M2 + 6 / R ^ 2 * M3 + 2 * 41 / R ^ 2 * M4 :=
        add_le_add (add_le_add (add_le_add hE1 h2) h3) h4
    _ = _ := by ring

/-- **Explicit criterion.** If `R ≥ 1`, `|g₁| ≤ M₁`, `|g₂| ≤ M₂`, `|g₃| ≤ M₃`, `|q| ≤ M₄` and
`(8 · 41 · M₁ · 20² + 6 M₂ + 6 M₃ + 82 M₄) / R² < -20⁻⁴¹ ∫_{cell} g₁`, then `D(f_R) < 0`. -/
theorem Dfun_fR_neg_of_bounds {R M1 M2 M3 M4 : ℝ} (hR : 1 ≤ R)
    (hM1 : ∀ x, |DensityNeg.g1 x| ≤ M1) (hM2 : ∀ x, |DensityNeg.g2 x| ≤ M2)
    (hM3 : ∀ x, |DensityNeg.g3 x| ≤ M3) (hM4 : ∀ x, |qper x| ≤ M4)
    (hbig : (8 * 41 * M1 * 20 ^ 2 + 6 * M2 + 6 * M3 + 2 * 41 * M4) / R ^ 2 <
      -((∫ x in cell, DensityNeg.g1 x) / 20 ^ 41)) :
    Dfun (fR R) < 0 := by
  have hle := mul_Dfun_fR_le hR hM1 hM2 hM3 hM4
  have hZ := one_le_integral_qper_mul_gaussian (lt_of_lt_of_le one_pos hR)
  have hZD : (∫ x, qper x * gaussian 41 (R ^ 2) x) * Dfun (fR R) < 0 :=
    hle.trans_lt (by linarith)
  by_contra hD
  have h0 := mul_nonneg (by linarith : (0 : ℝ) ≤ ∫ x, qper x * gaussian 41 (R ^ 2) x)
    (not_lt.1 hD)
  linarith

/-- **`D(f_R) < 0` for all sufficiently large `R`.** -/
theorem exists_forall_ge_Dfun_fR_neg : ∃ R₀ > 0, ∀ R ≥ R₀, Dfun (fR R) < 0 := by
  obtain ⟨M1, hM1⟩ := DensityNeg.exists_abs_g1_le
  obtain ⟨M2, hM2⟩ := DensityNeg.exists_abs_g2_le
  obtain ⟨M3, hM3⟩ := DensityNeg.exists_abs_g3_le
  obtain ⟨M4, hM4⟩ := exists_abs_qper_le
  have hM1' : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2' : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  have hM3' : 0 ≤ M3 := (abs_nonneg _).trans (hM3 0)
  have hM4' : 0 ≤ M4 := (abs_nonneg _).trans (hM4 0)
  obtain ⟨a1, ha1_eq⟩ : ∃ a1 : ℝ, (∫ x in cell, DensityNeg.g1 x) / 20 ^ 41 = a1 := ⟨_, rfl⟩
  have ha1 : a1 < 0 := by
    rw [← ha1_eq]
    exact div_neg_of_neg_of_pos integral_cell_qper_mul_kernelK_neg (by positivity)
  obtain ⟨A, hA_eq⟩ : ∃ A : ℝ, 8 * 41 * M1 * 20 ^ 2 + 6 * M2 + 6 * M3 + 2 * 41 * M4 = A :=
    ⟨_, rfl⟩
  have hA : 0 ≤ A := by rw [← hA_eq]; linarith
  refine ⟨max 1 (A / -a1 + 1), lt_of_lt_of_le one_pos (le_max_left _ _), fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hRA : A / -a1 + 1 ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hR2 : 0 < R ^ 2 := by positivity
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hAR : A < R ^ 2 * -a1 := by
    have h1 : A ≤ (R - 1) * -a1 := (div_le_iff₀ (neg_pos.2 ha1)).1 (by linarith)
    have h2 : R * -a1 ≤ R ^ 2 * -a1 := mul_le_mul_of_nonneg_right hRR (neg_pos.2 ha1).le
    linarith
  refine Dfun_fR_neg_of_bounds hR1 hM1 hM2 hM3 hM4 ?_
  rw [ha1_eq, hA_eq]
  exact (div_lt_iff₀ hR2).2 (by linarith)

/-- **Some enveloped density has `D(f_R) < 0`.** -/
theorem exists_Dfun_fR_neg : ∃ R > 0, Dfun (fR R) < 0 := by
  obtain ⟨R₀, hR₀, h⟩ := exists_forall_ge_Dfun_fR_neg
  exact ⟨R₀, hR₀, h R₀ le_rfl⟩

end Fisher41
