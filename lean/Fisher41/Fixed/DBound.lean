/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Static.DensityNeg
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The fixed density has `D(f) < -10⁻⁴⁴`

For the density of the manuscript, `f = q γ_{R²} / Z` with `R = 10⁴⁰` (`Fisher41.fPDF`), we
prove the explicit bound `D(f) < -10⁻⁴⁴` (`Fisher41.Dfun_fPDF_lt`); in fact `D(f) < -10⁻⁴³`.

## Proof

1. *Profile bounds.* `ũ ≤ u ≤ 23` everywhere, and on `0 ≤ s ≤ 32`:
   `|ũ'| ≤ 100`, `|ũ''| ≤ 2000`, `|ũ'''| ≤ 10⁵` (for `s ≤ 16` from `0 < σ < 1` and
   `|V'| ≤ 34`; for `16 ≤ s ≤ 32` from the tail bounds of `Fisher41.Static.Profile`).
2. *The periodic functions.* By lattice invariance it suffices to work on the box
   `(-11, 11)⁴¹`, where `q = e^w`, `Hᵢⱼ = -(ũ''(s) xᵢ xⱼ + ũ'(s) δᵢⱼ)` and
   `K_q = K₄₁(s, -ũ', ũ'', ũ''')` with `s = |x|²/2`; the derivatives of `ũ` vanish unless
   `|x| < 8`. Hence `q ≤ 10¹¹`, `|Hᵢⱼ| ≤ 128100`, `|K_q| ≤ 10¹⁶`, and
   `|g₁| ≤ 10²⁷`, `|g₂| ≤ 10²⁵`, `|g₃| ≤ 10¹⁸`.
3. *Volume of balls.* `|B₁| = 2²¹ π²⁰ / 41‼` in `ℝ⁴¹`, so `41 |B₁| ≥ 10⁻⁸` (`π > 3`) and
   `|B₈| ≤ 2·10³⁰` (`π ≤ 4`).
4. *The normalizer.* On the period cell `q - 1 ≤ 10¹¹ · 1_{B₈}`, so Gaussian averaging of
   `q - 1` gives `Z = ∫ q γ_{R²} < 2`.
5. *Assembly.* `Fisher41.mul_Dfun_fR_le` and `Fisher41.integral_cell_qper_mul_kernelK_le` give
   `Z D(f) < -2·10⁻⁴³`; with `1 ≤ Z < 2` this yields `D(f) < -10⁻⁴³`.

Auxiliary lemmas live in the namespace `Fisher41.DBound`.
-/

open MeasureTheory Real
open scoped Nat

noncomputable section

namespace Fisher41

namespace DBound

/-! ### Bounds on the radial profile -/

/-- `V(s) = 16 - (s + 1)² ≤ 16`. -/
theorem Vfun_le (s : ℝ) : Vfun s ≤ 16 := by
  unfold Vfun
  nlinarith [sq_nonneg (s + 1)]

/-- `u = (4/3) log (1 + e^V) ≤ 23`, since `1 + e^V ≤ e¹⁷`. -/
theorem uprof_le (s : ℝ) : uprof s ≤ 23 := by
  have e1 : Real.exp (Vfun s) ≤ Real.exp 16 := Real.exp_le_exp.2 (Vfun_le s)
  have e2 : (1 : ℝ) ≤ Real.exp 16 := Real.one_le_exp (by norm_num)
  have e3 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 : 1 + Real.exp (Vfun s) ≤ Real.exp 17 :=
    calc 1 + Real.exp (Vfun s) ≤ 2 * Real.exp 16 := by linarith
      _ ≤ Real.exp 1 * Real.exp 16 := mul_le_mul_of_nonneg_right e3 (Real.exp_pos 16).le
      _ = Real.exp 17 := by rw [← Real.exp_add]; norm_num
  have h2 : Real.log (1 + Real.exp (Vfun s)) ≤ 17 :=
    (Real.log_le_iff_le_exp (by positivity)).2 h1
  rw [uprof]
  linarith

/-- `ũ ≤ u ≤ 23`. -/
theorem ucut_le (s : ℝ) : ucut s ≤ 23 :=
  (mul_le_of_le_one_left (Periodic.uprof_nonneg s) (eta_le_one _)).trans (uprof_le s)

/-- `U ≤ 23`: at every point `U` is `0` or a single bump value. -/
theorem Uper_le (x : E 41) : Uper x ≤ 23 := by
  rcases Periodic.Uper_eq_zero_or_bump x with h | ⟨z, h⟩
  · rw [h]
    norm_num
  · rw [h]
    exact ucut_le _

/-- `q = e^U ≤ e²³ ≤ 3²³ ≤ 10¹¹`. -/
theorem qper_le (x : E 41) : qper x ≤ 10 ^ 11 := by
  have h1 : qper x ≤ Real.exp 23 := Real.exp_le_exp.2 (Uper_le x)
  have h2 : Real.exp 23 = Real.exp 1 ^ 23 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have h4 : Real.exp 1 ^ 23 ≤ 3 ^ 23 := pow_le_pow_left₀ (Real.exp_pos 1).le h3 23
  have h5 : (3 : ℝ) ^ 23 ≤ 10 ^ 11 := by norm_num
  linarith

/-- `|q| ≤ 10¹¹`. -/
theorem abs_qper_le (x : E 41) : |qper x| ≤ 10 ^ 11 := by
  rw [abs_of_pos (qper_pos x)]
  exact qper_le x

/-- For `16 ≤ s ≤ 32` the tail factor `10⁶ s³ e^{V(s)}` of `Fisher41.Static.Profile` is at
most `1`. -/
theorem tail_le_one {s : ℝ} (hs : 16 ≤ s) (hs' : s ≤ 32) :
    10 ^ 6 * s ^ 3 * Real.exp (Vfun s) ≤ 1 := by
  have h1 := Profile.exp_Vfun_le hs
  have h2 : s ^ 3 ≤ 32 ^ 3 := pow_le_pow_left₀ (by linarith) hs' 3
  have h3 : 10 ^ 6 * s ^ 3 * Real.exp (Vfun s) ≤ 10 ^ 6 * 32 ^ 3 * (2 ^ 200)⁻¹ :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1 (Real.exp_pos _).le
      (by norm_num)
  exact h3.trans (by norm_num)

/-- Bounds on the derivatives of the cut-off profile on `[0, 32]`:
`|ũ'| ≤ 100`, `|ũ''| ≤ 2000` and `|ũ'''| ≤ 10⁵`. -/
theorem abs_uc_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 32) :
    |uc1 s| ≤ 100 ∧ |uc2 s| ≤ 2000 ∧ |uc3 s| ≤ 10 ^ 5 := by
  rcases le_total s 16 with h16 | h16
  · rw [uc1_eq_u1 h16, uc2_eq_u2 h16, uc3_eq_u3 h16]
    have hσ0 := Num.sigma_pos (Vfun s)
    have hσ1 := Num.sigma_lt_one (Vfun s)
    have hσ : |Num.sigma (Vfun s)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have h1σ := Profile.abs_one_sub_sigma_le (Vfun s)
    have h2σ := Profile.abs_one_sub_two_sigma_le (Vfun s)
    have hW : |-2 - 2 * s| ≤ 34 := abs_le.2 ⟨by linarith, by linarith⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (Profile.bnd_mul (Profile.bnd_const (by norm_num : (0 : ℝ) ≤ 4 / 3))
        (Profile.bnd_mul hσ hW)).trans (by norm_num)
    · exact (Profile.bnd_mul (Profile.bnd_const (by norm_num : (0 : ℝ) ≤ 4 / 3))
        (Profile.bnd_add
          (Profile.bnd_mul (Profile.bnd_neg_const (by norm_num : (0 : ℝ) ≤ 2)) hσ)
          (Profile.bnd_mul (Profile.bnd_mul hσ h1σ) (Profile.bnd_pow hW 2)))).trans
        (by norm_num)
    · exact (Profile.bnd_mul (Profile.bnd_const (by norm_num : (0 : ℝ) ≤ 4 / 3))
        (Profile.bnd_add
          (Profile.bnd_mul (Profile.bnd_mul (Profile.bnd_mul
            (Profile.bnd_neg_const (by norm_num : (0 : ℝ) ≤ 6)) hσ) h1σ) hW)
          (Profile.bnd_mul (Profile.bnd_mul (Profile.bnd_mul hσ h1σ) h2σ)
            (Profile.bnd_pow hW 3)))).trans (by norm_num)
  · have ht := tail_le_one h16 hs
    exact ⟨(Profile.abs_uc1_le h16).trans (by linarith),
      (Profile.abs_uc2_le h16).trans (by linarith), (Profile.abs_uc3_le h16).trans (by linarith)⟩

/-- `|K₄₁(s, a, B, C)| ≤ 10¹⁶` for `0 ≤ s ≤ 32`, `|a| ≤ 100`, `|B| ≤ 2000`, `|C| ≤ 10⁵`. -/
theorem abs_Kd_le_of_bounds {s a B C : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 32) (ha : |a| ≤ 100)
    (hB : |B| ≤ 2000) (hC : |C| ≤ 10 ^ 5) : |Kd 41 s a B C| ≤ 10 ^ 16 := by
  have hsa : |s| ≤ 32 := by
    rw [abs_of_nonneg hs0]
    exact hs
  have h41a : |((41 : ℕ) : ℝ) + 2| ≤ 43 := by
    rw [abs_of_nonneg (by positivity)]
    norm_num
  have h41b : |((41 : ℕ) : ℝ) - 1| ≤ 40 := by
    rw [abs_of_nonneg (by norm_num)]
    norm_num
  have hK := Profile.bnd_add (Profile.bnd_add (Profile.bnd_add
    (Profile.bnd_mul (Profile.bnd_mul (Profile.bnd_const (by norm_num : (0 : ℝ) ≤ 8))
      (Profile.bnd_pow hsa 3)) (Profile.bnd_pow hC 2))
    (Profile.bnd_mul (Profile.bnd_mul (Profile.bnd_mul
      (Profile.bnd_const (by norm_num : (0 : ℝ) ≤ 24)) (Profile.bnd_pow hsa 2)) hB) hC))
    (Profile.bnd_mul (Profile.bnd_mul (Profile.bnd_mul
      (Profile.bnd_const (by norm_num : (0 : ℝ) ≤ 6)) h41a) hsa) (Profile.bnd_pow hB 2)))
    (Profile.bnd_mul (Profile.bnd_const (by norm_num : (0 : ℝ) ≤ 2))
      (Profile.bnd_add (Profile.bnd_mul h41b (Profile.bnd_pow ha 3))
        (Profile.bnd_pow (Profile.bnd_sub ha (Profile.bnd_mul (Profile.bnd_mul
          (Profile.bnd_const (by norm_num : (0 : ℝ) ≤ 2)) hsa) hB)) 3)))
  exact hK.trans (by norm_num)

/-! ### The periodic functions on the box `(-11, 11)⁴¹` -/

/-- On the box, `Hᵢⱼ = -(ũ''(s) xᵢ xⱼ + ũ'(s) δᵢⱼ)` with `s = |x|²/2`. -/
theorem negHess_qper_eq {y : E 41} (hy : ∀ i, |y i| < 11) (i j : Fin 41) :
    negHess qper i j y = -(uc2 (‖y‖ ^ 2 / 2) * y i * y j +
      uc1 (‖y‖ ^ 2 / 2) * (if i = j then 1 else 0)) := by
  have h0 : Set.EqOn (fun w => Real.log (qper w)) (fun w : E 41 => ucut (‖w‖ ^ 2 / 2))
      Periodic.box := fun w hw => by
    show Real.log (qper w) = ucut (‖w‖ ^ 2 / 2)
    rw [qper, Real.log_exp, Uper_eq_bump (show ∀ i, |w i| < 11 from hw)]
    rfl
  have h2 := Periodic.pd_eqOn Periodic.isOpen_box (Periodic.pd_eqOn Periodic.isOpen_box h0 i) j
    (show y ∈ Periodic.box from hy)
  show -pd (pd (fun w => Real.log (qper w)) i) j y = _
  rw [h2, pd_pd_radial hasDerivAt_ucut hasDerivAt_uc1]

/-- On the box, `K_q = K₄₁(s, -ũ'(s), ũ''(s), ũ'''(s))` with `s = |x|²/2`. -/
theorem kernelK_qper_eq_Kd {y : E 41} (hy : ∀ i, |y i| < 11) :
    kernelK qper y = Kd 41 (‖y‖ ^ 2 / 2) (-uc1 (‖y‖ ^ 2 / 2)) (uc2 (‖y‖ ^ 2 / 2))
      (uc3 (‖y‖ ^ 2 / 2)) := by
  rw [kernelK_qper_eq hy]
  exact Periodic.kernelK_exp_bump hasDerivAt_ucut hasDerivAt_uc1 hasDerivAt_uc2 y

/-- On the box, `|Hᵢⱼ| ≤ 2000 · 8 · 8 + 100 = 128100`. -/
theorem abs_negHess_qper_le_of_box {y : E 41} (hy : ∀ i, |y i| < 11) (i j : Fin 41) :
    |negHess qper i j y| ≤ 128100 := by
  rw [negHess_qper_eq hy, abs_neg]
  rcases le_total (‖y‖ ^ 2 / 2) 32 with hs | hs
  · have hn : ‖y‖ ≤ 8 := by nlinarith [norm_nonneg y]
    have hyi : |y i| ≤ 8 := (Periodic.abs_apply_le_norm y i).trans hn
    have hyj : |y j| ≤ 8 := (Periodic.abs_apply_le_norm y j).trans hn
    obtain ⟨h1, h2, -⟩ := abs_uc_le (by positivity) hs
    have hδ : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    exact (Profile.bnd_add (Profile.bnd_mul (Profile.bnd_mul h2 hyi) hyj)
      (Profile.bnd_mul h1 hδ)).trans (by norm_num)
  · rw [uc1_eq_zero hs, uc2_eq_zero hs]
    norm_num

/-- On the box, `|K_q| ≤ 10¹⁶`. -/
theorem abs_kernelK_qper_le_of_box {y : E 41} (hy : ∀ i, |y i| < 11) :
    |kernelK qper y| ≤ 10 ^ 16 := by
  rw [kernelK_qper_eq_Kd hy]
  rcases le_total (‖y‖ ^ 2 / 2) 32 with hs | hs
  · obtain ⟨h1, h2, h3⟩ := abs_uc_le (by positivity) hs
    exact abs_Kd_le_of_bounds (by positivity) hs (by rwa [abs_neg]) h2 h3
  · rw [uc1_eq_zero hs, uc2_eq_zero hs, uc3_eq_zero hs]
    norm_num [Kd]

/-! ### Bounds on all of `ℝ⁴¹` by lattice invariance -/

/-- Every point has a lattice translate in the box `(-11, 11)⁴¹`. -/
theorem exists_sub_latt_mem_box (x : E 41) :
    ∃ z : Fin 41 → ℤ, ∀ i, |(x - latt z) i| < 11 := by
  obtain ⟨z, hz⟩ := DensityNeg.exists_sub_latt_mem_cell x
  have hz' : ∀ i, (x - latt z) i ∈ Set.Icc (-10 : ℝ) 10 := hz
  exact ⟨z, fun i => abs_lt.2 ⟨by linarith [(hz' i).1], by linarith [(hz' i).2]⟩⟩

/-- `|Hᵢⱼ| ≤ 128100` everywhere, where `H = -∇² log q`. -/
theorem abs_negHess_qper_le (x : E 41) (i j : Fin 41) : |negHess qper i j x| ≤ 128100 := by
  obtain ⟨z, hz⟩ := exists_sub_latt_mem_box x
  have h := DensityNeg.negHess_add_of_forall_add (ρ := qper) (a := latt z)
    (fun y => qper_add_latt y z) i j (x - latt z)
  rw [sub_add_cancel] at h
  rw [h]
  exact abs_negHess_qper_le_of_box hz i j

/-- `|K_q| ≤ 10¹⁶` everywhere. -/
theorem abs_kernelK_qper_le (x : E 41) : |kernelK qper x| ≤ 10 ^ 16 := by
  obtain ⟨z, hz⟩ := exists_sub_latt_mem_box x
  have h := DensityNeg.kernelK_add_of_forall_add (ρ := qper) (a := latt z)
    (fun y => qper_add_latt y z) (x - latt z)
  rw [sub_add_cancel] at h
  rw [h]
  exact abs_kernelK_qper_le_of_box hz

/-- `|g₁| = |q K_q| ≤ 10¹¹ · 10¹⁶ = 10²⁷`. -/
theorem abs_g1_le (x : E 41) : |DensityNeg.g1 x| ≤ 10 ^ 27 := by
  show |qper x * kernelK qper x| ≤ 10 ^ 27
  rw [abs_mul]
  calc |qper x| * |kernelK qper x| ≤ 10 ^ 11 * 10 ^ 16 :=
        mul_le_mul (abs_qper_le x) (abs_kernelK_qper_le x) (abs_nonneg _) (by norm_num)
    _ = 10 ^ 27 := by norm_num

/-- `|g₂| = |q ∑ᵢⱼ Hᵢⱼ²| ≤ 10²⁵`. -/
theorem abs_g2_le (x : E 41) : |DensityNeg.g2 x| ≤ 10 ^ 25 := by
  have h0 : 0 ≤ ∑ i, ∑ j, (negHess qper i j x) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsum : ∑ i, ∑ j, (negHess qper i j x) ^ 2 ≤ 41 * (41 * 128100 ^ 2) :=
    calc ∑ i, ∑ j, (negHess qper i j x) ^ 2
        ≤ ∑ _i : Fin 41, ∑ _j : Fin 41, (128100 : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            sq_le_sq' (abs_le.1 (abs_negHess_qper_le x i j)).1
              (abs_le.1 (abs_negHess_qper_le x i j)).2
      _ = 41 * (41 * 128100 ^ 2) := by norm_num
  show |qper x * ∑ i, ∑ j, (negHess qper i j x) ^ 2| ≤ 10 ^ 25
  rw [abs_mul, abs_of_nonneg h0]
  calc |qper x| * ∑ i, ∑ j, (negHess qper i j x) ^ 2 ≤ 10 ^ 11 * (41 * (41 * 128100 ^ 2)) :=
        mul_le_mul (abs_qper_le x) hsum h0 (by norm_num)
    _ ≤ 10 ^ 25 := by norm_num

/-- `|g₃| = |q ∑ᵢ Hᵢᵢ| ≤ 10¹⁸`. -/
theorem abs_g3_le (x : E 41) : |DensityNeg.g3 x| ≤ 10 ^ 18 := by
  have hsum : |∑ i, negHess qper i i x| ≤ 41 * 128100 :=
    calc |∑ i, negHess qper i i x| ≤ ∑ i, |negHess qper i i x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 41, (128100 : ℝ) :=
          Finset.sum_le_sum fun i _ => abs_negHess_qper_le x i i
      _ = 41 * 128100 := by norm_num
  show |qper x * ∑ i, negHess qper i i x| ≤ 10 ^ 18
  rw [abs_mul]
  calc |qper x| * |∑ i, negHess qper i i x| ≤ 10 ^ 11 * (41 * 128100) :=
        mul_le_mul (abs_qper_le x) hsum (abs_nonneg _) (by norm_num)
    _ ≤ 10 ^ 18 := by norm_num

/-! ### Volumes of balls in `ℝ⁴¹` -/

/-- `41‼ = 13113070457687988603440625`. -/
theorem doubleFactorial_forty_one : (41 : ℕ)‼ = 13113070457687988603440625 := by
  decide

/-- `|B_r| = r⁴¹ · 2²¹ π²⁰ / 41‼` in `ℝ⁴¹`. -/
theorem volume_ball_toReal {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : E 41) r)).toReal =
      r ^ 41 * (π ^ 20 * 2 ^ 21 / 13113070457687988603440625) := by
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 20) (by simp) (0 : E 41) r,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity), doubleFactorial_forty_one]
  norm_num

/-- `ω = 41 |B₁| ≥ 10⁻⁸` (using `π > 3`). -/
theorem one_div_le_omega :
    (1 : ℝ) / 10 ^ 8 ≤ 41 * (volume (Metric.ball (0 : E 41) 1)).toReal := by
  rw [volume_ball_toReal zero_le_one]
  have hπ : (3 : ℝ) ^ 20 ≤ π ^ 20 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 20
  have h : (3 : ℝ) ^ 20 * 2 ^ 21 / 13113070457687988603440625 ≤
      π ^ 20 * 2 ^ 21 / 13113070457687988603440625 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hπ (by norm_num)) (by norm_num)
  calc (1 : ℝ) / 10 ^ 8
      ≤ 41 * (1 ^ 41 * ((3 : ℝ) ^ 20 * 2 ^ 21 / 13113070457687988603440625)) := by norm_num
    _ ≤ 41 * (1 ^ 41 * (π ^ 20 * 2 ^ 21 / 13113070457687988603440625)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by norm_num)) (by norm_num)

/-- `|B₈| ≤ 2·10³⁰` in `ℝ⁴¹` (using `π ≤ 4`). -/
theorem volume_ball_eight_le : (volume (Metric.ball (0 : E 41) 8)).toReal ≤ 2 * 10 ^ 30 := by
  rw [volume_ball_toReal (by norm_num : (0 : ℝ) ≤ 8)]
  have hπ : π ^ 20 ≤ (4 : ℝ) ^ 20 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four 20
  have h : π ^ 20 * 2 ^ 21 / 13113070457687988603440625 ≤
      (4 : ℝ) ^ 20 * 2 ^ 21 / 13113070457687988603440625 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hπ (by norm_num)) (by norm_num)
  calc (8 : ℝ) ^ 41 * (π ^ 20 * 2 ^ 21 / 13113070457687988603440625)
      ≤ 8 ^ 41 * ((4 : ℝ) ^ 20 * 2 ^ 21 / 13113070457687988603440625) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 2 * 10 ^ 30 := by norm_num

/-! ### The normalizer -/

/-- On the period cell `q - 1 ≤ 10¹¹ · 1_{B₈}`, hence `∫_{cell} (q - 1) ≤ 10¹¹ |B₈|`. -/
theorem integral_cell_qper_sub_one_le :
    ∫ x in cell, (qper x - 1) ≤ 10 ^ 11 * (volume (Metric.ball (0 : E 41) 8)).toReal := by
  have hc : Continuous fun x => qper x - 1 := contDiff_qper.continuous.sub continuous_const
  have hpt : ∀ x ∈ cell,
      qper x - 1 ≤ (Metric.ball (0 : E 41) 8).indicator (fun _ => (10 : ℝ) ^ 11) x := by
    intro x hx
    have hx' : ∀ i, x i ∈ Set.Icc (-10 : ℝ) 10 := hx
    have hbox : ∀ i, |x i| < 11 := fun i =>
      abs_lt.2 ⟨by linarith [(hx' i).1], by linarith [(hx' i).2]⟩
    by_cases hxB : x ∈ Metric.ball (0 : E 41) 8
    · simp only [Set.indicator_of_mem hxB]
      linarith [qper_le x]
    · simp only [Set.indicator_of_notMem hxB]
      have hn : 8 ≤ ‖x‖ := not_lt.1 fun h => hxB (mem_ball_zero_iff.2 h)
      have h1 : qper x = 1 := by
        rw [qper, Uper_eq_bump hbox, bump_eq_zero hn, Real.exp_zero]
      linarith
  have hi1 : IntegrableOn (fun x => qper x - 1) cell :=
    hc.continuousOn.integrableOn_compact DensityNeg.isCompact_cell
  have hconst : IntegrableOn (fun _ : E 41 => (10 : ℝ) ^ 11) cell :=
    continuous_const.continuousOn.integrableOn_compact DensityNeg.isCompact_cell
  have hi2 : IntegrableOn ((Metric.ball (0 : E 41) 8).indicator fun _ => (10 : ℝ) ^ 11) cell :=
    hconst.indicator measurableSet_ball
  calc ∫ x in cell, (qper x - 1)
      ≤ ∫ x in cell, (Metric.ball (0 : E 41) 8).indicator (fun _ => (10 : ℝ) ^ 11) x :=
        setIntegral_mono_on hi1 hi2 measurableSet_cell hpt
    _ = ∫ _ in cell ∩ Metric.ball (0 : E 41) 8, (10 : ℝ) ^ 11 :=
        setIntegral_indicator measurableSet_ball
    _ = (volume (cell ∩ Metric.ball (0 : E 41) 8)).toReal * 10 ^ 11 := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def]
    _ ≤ (volume (Metric.ball (0 : E 41) 8)).toReal * 10 ^ 11 :=
        mul_le_mul_of_nonneg_right
          (ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono Set.inter_subset_right))
          (by norm_num)
    _ = 10 ^ 11 * (volume (Metric.ball (0 : E 41) 8)).toReal := mul_comm _ _

/-- **The normalizer** `Z = ∫ q γ_{R²}` for `R = 10⁴⁰` satisfies `Z < 2`. -/
theorem integral_qper_mul_gaussian_lt_two : ∫ x, qper x * gaussian 41 (Rstd ^ 2) x < 2 := by
  have hR0 : (0 : ℝ) < Rstd := by norm_num [Rstd]
  have hR2 : Rstd ^ 2 = 10 ^ 80 := by norm_num [Rstd]
  have hR2pos : (0 : ℝ) < Rstd ^ 2 := by positivity
  have hc : Continuous fun x => qper x - 1 := contDiff_qper.continuous.sub continuous_const
  have hM : ∀ x, |qper x - 1| ≤ 10 ^ 11 := fun x => by
    have h1 := one_le_qper x
    have h2 := qper_le x
    rw [abs_le]
    constructor <;> linarith
  have havg : |(∫ x, (qper x - 1) * gaussian 41 (Rstd ^ 2) x) -
      (∫ x in cell, (qper x - 1)) / 20 ^ 41| ≤ 8 * 41 * 10 ^ 11 * 20 ^ 2 / Rstd ^ 2 :=
    abs_integral_mul_gaussian_sub_cell_le_of_add_latt hR0 hc
      (fun x z => by simp only [qper_add_latt]) hM
  have hsplit : ∫ x, (qper x - 1) * gaussian 41 (Rstd ^ 2) x =
      (∫ x, qper x * gaussian 41 (Rstd ^ 2) x) - 1 := by
    have hi1 : Integrable fun x => qper x * gaussian 41 (Rstd ^ 2) x :=
      DensityNeg.integrable_mul_gaussian hR0 contDiff_qper.continuous abs_qper_le
    have hi2 : Integrable fun x => gaussian 41 (Rstd ^ 2) x := integrable_gaussian hR2pos
    calc ∫ x, (qper x - 1) * gaussian 41 (Rstd ^ 2) x
        = ∫ x, (qper x * gaussian 41 (Rstd ^ 2) x - gaussian 41 (Rstd ^ 2) x) := by
          congr 1
          funext x
          ring
      _ = (∫ x, qper x * gaussian 41 (Rstd ^ 2) x) - 1 := by
          rw [integral_sub hi1 hi2, integral_gaussian_eq_one hR2pos]
  have hA : (∫ x in cell, (qper x - 1)) / 20 ^ 41 ≤ 10 ^ 11 * (2 * 10 ^ 30) / 20 ^ 41 :=
    div_le_div_of_nonneg_right (integral_cell_qper_sub_one_le.trans
      (mul_le_mul_of_nonneg_left volume_ball_eight_le (by norm_num))) (by norm_num)
  have h1 : ∫ x, (qper x - 1) * gaussian 41 (Rstd ^ 2) x ≤
      (∫ x in cell, (qper x - 1)) / 20 ^ 41 + 8 * 41 * 10 ^ 11 * 20 ^ 2 / Rstd ^ 2 :=
    sub_le_iff_le_add'.1 (abs_le.1 havg).2
  calc ∫ x, qper x * gaussian 41 (Rstd ^ 2) x
      = (∫ x, (qper x - 1) * gaussian 41 (Rstd ^ 2) x) + 1 := by
        rw [hsplit]
        ring
    _ ≤ ((∫ x in cell, (qper x - 1)) / 20 ^ 41 + 8 * 41 * 10 ^ 11 * 20 ^ 2 / Rstd ^ 2) + 1 :=
        add_le_add h1 le_rfl
    _ ≤ (10 ^ 11 * (2 * 10 ^ 30) / 20 ^ 41 + 8 * 41 * 10 ^ 11 * 20 ^ 2 / 10 ^ 80) + 1 := by
        rw [hR2]
        exact add_le_add (add_le_add hA le_rfl) le_rfl
    _ < 2 := by norm_num

end DBound

/-! ### The main estimate -/

/-- **The density of the manuscript has `D(f) < -10⁻⁴⁴`.** For `f = q γ_{R²} / Z` with
`R = 10⁴⁰` (`Fisher41.fPDF`), `Z D(f) ≤ 20⁻⁴¹ ∫_{cell} q K_q + O(R⁻²) < -2·10⁻⁴³` and
`1 ≤ Z < 2`, so in fact `D(f) < -10⁻⁴³`. -/
theorem Dfun_fPDF_lt : Dfun fPDF < -(10 : ℝ) ^ (-44 : ℤ) := by
  have hR1 : (1 : ℝ) ≤ Rstd := by norm_num [Rstd]
  have hR0 : (0 : ℝ) < Rstd := by norm_num [Rstd]
  have hR2 : Rstd ^ 2 = 10 ^ 80 := by norm_num [Rstd]
  have hle : (∫ x, qper x * gaussian 41 (Rstd ^ 2) x) * Dfun (fR Rstd) ≤
      (∫ x in cell, DensityNeg.g1 x) / 20 ^ 41 +
        (8 * 41 * 10 ^ 27 * 20 ^ 2 + 6 * 10 ^ 25 + 6 * 10 ^ 18 + 2 * 41 * 10 ^ 11) / Rstd ^ 2 :=
    mul_Dfun_fR_le hR1 DBound.abs_g1_le DBound.abs_g2_le DBound.abs_g3_le DBound.abs_qper_le
  have hI : (∫ x in cell, DensityNeg.g1 x) ≤ 1 / 10 ^ 8 * (-5000000000000000000 + 16) :=
    integral_cell_qper_mul_kernelK_le.trans
      (mul_le_mul_of_nonpos_right DBound.one_div_le_omega (by norm_num))
  have hZ1 := one_le_integral_qper_mul_gaussian hR0
  have hZ2 := DBound.integral_qper_mul_gaussian_lt_two
  have hZD : (∫ x, qper x * gaussian 41 (Rstd ^ 2) x) * Dfun (fR Rstd) < -2 / 10 ^ 43 := by
    refine hle.trans_lt ?_
    rw [hR2]
    calc _ ≤ 1 / 10 ^ 8 * (-5000000000000000000 + 16) / 20 ^ 41 +
          (8 * 41 * 10 ^ 27 * 20 ^ 2 + 6 * 10 ^ 25 + 6 * 10 ^ 18 + 2 * 41 * 10 ^ 11) / 10 ^ 80 :=
          add_le_add (div_le_div_of_nonneg_right hI (by norm_num)) le_rfl
      _ < -2 / 10 ^ 43 := by norm_num
  have h5 : (∫ x, qper x * gaussian 41 (Rstd ^ 2) x) * Dfun (fR Rstd) <
      (∫ x, qper x * gaussian 41 (Rstd ^ 2) x) * (-1 / 10 ^ 43) :=
    calc (∫ x, qper x * gaussian 41 (Rstd ^ 2) x) * Dfun (fR Rstd) < -2 / 10 ^ 43 := hZD
      _ = 2 * (-1 / 10 ^ 43) := by ring
      _ < (∫ x, qper x * gaussian 41 (Rstd ^ 2) x) * (-1 / 10 ^ 43) :=
        mul_lt_mul_of_neg_right hZ2 (by norm_num)
  have hD : Dfun (fR Rstd) < -1 / 10 ^ 43 := lt_of_mul_lt_mul_left h5 (by linarith)
  exact hD.trans (by norm_num)

end Fisher41
