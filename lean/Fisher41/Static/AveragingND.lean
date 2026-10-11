/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Defs
import Fisher41.Static.Averaging1D
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier-free Gaussian averaging of a periodic function in `d` dimensions

Let `g : E d → ℝ` be continuous, bounded by `M`, and `L`-periodic in each coordinate direction.
We show that the Gaussian average of `g` (variance `R²`) approximates its mean over a period cell
`[a, a + L]^d`:

`|∫ g · gaussian d (R²) - L^{-d} ∫_{[a, a + L]^d} g| ≤ 8 d M L² / R²`.

## Proof sketch

The Gaussian `gaussian d (R²)` factorizes as `∏ i, gauss1 R (x i)`, and the normalized indicator
of the cell factorizes as `∏ i, unif a L (x i)` with `unif a L = L⁻¹ 𝟙_{[a, a + L]}`. Transferring
to `Fin d → ℝ`, we argue by induction on the dimension, splitting off the first coordinate with
Fubini's theorem. In dimension `n + 1`, writing `x = (t, y)`:

* replacing `gauss1 R t dt` by `unif a L t dt` costs at most `8 M L² / R²` for every `y`, by the
  one-dimensional estimate `Fisher41.abs_integral_mul_gauss1_sub_average_le` applied to the slice
  `t ↦ g (t, y)`; since the remaining Gaussian factors form a probability density, the same bound
  holds after integration in `y`;
* the partial average `k y = L⁻¹ ∫₀ᴸ g (t, y) dt` is again continuous, bounded by `M` and
  periodic, so the induction hypothesis applies to it.

## Main results

* `Fisher41.AveragingND.gaussian_sq_eq_prod_gauss1`: `gaussian d (R ^ 2) x = ∏ i, gauss1 R (x i)`.
* `Fisher41.AveragingND.abs_integral_mul_prod_gauss1_sub_unif_le`: the estimate on `Fin n → ℝ`
  with the product densities.
* `Fisher41.abs_integral_mul_gaussian_sub_cell_le`: the averaging estimate on `E d`.
-/

open MeasureTheory Real

namespace Fisher41

namespace AveragingND

/-! ### The uniform density of a period interval -/

/-- The uniform density `L⁻¹ 𝟙_{[a, a + L]}` of the interval `[a, a + L]` (a probability density
when `0 < L`). -/
noncomputable def unif (a L t : ℝ) : ℝ := (Set.Icc a (a + L)).indicator (fun _ ↦ L⁻¹) t

/-- `unif a L` is integrable. -/
theorem integrable_unif (a L : ℝ) : Integrable (unif a L) := by
  have h : unif a L = (Set.Icc a (a + L)).indicator (fun _ ↦ L⁻¹) := rfl
  rw [h]
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- Integrating against `unif a L` is averaging over `[a, a + L]`. -/
theorem integral_mul_unif {L : ℝ} (hL : 0 < L) (a : ℝ) (φ : ℝ → ℝ) :
    ∫ t, φ t * unif a L t = (∫ t in a..a + L, φ t) / L := by
  have h : (fun t ↦ φ t * unif a L t) = (Set.Icc a (a + L)).indicator (fun t ↦ φ t * L⁻¹) := by
    funext t
    exact (Set.indicator_mul_right _ φ (fun _ ↦ L⁻¹)).symm
  rw [h, integral_indicator measurableSet_Icc, integral_mul_const, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show a ≤ a + L by linarith), div_eq_mul_inv]

/-- Integrating against the product density `∏ i, unif a L (y i)` is averaging over the cell
`[a, a + L]^n`. -/
theorem integral_mul_prod_unif {n : ℕ} {L : ℝ} (a : ℝ) (φ : (Fin n → ℝ) → ℝ) :
    ∫ y, φ y * ∏ i, unif a L (y i) =
      (∫ y in {y : Fin n → ℝ | ∀ i, y i ∈ Set.Icc a (a + L)}, φ y) / L ^ n := by
  have hS : MeasurableSet {y : Fin n → ℝ | ∀ i, y i ∈ Set.Icc a (a + L)} := by
    have hpi : {y : Fin n → ℝ | ∀ i, y i ∈ Set.Icc a (a + L)} =
        Set.univ.pi fun _ ↦ Set.Icc a (a + L) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    rw [hpi]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have h : (fun y ↦ φ y * ∏ i, unif a L (y i)) =
      {y : Fin n → ℝ | ∀ i, y i ∈ Set.Icc a (a + L)}.indicator (fun y ↦ φ y * (L ^ n)⁻¹) := by
    funext y
    by_cases hy : y ∈ {y : Fin n → ℝ | ∀ i, y i ∈ Set.Icc a (a + L)}
    · rw [Set.indicator_of_mem hy]
      have hy' : ∀ i, y i ∈ Set.Icc a (a + L) := hy
      have hprod : ∏ i, unif a L (y i) = ∏ _i : Fin n, L⁻¹ :=
        Finset.prod_congr rfl fun i _ ↦ Set.indicator_of_mem (hy' i) _
      rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
    · rw [Set.indicator_of_notMem hy]
      have hy' : ¬∀ i, y i ∈ Set.Icc a (a + L) := hy
      obtain ⟨i, hi⟩ := not_forall.mp hy'
      have h0 : ∏ j, unif a L (y j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      rw [h0, mul_zero]
  rw [h, integral_indicator hS, integral_mul_const, div_eq_mul_inv]

/-! ### Product Gaussian densities -/

/-- `gaussian d (R ^ 2)` is the product of the one-dimensional densities `gauss1 R`. -/
theorem gaussian_sq_eq_prod_gauss1 {d : ℕ} {R : ℝ} (hR : 0 < R) (x : E d) :
    gaussian d (R ^ 2) x = ∏ i, gauss1 R (x i) := by
  have hs : 0 < √(2 * π) * R := by positivity
  have h2 : 2 * π * R ^ 2 = (√(2 * π) * R) ^ (2 : ℝ) := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (by positivity)]
  simp only [gaussian, gauss1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  rw [EuclideanSpace.real_norm_sq_eq, h2, ← Real.rpow_mul hs.le,
    show (2 : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by ring, Real.rpow_neg hs.le, Real.rpow_natCast,
    inv_pow]
  congr 2
  simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

/-- The product Gaussian density is nonnegative. -/
theorem prod_gauss1_nonneg {n : ℕ} {R : ℝ} (hR : 0 < R) (y : Fin n → ℝ) :
    0 ≤ ∏ i, gauss1 R (y i) :=
  Finset.prod_nonneg fun _ _ ↦ gauss1_nonneg hR.le _

/-- The product Gaussian density is a probability density. -/
theorem integral_prod_gauss1 {n : ℕ} {R : ℝ} (hR : 0 < R) :
    ∫ y : Fin n → ℝ, ∏ i, gauss1 R (y i) = 1 := by
  rw [integral_fintype_prod_volume_eq_pow (ι := Fin n) (gauss1 R), integral_gauss1 hR, one_pow]

/-! ### Splitting off the first coordinate -/

/-- Shifting the first coordinate of `Fin.cons t y` by `L`. -/
theorem cons_add_smul_single_zero {n : ℕ} (t L : ℝ) (y : Fin n → ℝ) :
    (Fin.cons (t + L) y : Fin (n + 1) → ℝ) = Fin.cons t y + L • Pi.single 0 1 := by
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp

/-- Shifting a later coordinate of `Fin.cons t y` by `L`. -/
theorem cons_add_smul_single_succ {n : ℕ} (t L : ℝ) (y : Fin n → ℝ) (i : Fin n) :
    (Fin.cons t (y + L • Pi.single i 1) : Fin (n + 1) → ℝ) =
      Fin.cons t y + L • Pi.single i.succ 1 := by
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp
  · simp [Pi.single_apply]

/-- Fubini's theorem on `Fin (n + 1) → ℝ`, splitting off the first coordinate. -/
theorem integral_fin_succ_cons {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ} (hF : Integrable F) :
    Integrable (fun y : Fin n → ℝ ↦ ∫ t : ℝ, F (Fin.cons t y)) ∧
      ∫ x, F x = ∫ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have he : MeasurePreserving e.symm ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      volume :=
    MeasurePreserving.symm e (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0)
  have he' : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p ↦
    Fin.insertNth_zero' p.1 p.2
  have hF' : Integrable (fun p : ℝ × (Fin n → ℝ) ↦ F (Fin.cons p.1 p.2))
      ((volume : Measure ℝ).prod volume) := by
    have h := he.integrable_comp_of_integrable hF
    simp only [Function.comp_def, he'] at h
    exact h
  refine ⟨hF'.integral_prod_right, ?_⟩
  calc ∫ x, F x = ∫ p, F (e.symm p) ∂((volume : Measure ℝ).prod volume) :=
        (he.integral_comp' F).symm
    _ = ∫ p, F (Fin.cons p.1 p.2) ∂((volume : Measure ℝ).prod volume) := by
        simp only [he']
    _ = ∫ y : Fin n → ℝ, ∫ t : ℝ, F (Fin.cons t y) := integral_prod_symm _ hF'

/-- Splitting off the first coordinate in `∫ f x ∏ i, ρ (x i) dx`. -/
theorem integral_mul_prod_succ {n : ℕ} {ρ : ℝ → ℝ} (hρ : Integrable ρ)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    Integrable (fun y : Fin n → ℝ ↦ (∫ t, f (Fin.cons t y) * ρ t) * ∏ i, ρ (y i)) ∧
      ∫ x, f x * ∏ i, ρ (x i) =
        ∫ y : Fin n → ℝ, (∫ t, f (Fin.cons t y) * ρ t) * ∏ i, ρ (y i) := by
  have hF : Integrable (fun x : Fin (n + 1) → ℝ ↦ f x * ∏ i, ρ (x i)) :=
    (Integrable.fintype_prod (ι := Fin (n + 1)) (f := fun _ ↦ ρ) fun _ ↦ hρ).bdd_mul
      hf.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  have hslice : ∀ y : Fin n → ℝ,
      ∫ t, f (Fin.cons t y) * ∏ i, ρ ((Fin.cons t y : Fin (n + 1) → ℝ) i) =
        (∫ t, f (Fin.cons t y) * ρ t) * ∏ i, ρ (y i) := by
    intro y
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← mul_assoc]
    exact integral_mul_const _ _
  obtain ⟨h1, h2⟩ := integral_fin_succ_cons hF
  exact ⟨h1.congr (Filter.Eventually.of_forall hslice),
    h2.trans (integral_congr_ae (Filter.Eventually.of_forall hslice))⟩

/-! ### The estimate on `Fin n → ℝ` -/

/-- **Gaussian averaging on `Fin n → ℝ`.** For a continuous function `f` on `Fin n → ℝ` which is
`L`-periodic in each coordinate and bounded by `M`, integrating against the product Gaussian
density differs from averaging over the cell `[a, a + L]^n` by at most `8 n M L² / R²`. -/
theorem abs_integral_mul_prod_gauss1_sub_unif_le {L M R : ℝ} (a : ℝ) (hL : 0 < L) (hR : 0 < R) :
    ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), Continuous f →
      (∀ x i, f (x + L • Pi.single i 1) = f x) → (∀ x, |f x| ≤ M) →
      |(∫ x, f x * ∏ i, gauss1 R (x i)) - ∫ x, f x * ∏ i, unif a L (x i)| ≤
        8 * n * M * L ^ 2 / R ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro f _ _ _
    simp
  | succ n ih =>
    intro f hf hper hM
    -- the one-dimensional slices `t ↦ f (t, y)`
    have hcons_cont : ∀ y : Fin n → ℝ, Continuous fun t : ℝ ↦ f (Fin.cons t y) := fun y ↦
      hf.comp (Continuous.finCons (A := fun _ ↦ ℝ) continuous_id continuous_const)
    have hcons_per : ∀ y : Fin n → ℝ, Function.Periodic (fun t : ℝ ↦ f (Fin.cons t y)) L :=
      fun y t ↦ by simp only [cons_add_smul_single_zero, hper]
    -- the partial average `k y = L⁻¹ ∫₀ᴸ f (t, y) dt`
    obtain ⟨k, hk⟩ : ∃ k : (Fin n → ℝ) → ℝ,
        ∀ y, k y = (∫ t in (0 : ℝ)..L, f (Fin.cons t y)) / L := ⟨_, fun _ ↦ rfl⟩
    have hk_cont : Continuous k := by
      rw [show k = fun y ↦ (∫ t in (0 : ℝ)..L, f (Fin.cons t y)) / L from funext hk]
      have hc : Continuous (Function.uncurry fun (y : Fin n → ℝ) (t : ℝ) ↦ f (Fin.cons t y)) :=
        hf.comp (Continuous.finCons (A := fun _ ↦ ℝ) continuous_snd continuous_fst)
      exact
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 L).div_const L
    have hk_per : ∀ y i, k (y + L • Pi.single i 1) = k y := fun y i ↦ by
      simp only [hk, cons_add_smul_single_succ, hper]
    have hk_bdd : ∀ y, |k y| ≤ M := fun y ↦ by
      rw [hk]
      exact abs_intervalIntegral_div_le hL fun t ↦ hM _
    have hunif : ∀ y, ∫ t, f (Fin.cons t y) * unif a L t = k y := fun y ↦ by
      rw [integral_mul_unif hL, (hcons_per y).intervalIntegral_add_eq a 0, zero_add, hk]
    have hgk : ∀ y, |(∫ t, f (Fin.cons t y) * gauss1 R t) - k y| ≤ 8 * M * L ^ 2 / R ^ 2 :=
      fun y ↦ by
        rw [hk]
        exact abs_integral_mul_gauss1_sub_average_le hL hR (hcons_cont y) (hcons_per y)
          fun t ↦ hM _
    -- split off the first coordinate in both integrals
    obtain ⟨hintG, hG⟩ := integral_mul_prod_succ (integrable_gauss1 hR) hf hM
    have hU := (integral_mul_prod_succ (integrable_unif a L) hf hM).2
    simp only [hunif] at hU
    rw [hG, hU]
    -- first step: replace the first Gaussian factor by the uniform density
    have hGint : Integrable (fun y : Fin n → ℝ ↦ ∏ i, gauss1 R (y i)) :=
      Integrable.fintype_prod (ι := Fin n) (f := fun _ ↦ gauss1 R) fun _ ↦ integrable_gauss1 hR
    have hkG : Integrable (fun y ↦ k y * ∏ i, gauss1 R (y i)) :=
      hGint.bdd_mul hk_cont.aestronglyMeasurable (Filter.Eventually.of_forall hk_bdd)
    have hpt : ∀ y, ‖(∫ t, f (Fin.cons t y) * gauss1 R t) * ∏ i, gauss1 R (y i) -
        k y * ∏ i, gauss1 R (y i)‖ ≤ 8 * M * L ^ 2 / R ^ 2 * ∏ i, gauss1 R (y i) := fun y ↦ by
      rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (prod_gauss1_nonneg hR y)]
      exact mul_le_mul_of_nonneg_right (hgk y) (prod_gauss1_nonneg hR y)
    have hstep : |(∫ y, (∫ t, f (Fin.cons t y) * gauss1 R t) * ∏ i, gauss1 R (y i)) -
        ∫ y, k y * ∏ i, gauss1 R (y i)| ≤ 8 * M * L ^ 2 / R ^ 2 := by
      rw [← integral_sub hintG hkG, ← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le (hGint.const_mul _)
        (Filter.Eventually.of_forall hpt)).trans_eq ?_
      rw [integral_const_mul, integral_prod_gauss1 hR, mul_one]
    -- second step: the induction hypothesis for the partial average `k`
    calc _ ≤ |(∫ y, (∫ t, f (Fin.cons t y) * gauss1 R t) * ∏ i, gauss1 R (y i)) -
            ∫ y, k y * ∏ i, gauss1 R (y i)| +
          |(∫ y, k y * ∏ i, gauss1 R (y i)) - ∫ y, k y * ∏ i, unif a L (y i)| :=
          abs_sub_le _ _ _
      _ ≤ 8 * M * L ^ 2 / R ^ 2 + 8 * n * M * L ^ 2 / R ^ 2 :=
          add_le_add hstep (ih k hk_cont hk_per hk_bdd)
      _ = 8 * ↑(n + 1) * M * L ^ 2 / R ^ 2 := by push_cast; ring

end AveragingND

/-! ### The estimate on `E d` -/

/-- **Fourier-free Gaussian averaging in `d` dimensions.** For a continuous function `g` on `E d`
which is `L`-periodic in each coordinate direction and bounded by `M`, the Gaussian average
`∫ g · gaussian d (R²)` differs from the mean of `g` over any period cell `[a, a + L]^d` by at most
`8 d M L² / R²`. -/
theorem abs_integral_mul_gaussian_sub_cell_le {d : ℕ} {g : E d → ℝ} {L M R a : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hg : Continuous g)
    (hper : ∀ (x : E d) (i : Fin d), g (x + L • EuclideanSpace.single i 1) = g x)
    (hM : ∀ x, |g x| ≤ M) :
    |(∫ x, g x * gaussian d (R ^ 2) x) -
        (∫ x in {x : E d | ∀ i, x i ∈ Set.Icc a (a + L)}, g x) / L ^ d|
      ≤ 8 * d * M * L ^ 2 / R ^ 2 := by
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  have hemb := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
  have h1 : ∫ x, g x * gaussian d (R ^ 2) x =
      ∫ y : Fin d → ℝ, g (WithLp.toLp 2 y) * ∏ i, gauss1 R (y i) := by
    rw [← hmp.integral_comp hemb]
    simp only [AveragingND.gaussian_sq_eq_prod_gauss1 hR]
  have hset : ∫ x in {x : E d | ∀ i, x i ∈ Set.Icc a (a + L)}, g x =
      ∫ y in {y : Fin d → ℝ | ∀ i, y i ∈ Set.Icc a (a + L)}, g (WithLp.toLp 2 y) :=
    (hmp.setIntegral_preimage_emb hemb g _).symm
  rw [h1, hset, ← AveragingND.integral_mul_prod_unif]
  exact AveragingND.abs_integral_mul_prod_gauss1_sub_unif_le a hL hR d
    (fun y ↦ g (WithLp.toLp 2 y)) (hg.comp (PiLp.continuous_toLp 2 _))
    (fun y i ↦ hper (WithLp.toLp 2 y) i) (fun y ↦ hM _)

end Fisher41
