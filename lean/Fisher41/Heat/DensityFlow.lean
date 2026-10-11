/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Heat.Commute
import Fisher41.Heat.Domination
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The heat flow of a Gaussian-dominated smooth density

We study the heat flow `ρ s = heat f s` of a density `f = c q γ_T`, where `γ_T = gaussian d T` is
the centred Gaussian of variance `T > 0`, `c > 0`, and the prefactor `q` is smooth with
`1 ≤ q ≤ Q` and with bounded derivatives of order at most `4`. These standing hypotheses are
bundled in `Fisher41.DensityFlowHyp d T c Q q f` (the density is an arbitrary `f` together with
the identity `f x = c * q x * gaussian d T x`).

## Main definitions

* `Fisher41.pdList g l`: the iterated coordinate partial derivative, `pdList g [] = g` and
  `pdList g (i :: l) = pdList (pd g i) l`, so that `pdList g [i, j] = pd (pd g i) j`.
* `Fisher41.DensityFlowHyp d T c Q q f`: the standing hypotheses, with the derivative bounds on
  `q` phrased with `pdList`; `Fisher41.DensityFlowHyp.of_iteratedFDeriv` builds them from bounds
  on `iteratedFDeriv ℝ k q`, `k ≤ 4`.

## Main results

For `H : DensityFlowHyp d T c Q q f`:

* `H.contDiff`, `H.pos`, `H.mul_gaussian_le`, `H.le_mul_gaussian`, `H.integrable`: `f` is
  smooth, positive, `c γ_T ≤ f ≤ c Q γ_T`, and integrable.
* `H.contDiff_pdList`, `H.polyGauss_pdList`: the iterated partial derivatives of `f` are smooth,
  and those of order at most `4` are dominated by `K (1 + ‖x‖)^m γ_T(x)`.
* `H.pdList_flow`: `pdList (heat f s) l = heat (pdList f l) s` for `s > 0` and `|l| ≤ 4`
  (special cases `H.pd_flow`, `H.pd_pd_flow`).
* `H.exists_abs_pdList_flow_le`, `H.mul_gaussian_le_flow`, `H.flow_le_mul_gaussian`,
  `H.exists_abs_pdList_flow_div_le`: Gaussian bounds on `ρ s` and its derivatives, and
  polynomial bounds on `∂ˡρ s / ρ s`, uniform in `s ∈ (0, t₁]`.
* `H.hasDerivAt_flow`, `H.hasDerivAt_pd_flow`, `H.hasDerivAt_pd_pd_flow`: the heat equation
  `∂ₛ = ½ Σₖ ∂ₖ∂ₖ` for `ρ`, `∂ᵢρ` and `∂ⱼ∂ᵢρ`.
* `H.contDiff_flow`, `H.contDiff_pdList_flow`, `H.flow_pos`: `ρ s` and its iterated partial
  derivatives are smooth, and `ρ s` is positive, for `s > 0`.

## Implementation notes

The domination of the derivatives of `f` is proved with the class
`Fisher41.DensityFlow.Tame n` of smooth prefactors whose iterated partial derivatives of order at
most `n` have polynomial growth. It contains constants and coordinate functions and is closed
under sums and products. Since `∂ᵢ (u γ_T) = (∂ᵢ u - u xᵢ / T) γ_T`
(`Fisher41.DensityFlow.pd_mul_gaussian`), a partial derivative of `u γ_T` with `u` tame of order
`n + 1` is `u' γ_T` with `u'` tame of order `n` (`Fisher41.DensityFlow.GTame.gtame_pd`).
-/

open MeasureTheory Real
open scoped ContDiff Nat

noncomputable section

namespace Fisher41

/-- Iterated coordinate partial derivatives: `pdList g [] = g` and
`pdList g (i :: l) = pdList (pd g i) l`. Thus `pdList g [i₁, …, iₖ] = ∂_{iₖ} ⋯ ∂_{i₁} g`; for
instance `pdList g [i, j] = pd (pd g i) j`. -/
def pdList {d : ℕ} (g : E d → ℝ) : List (Fin d) → E d → ℝ
  | [] => g
  | i :: l => pdList (pd g i) l

/-- The empty iterated partial derivative is the function itself. -/
@[simp]
theorem pdList_nil {d : ℕ} (g : E d → ℝ) : pdList g [] = g := rfl

/-- Unfolding `pdList` on a nonempty list: the head index is differentiated first. -/
@[simp]
theorem pdList_cons {d : ℕ} (g : E d → ℝ) (i : Fin d) (l : List (Fin d)) :
    pdList g (i :: l) = pdList (pd g i) l := rfl

/-- The standing hypotheses of this file: `f = c q γ_T` with `T > 0`, `c > 0`, and a smooth
prefactor `q` with `1 ≤ q ≤ Q` whose iterated partial derivatives of order at most `4` are
bounded. Use `Fisher41.DensityFlowHyp.of_iteratedFDeriv` to build it from bounds on the iterated
Fréchet derivatives `iteratedFDeriv ℝ k q`, `k ≤ 4`, instead. -/
structure DensityFlowHyp (d : ℕ) (T c Q : ℝ) (q f : E d → ℝ) : Prop where
  /-- The variance of the Gaussian envelope is positive. -/
  hT : 0 < T
  /-- The constant factor is positive. -/
  hc : 0 < c
  /-- The prefactor is smooth. -/
  hq : ContDiff ℝ ∞ q
  /-- The prefactor is at least `1`. -/
  hq1 : ∀ x, 1 ≤ q x
  /-- The prefactor is at most `Q`. -/
  hqQ : ∀ x, q x ≤ Q
  /-- The iterated partial derivatives of the prefactor of order at most `4` are bounded. -/
  hqd : ∀ l : List (Fin d), l.length ≤ 4 → ∃ C, ∀ x, |pdList q l x| ≤ C
  /-- The density is `f = c q γ_T`. -/
  hf : ∀ x, f x = c * q x * gaussian d T x

namespace DensityFlow

variable {d : ℕ}

/-! ### Calculus of coordinate partial derivatives -/

/-- A smooth function is `C¹`. -/
theorem contDiff_one_of_contDiff {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ 1 g :=
  contDiff_infty.1 hg 1

/-- A smooth function is differentiable. -/
theorem differentiable_of_contDiff {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) : Differentiable ℝ g :=
  (contDiff_one_of_contDiff hg).differentiable one_ne_zero

/-- Partial derivatives of smooth functions are smooth. -/
theorem contDiff_pd {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin d) : ContDiff ℝ ∞ (pd g i) :=
  (contDiff_infty_iff_fderiv.1 hg).2.clm_apply contDiff_const

/-- Iterated partial derivatives of smooth functions are smooth. -/
theorem contDiff_pdList {g : E d → ℝ} (hg : ContDiff ℝ ∞ g) (l : List (Fin d)) :
    ContDiff ℝ ∞ (pdList g l) := by
  induction l generalizing g with
  | nil => exact hg
  | cons i l ih => exact ih (contDiff_pd hg i)

/-- Additivity of `pd`. -/
theorem pd_add {u v : E d → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (i : Fin d) :
    pd (u + v) i = pd u i + pd v i := by
  funext x
  simp only [pd, Pi.add_apply, fderiv_add (hu x) (hv x), _root_.add_apply]

/-- The Leibniz rule for `pd`. -/
theorem pd_mul {u v : E d → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (i : Fin d) :
    pd (u * v) i = pd u i * v + u * pd v i := by
  funext x
  simp only [pd, Pi.add_apply, Pi.mul_apply, fderiv_mul (hu x) (hv x), _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

/-- Partial derivatives of constants vanish. -/
theorem pd_const (a : ℝ) (i : Fin d) : pd (fun _ : E d => a) i = fun _ => 0 := by
  funext x
  simp [pd]

/-- Partial derivatives of the coordinate functions are constant. -/
theorem pd_coord (j i : Fin d) :
    pd (fun x : E d => x j) i = fun _ => (EuclideanSpace.single i (1 : ℝ) : E d) j := by
  funext x
  have h : HasFDerivAt (fun y : E d => y j) _ x := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x j
  rw [pd, h.fderiv]
  rfl

/-- Additivity of iterated partial derivatives. -/
theorem pdList_add {u v : E d → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (l : List (Fin d)) : pdList (u + v) l = pdList u l + pdList v l := by
  induction l generalizing u v with
  | nil => rfl
  | cons i l ih =>
    simp only [pdList_cons]
    rw [pd_add (differentiable_of_contDiff hu) (differentiable_of_contDiff hv)]
    exact ih (contDiff_pd hu i) (contDiff_pd hv i)

/-- Iterated partial derivatives of constants are constant. -/
theorem exists_pdList_const (a : ℝ) (l : List (Fin d)) :
    ∃ b : ℝ, pdList (fun _ : E d => a) l = fun _ => b := by
  induction l generalizing a with
  | nil => exact ⟨a, rfl⟩
  | cons i l ih =>
    rw [pdList_cons, pd_const]
    exact ih 0

/-- The operator norm of the derivative is at most the sum of the absolute values of the
partial derivatives. -/
theorem norm_fderiv_le_sum_abs_pd (g : E d → ℝ) (x : E d) :
    ‖fderiv ℝ g x‖ ≤ ∑ i, |pd g i x| := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => abs_nonneg _) fun v => ?_
  have hv : ∑ i, v i • (EuclideanSpace.single i (1 : ℝ) : E d) = v := by
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
    exact h
  have hfv : fderiv ℝ g x v = ∑ i, v i * pd g i x := by
    calc fderiv ℝ g x v
        = fderiv ℝ g x (∑ i, v i • (EuclideanSpace.single i (1 : ℝ) : E d)) := by rw [hv]
      _ = ∑ i, v i * pd g i x := by simp only [map_sum, map_smul, smul_eq_mul, pd]
  rw [hfv, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le v i) (abs_nonneg _)

/-- An iterated partial derivative is bounded by the norm of the iterated Fréchet derivative of
the same order. -/
theorem abs_pdList_le_norm_iteratedFDeriv {g : E d → ℝ} (hg : ContDiff ℝ ∞ g)
    (l : List (Fin d)) (x : E d) : |pdList g l x| ≤ ‖iteratedFDeriv ℝ l.length g x‖ := by
  induction l generalizing g with
  | nil => simp
  | cons i l ih =>
    have hD : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg).2
    calc |pdList g (i :: l) x| = |pdList (pd g i) l x| := rfl
      _ ≤ ‖iteratedFDeriv ℝ l.length (pd g i) x‖ := ih (contDiff_pd hg i)
      _ ≤ ‖(EuclideanSpace.single i (1 : ℝ) : E d)‖ *
            ‖iteratedFDeriv ℝ l.length (fderiv ℝ g) x‖ :=
          norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ g) hD.contDiffAt (mod_cast le_top)
      _ = ‖iteratedFDeriv ℝ (i :: l).length g x‖ := by
          rw [List.length_cons, ← norm_iteratedFDeriv_fderiv]
          simp

/-! ### The Gaussian -/

/-- The Gaussian is smooth. -/
theorem contDiff_gaussian (T : ℝ) : ContDiff ℝ ∞ (gaussian d T) :=
  contDiff_const.mul ((contDiff_norm_sq ℝ).neg.div_const _).exp

/-- Partial derivatives of the Gaussian: `∂ᵢ γ_T(x) = -(xᵢ / T) γ_T(x)`. -/
theorem pd_gaussian (T : ℝ) (i : Fin d) (x : E d) :
    pd (gaussian d T) i x = -(x i / T) * gaussian d T x := by
  have hfun : (fun y : E d => -‖y‖ ^ 2 / (2 * T)) = fun y => -(2 * T)⁻¹ * ‖y‖ ^ 2 := by
    funext y
    ring
  have h₁ : HasFDerivAt (fun y : E d => -‖y‖ ^ 2 / (2 * T))
      (-(2 * T)⁻¹ • (2 • innerSL ℝ x)) x := by
    rw [hfun]
    exact (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul _
  have h₂ : HasFDerivAt (gaussian d T) ((2 * π * T) ^ (-(d : ℝ) / 2) •
      (exp (-‖x‖ ^ 2 / (2 * T)) • (-(2 * T)⁻¹ • (2 • innerSL ℝ x)))) x :=
    h₁.exp.const_mul _
  rw [pd, h₂.fderiv]
  simp only [two_nsmul, _root_.add_apply, _root_.smul_apply, smul_eq_mul, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, gaussian]
  ring

/-- Partial derivatives of the Gaussian, as an identity of functions. -/
theorem pd_gaussian_eq (T : ℝ) (i : Fin d) :
    pd (gaussian d T) i = (fun _ : E d => -T⁻¹) * (fun x : E d => x i) * gaussian d T := by
  funext x
  rw [pd_gaussian]
  simp only [Pi.mul_apply]
  ring

/-- **Partial derivatives of Gaussian-weighted functions**:
`∂ᵢ (u γ_T) = (∂ᵢ u) γ_T - u (xᵢ / T) γ_T`. -/
theorem pd_mul_gaussian {u : E d → ℝ} (hu : Differentiable ℝ u) (T : ℝ) (i : Fin d)
    (x : E d) :
    pd (u * gaussian d T) i x =
      pd u i x * gaussian d T x - u x * (x i / T) * gaussian d T x := by
  rw [pd_mul hu (differentiable_of_contDiff (contDiff_gaussian T))]
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [pd_gaussian]
  ring

/-- A function dominated by a polynomially weighted Gaussian is bounded. -/
theorem exists_abs_le_of_polyGauss {T : ℝ} (hT : 0 < T) {g : E d → ℝ} (hg : PolyGauss T g) :
    ∃ M, ∀ x, |g x| ≤ M := by
  obtain ⟨K, m, h⟩ := hg
  refine ⟨|K| * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + T)) * (2 * π * (2 * T)) ^ (-(d : ℝ) / 2)),
    fun x => ?_⟩
  have hP : 0 ≤ (1 + ‖x‖) ^ m * gaussian d T x :=
    mul_nonneg (by positivity) (gaussian_pos hT x).le
  calc |g x| ≤ K * (1 + ‖x‖) ^ m * gaussian d T x := h x
    _ = K * ((1 + ‖x‖) ^ m * gaussian d T x) := mul_assoc _ _ _
    _ ≤ |K| * ((1 + ‖x‖) ^ m * gaussian d T x) := mul_le_mul_of_nonneg_right (le_abs_self K) hP
    _ ≤ |K| * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + T)) * gaussian d (2 * T) x) :=
        mul_le_mul_of_nonneg_left (Domination.one_add_norm_pow_mul_gaussian_le m hT x)
          (abs_nonneg K)
    _ ≤ |K| * (2 ^ ((d : ℝ) / 2) * (m ! * exp (1 + T)) * (2 * π * (2 * T)) ^ (-(d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (gaussian_le (by positivity) x) (by positivity)) (abs_nonneg K)

/-- **Gaussian upper bounds propagate along the heat flow**: if `f` is integrable and
`f ≤ C γ_T`, then `heat f t ≤ C γ_{T+t}` for `T, t > 0`. -/
theorem heat_le_mul_gaussian {f : E d → ℝ} {C T t : ℝ} (hf : Integrable f)
    (hfC : ∀ y, f y ≤ C * gaussian d T y) (hT : 0 < T) (ht : 0 < t) (x : E d) :
    heat f t x ≤ C * gaussian d (T + t) x := by
  have h := mul_gaussian_le_heat (f := -f) (c := -C) hf.neg
    (fun y => by rw [Pi.neg_apply, neg_mul]; exact neg_le_neg (hfC y)) hT ht x
  have hneg : heat (-f) t x = -heat f t x := by
    simp only [heat, Pi.neg_apply, neg_mul, integral_neg]
  rw [hneg, neg_mul] at h
  exact neg_le_neg_iff.1 h

/-! ### Polynomial growth -/

/-- Polynomial growth: `|u x| ≤ K (1 + ‖x‖)^m` for some `K` and `m`. -/
def PolyGrowth (u : E d → ℝ) : Prop :=
  ∃ K : ℝ, ∃ m : ℕ, ∀ x, |u x| ≤ K * (1 + ‖x‖) ^ m

/-- Bounded functions have polynomial growth. -/
theorem PolyGrowth.of_abs_le_const {u : E d → ℝ} {C : ℝ} (h : ∀ x, |u x| ≤ C) :
    PolyGrowth u :=
  ⟨C, 0, fun x => by simpa using h x⟩

/-- Constants have polynomial growth. -/
theorem PolyGrowth.const (a : ℝ) : PolyGrowth (fun _ : E d => a) :=
  PolyGrowth.of_abs_le_const (C := |a|) fun _ => le_rfl

/-- Coordinate functions have polynomial growth. -/
theorem PolyGrowth.coord (j : Fin d) : PolyGrowth (fun x : E d => x j) := by
  refine ⟨1, 1, fun x => ?_⟩
  show |x j| ≤ 1 * (1 + ‖x‖) ^ 1
  rw [pow_one, one_mul, ← Real.norm_eq_abs]
  exact (PiLp.norm_apply_le x j).trans (le_add_of_nonneg_left zero_le_one)

/-- Sums of functions of polynomial growth have polynomial growth. -/
theorem PolyGrowth.add {u v : E d → ℝ} (hu : PolyGrowth u) (hv : PolyGrowth v) :
    PolyGrowth (u + v) := by
  obtain ⟨K₁, m₁, h₁⟩ := hu
  obtain ⟨K₂, m₂, h₂⟩ := hv
  refine ⟨|K₁| + |K₂|, max m₁ m₂, fun x => ?_⟩
  have hx : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have key : ∀ (K : ℝ) (k : ℕ), k ≤ max m₁ m₂ →
      K * (1 + ‖x‖) ^ k ≤ |K| * (1 + ‖x‖) ^ max m₁ m₂ :=
    fun K k hk => mul_le_mul (le_abs_self K) (pow_le_pow_right₀ hx hk) (by positivity)
      (abs_nonneg K)
  calc |(u + v) x| ≤ |u x| + |v x| := abs_add_le (u x) (v x)
    _ ≤ K₁ * (1 + ‖x‖) ^ m₁ + K₂ * (1 + ‖x‖) ^ m₂ := add_le_add (h₁ x) (h₂ x)
    _ ≤ |K₁| * (1 + ‖x‖) ^ max m₁ m₂ + |K₂| * (1 + ‖x‖) ^ max m₁ m₂ :=
        add_le_add (key K₁ m₁ (le_max_left _ _)) (key K₂ m₂ (le_max_right _ _))
    _ = (|K₁| + |K₂|) * (1 + ‖x‖) ^ max m₁ m₂ := by ring

/-- Products of functions of polynomial growth have polynomial growth. -/
theorem PolyGrowth.mul {u v : E d → ℝ} (hu : PolyGrowth u) (hv : PolyGrowth v) :
    PolyGrowth (u * v) := by
  obtain ⟨K₁, m₁, h₁⟩ := hu
  obtain ⟨K₂, m₂, h₂⟩ := hv
  refine ⟨K₁ * K₂, m₁ + m₂, fun x => ?_⟩
  calc |(u * v) x| = |u x| * |v x| := abs_mul (u x) (v x)
    _ ≤ K₁ * (1 + ‖x‖) ^ m₁ * (K₂ * (1 + ‖x‖) ^ m₂) :=
        mul_le_mul (h₁ x) (h₂ x) (abs_nonneg _) ((abs_nonneg _).trans (h₁ x))
    _ = K₁ * K₂ * (1 + ‖x‖) ^ (m₁ + m₂) := by ring

/-! ### Tame prefactors -/

/-- `Tame n u`: `u` is smooth, and `u` and all its iterated partial derivatives of order at most
`n` have polynomial growth. -/
def Tame (n : ℕ) (u : E d → ℝ) : Prop :=
  ContDiff ℝ ∞ u ∧ ∀ l : List (Fin d), l.length ≤ n → PolyGrowth (pdList u l)

/-- Tame functions are smooth. -/
theorem Tame.contDiff {n : ℕ} {u : E d → ℝ} (h : Tame n u) : ContDiff ℝ ∞ u := h.1

/-- Tame functions are differentiable. -/
theorem Tame.differentiable {n : ℕ} {u : E d → ℝ} (h : Tame n u) : Differentiable ℝ u :=
  differentiable_of_contDiff h.1

/-- Tame functions have polynomial growth. -/
theorem Tame.polyGrowth {n : ℕ} {u : E d → ℝ} (h : Tame n u) : PolyGrowth u :=
  h.2 [] (Nat.zero_le n)

/-- Tameness of higher order implies tameness of lower order. -/
theorem Tame.of_le {m n : ℕ} {u : E d → ℝ} (hmn : m ≤ n) (h : Tame n u) : Tame m u :=
  ⟨h.1, fun l hl => h.2 l (hl.trans hmn)⟩

/-- Partial derivatives of tame functions are tame, of one order less. -/
theorem Tame.tame_pd {n : ℕ} {u : E d → ℝ} (h : Tame (n + 1) u) (i : Fin d) :
    Tame n (pd u i) :=
  ⟨contDiff_pd h.1 i, fun l hl => h.2 (i :: l) (by simp only [List.length_cons]; omega)⟩

/-- Smooth functions of polynomial growth are tame of order `0`. -/
theorem Tame.zero {u : E d → ℝ} (hu : ContDiff ℝ ∞ u) (hp : PolyGrowth u) : Tame 0 u := by
  refine ⟨hu, fun l hl => ?_⟩
  cases l with
  | nil => exact hp
  | cons i l =>
    simp only [List.length_cons] at hl
    omega

/-- A smooth function of polynomial growth whose partial derivatives are tame of order `n` is
tame of order `n + 1`. -/
theorem Tame.of_succ {n : ℕ} {u : E d → ℝ} (hu : ContDiff ℝ ∞ u) (hp : PolyGrowth u)
    (h : ∀ i, Tame n (pd u i)) : Tame (n + 1) u := by
  refine ⟨hu, fun l hl => ?_⟩
  cases l with
  | nil => exact hp
  | cons i l =>
    simp only [List.length_cons] at hl
    exact (h i).2 l (by omega)

/-- Constants are tame. -/
theorem Tame.const (n : ℕ) (a : ℝ) : Tame n (fun _ : E d => a) := by
  refine ⟨contDiff_const, fun l _ => ?_⟩
  obtain ⟨b, hb⟩ := exists_pdList_const (d := d) a l
  rw [hb]
  exact PolyGrowth.const b

/-- Coordinate functions are tame. -/
theorem Tame.coord (n : ℕ) (j : Fin d) : Tame n (fun x : E d => x j) := by
  refine ⟨contDiff_piLp_apply 2, fun l _ => ?_⟩
  cases l with
  | nil => exact PolyGrowth.coord j
  | cons i l =>
    obtain ⟨b, hb⟩ :=
      exists_pdList_const (d := d) ((EuclideanSpace.single i (1 : ℝ) : E d) j) l
    rw [pdList_cons, pd_coord, hb]
    exact PolyGrowth.const b

/-- Sums of tame functions are tame. -/
theorem Tame.add {n : ℕ} {u v : E d → ℝ} (hu : Tame n u) (hv : Tame n v) : Tame n (u + v) := by
  refine ⟨hu.1.add hv.1, fun l hl => ?_⟩
  rw [pdList_add hu.1 hv.1]
  exact (hu.2 l hl).add (hv.2 l hl)

/-- Products of tame functions are tame. -/
theorem Tame.mul {n : ℕ} {u v : E d → ℝ} (hu : Tame n u) (hv : Tame n v) : Tame n (u * v) := by
  induction n generalizing u v with
  | zero => exact Tame.zero (hu.1.mul hv.1) (hu.polyGrowth.mul hv.polyGrowth)
  | succ n ih =>
    refine Tame.of_succ (hu.1.mul hv.1) (hu.polyGrowth.mul hv.polyGrowth) fun i => ?_
    rw [pd_mul hu.differentiable hv.differentiable]
    exact (ih (hu.tame_pd i) (hv.of_le n.le_succ)).add (ih (hu.of_le n.le_succ) (hv.tame_pd i))

/-! ### Gaussian-weighted tame functions -/

/-- `GTame T n g`: `g = u γ_T` for a prefactor `u` that is tame of order `n`. -/
def GTame (T : ℝ) (n : ℕ) (g : E d → ℝ) : Prop :=
  ∃ u : E d → ℝ, Tame n u ∧ g = u * gaussian d T

/-- Gaussian-weighted tame functions are smooth. -/
theorem GTame.contDiff {T : ℝ} {n : ℕ} {g : E d → ℝ} (h : GTame T n g) : ContDiff ℝ ∞ g := by
  obtain ⟨u, hu, rfl⟩ := h
  exact hu.1.mul (contDiff_gaussian T)

/-- Gaussian-weighted tame functions are dominated by polynomially weighted Gaussians. -/
theorem GTame.polyGauss {T : ℝ} (hT : 0 ≤ T) {n : ℕ} {g : E d → ℝ} (h : GTame T n g) :
    PolyGauss T g := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨K, m, hK⟩ := hu.polyGrowth
  exact (polyGauss_gaussian hT).mul_poly hK

/-- Partial derivatives of Gaussian-weighted tame functions are Gaussian-weighted tame
functions, of one order less. -/
theorem GTame.gtame_pd {T : ℝ} {n : ℕ} {g : E d → ℝ} (h : GTame T (n + 1) g) (i : Fin d) :
    GTame T n (pd g i) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨pd u i + u * ((fun _ : E d => -T⁻¹) * fun x : E d => x i), ?_, ?_⟩
  · exact (hu.tame_pd i).add ((hu.of_le n.le_succ).mul ((Tame.const n _).mul (Tame.coord n i)))
  · rw [pd_mul hu.differentiable (differentiable_of_contDiff (contDiff_gaussian T)),
      pd_gaussian_eq]
    ring

/-- Iterated partial derivatives of Gaussian-weighted tame functions. -/
theorem GTame.gtame_pdList {T : ℝ} (l : List (Fin d)) {n : ℕ} {g : E d → ℝ}
    (h : GTame T n g) (hl : l.length ≤ n) : GTame T (n - l.length) (pdList g l) := by
  induction l generalizing n g with
  | nil => simpa using h
  | cons i l ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by simp only [List.length_cons] at hl; omega⟩
    have hl' : l.length ≤ m := by simp only [List.length_cons] at hl; omega
    have h' := ih (h.gtame_pd i) hl'
    simp only [pdList_cons, List.length_cons]
    rwa [Nat.add_sub_add_right]

/-- The derivative of a Gaussian-weighted function, tame of order at least `1`, is bounded. -/
theorem GTame.exists_norm_fderiv_le {T : ℝ} (hT : 0 < T) {n : ℕ} {g : E d → ℝ}
    (h : GTame T (n + 1) g) : ∃ M, ∀ x, ‖fderiv ℝ g x‖ ≤ M := by
  have hb : ∀ i, ∃ M, ∀ x, |pd g i x| ≤ M := fun i =>
    exists_abs_le_of_polyGauss hT ((h.gtame_pd i).polyGauss hT.le)
  choose M hM using hb
  exact ⟨∑ i, M i, fun x => (norm_fderiv_le_sum_abs_pd g x).trans
    (Finset.sum_le_sum fun i _ => hM i x)⟩

/-- **Iterated partial derivatives commute with the heat flow** for Gaussian-weighted tame
functions: `pdList (heat g s) l = heat (pdList g l) s` for `s > 0` and `|l| ≤ n`. -/
theorem GTame.pdList_heat {T s : ℝ} (hT : 0 < T) (hs : 0 < s) (l : List (Fin d)) {n : ℕ}
    {g : E d → ℝ} (h : GTame T n g) (hl : l.length ≤ n) :
    pdList (heat g s) l = heat (pdList g l) s := by
  induction l generalizing n g with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by simp only [List.length_cons] at hl; omega⟩
    have hl' : l.length ≤ m := by simp only [List.length_cons] at hl; omega
    obtain ⟨M, hM⟩ := exists_abs_le_of_polyGauss hT (h.polyGauss hT.le)
    obtain ⟨M', hM'⟩ := h.exists_norm_fderiv_le hT
    have hpd : pd (heat g s) i = heat (pd g i) s :=
      funext fun x => pd_heat (contDiff_one_of_contDiff h.contDiff) hM hM' hs i x
    simp only [pdList_cons]
    rw [hpd, ih (h.gtame_pd i) hl']

end DensityFlow

namespace DensityFlowHyp

variable {d : ℕ} {T c Q : ℝ} {q f : E d → ℝ}

/-- Build the standing hypotheses from bounds on the iterated Fréchet derivatives of the
prefactor: `‖iteratedFDeriv ℝ k q x‖ ≤ C` for `k ≤ 4`. -/
theorem of_iteratedFDeriv (hT : 0 < T) (hc : 0 < c) (hq : ContDiff ℝ ∞ q)
    (hq1 : ∀ x, 1 ≤ q x) (hqQ : ∀ x, q x ≤ Q)
    (hqd : ∀ k : ℕ, k ≤ 4 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ C)
    (hf : ∀ x, f x = c * q x * gaussian d T x) : DensityFlowHyp d T c Q q f where
  hT := hT
  hc := hc
  hq := hq
  hq1 := hq1
  hqQ := hqQ
  hqd l hl := by
    obtain ⟨C, hC⟩ := hqd l.length hl
    exact ⟨C, fun x => (DensityFlow.abs_pdList_le_norm_iteratedFDeriv hq l x).trans (hC x)⟩
  hf := hf

/-- The upper bound `Q` is at least `1`. -/
theorem one_le_Q (H : DensityFlowHyp d T c Q q f) : 1 ≤ Q :=
  (H.hq1 0).trans (H.hqQ 0)

/-- `f = (c q) γ_T`, where the prefactor `c q` is tame of order `4`. -/
theorem gtame (H : DensityFlowHyp d T c Q q f) : DensityFlow.GTame T 4 f := by
  have hq4 : DensityFlow.Tame 4 q := by
    refine ⟨H.hq, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := H.hqd l hl
    exact DensityFlow.PolyGrowth.of_abs_le_const hC
  refine ⟨(fun _ : E d => c) * q, (DensityFlow.Tame.const 4 c).mul hq4, ?_⟩
  funext x
  rw [H.hf x]
  rfl

/-! #### The initial density -/

/-- The density `f` is smooth. -/
theorem contDiff (H : DensityFlowHyp d T c Q q f) : ContDiff ℝ ∞ f :=
  H.gtame.contDiff

/-- The density `f` is positive. -/
theorem pos (H : DensityFlowHyp d T c Q q f) (x : E d) : 0 < f x := by
  rw [H.hf x]
  exact mul_pos (mul_pos H.hc (zero_lt_one.trans_le (H.hq1 x))) (gaussian_pos H.hT x)

/-- Gaussian lower bound: `c γ_T ≤ f`. -/
theorem mul_gaussian_le (H : DensityFlowHyp d T c Q q f) (x : E d) :
    c * gaussian d T x ≤ f x := by
  rw [H.hf x]
  calc c * gaussian d T x = c * 1 * gaussian d T x := by rw [mul_one]
    _ ≤ c * q x * gaussian d T x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (H.hq1 x) H.hc.le)
          (gaussian_pos H.hT x).le

/-- Gaussian upper bound: `f ≤ c Q γ_T`. -/
theorem le_mul_gaussian (H : DensityFlowHyp d T c Q q f) (x : E d) :
    f x ≤ c * Q * gaussian d T x := by
  rw [H.hf x]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (H.hqQ x) H.hc.le)
    (gaussian_pos H.hT x).le

/-- The density `f` is bounded. -/
theorem abs_le (H : DensityFlowHyp d T c Q q f) (x : E d) :
    |f x| ≤ c * Q * (2 * π * T) ^ (-(d : ℝ) / 2) := by
  rw [abs_of_pos (H.pos x)]
  exact (H.le_mul_gaussian x).trans (mul_le_mul_of_nonneg_left (gaussian_le H.hT x)
    (mul_nonneg H.hc.le (zero_le_one.trans H.one_le_Q)))

/-- The density `f` is integrable. -/
theorem integrable (H : DensityFlowHyp d T c Q q f) : Integrable f := by
  refine ((integrable_gaussian H.hT).const_mul (c * Q)).mono'
    H.contDiff.continuous.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (H.pos x).le]
  exact H.le_mul_gaussian x

/-- The density `f` is measurable. -/
theorem aestronglyMeasurable (H : DensityFlowHyp d T c Q q f) : AEStronglyMeasurable f :=
  H.contDiff.continuous.aestronglyMeasurable

/-- The density `f` is essentially bounded. -/
theorem ae_norm_le (H : DensityFlowHyp d T c Q q f) :
    ∀ᵐ y ∂(volume : Measure (E d)), ‖f y‖ ≤ c * Q * (2 * π * T) ^ (-(d : ℝ) / 2) :=
  ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]
    exact H.abs_le y

/-- The iterated partial derivatives of `f` are smooth. -/
theorem contDiff_pdList (H : DensityFlowHyp d T c Q q f) (l : List (Fin d)) :
    ContDiff ℝ ∞ (pdList f l) :=
  DensityFlow.contDiff_pdList H.contDiff l

/-- The iterated partial derivatives of `f` of order at most `4` are dominated by
polynomially weighted Gaussians: `|pdList f l x| ≤ K (1 + ‖x‖)^m γ_T(x)`. -/
theorem polyGauss_pdList (H : DensityFlowHyp d T c Q q f) {l : List (Fin d)}
    (hl : l.length ≤ 4) : PolyGauss T (pdList f l) :=
  (H.gtame.gtame_pdList l hl).polyGauss H.hT.le

/-! #### The heat flow -/

/-- **Derivatives commute with the heat flow**: `pdList (heat f s) l = heat (pdList f l) s` for
`s > 0` and `|l| ≤ 4`. -/
theorem pdList_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) {l : List (Fin d)}
    (hl : l.length ≤ 4) : pdList (heat f s) l = heat (pdList f l) s :=
  DensityFlow.GTame.pdList_heat H.hT hs l H.gtame hl

/-- `∂ᵢ (heat f s) = heat (∂ᵢ f) s` for `s > 0`. -/
theorem pd_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) (i : Fin d) :
    pd (heat f s) i = heat (pd f i) s :=
  H.pdList_flow hs (l := [i]) (by simp)

/-- `∂ⱼ ∂ᵢ (heat f s) = heat (∂ⱼ ∂ᵢ f) s` for `s > 0`. -/
theorem pd_pd_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) (i j : Fin d) :
    pd (pd (heat f s) i) j = heat (pd (pd f i) j) s :=
  H.pdList_flow hs (l := [i, j]) (by simp)

/-- **Uniform Gaussian bounds on the derivatives of the heat flow**: for `|l| ≤ 4` and every
`t₁`, there are `K ≥ 0` and `m` with
`|pdList (heat f s) l x| ≤ K (1 + ‖x‖)^m γ_{T+s}(x)` for all `s ∈ (0, t₁]` and all `x`. -/
theorem exists_abs_pdList_flow_le (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ)
    {l : List (Fin d)} (hl : l.length ≤ 4) :
    ∃ K : ℝ, ∃ m : ℕ, 0 ≤ K ∧ ∀ s ∈ Set.Ioc 0 t₁, ∀ x,
      |pdList (heat f s) l x| ≤ K * (1 + ‖x‖) ^ m * gaussian d (T + s) x := by
  obtain ⟨K₀, m, hK₀⟩ := H.polyGauss_pdList hl
  obtain ⟨C, hC0, hC⟩ := exists_abs_heat_le (d := d) m H.hT t₁
  refine ⟨K₀ * C, m, mul_nonneg (Domination.nonneg_of_forall_abs_le H.hT hK₀) hC0,
    fun s hs x => ?_⟩
  rw [H.pdList_flow hs.1 hl]
  exact hC (pdList f l) K₀ hK₀ s hs x

/-- Gaussian lower bound along the heat flow: `c γ_{T+s} ≤ heat f s` for `s > 0`. -/
theorem mul_gaussian_le_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) (x : E d) :
    c * gaussian d (T + s) x ≤ heat f s x :=
  mul_gaussian_le_heat H.integrable H.mul_gaussian_le H.hT hs x

/-- Gaussian upper bound along the heat flow: `heat f s ≤ c Q γ_{T+s}` for `s > 0`. -/
theorem flow_le_mul_gaussian (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) (x : E d) :
    heat f s x ≤ c * Q * gaussian d (T + s) x :=
  DensityFlow.heat_le_mul_gaussian H.integrable H.le_mul_gaussian H.hT hs x

/-- The heat flow is positive at positive times. -/
theorem flow_pos (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) (x : E d) :
    0 < heat f s x :=
  (mul_pos H.hc (gaussian_pos (add_pos H.hT hs) x)).trans_le (H.mul_gaussian_le_flow hs x)

/-- **Uniform polynomial bounds on logarithmic-type ratios**: for `|l| ≤ 4` and every `t₁`,
there are `K` and `m` with `|pdList (heat f s) l x / heat f s x| ≤ K (1 + ‖x‖)^m` for all
`s ∈ (0, t₁]` and all `x`. -/
theorem exists_abs_pdList_flow_div_le (H : DensityFlowHyp d T c Q q f) (t₁ : ℝ)
    {l : List (Fin d)} (hl : l.length ≤ 4) :
    ∃ K : ℝ, ∃ m : ℕ, ∀ s ∈ Set.Ioc 0 t₁, ∀ x,
      |pdList (heat f s) l x / heat f s x| ≤ K * (1 + ‖x‖) ^ m := by
  obtain ⟨K, m, hK0, hK⟩ := H.exists_abs_pdList_flow_le t₁ hl
  refine ⟨K / c, m, fun s hs x => ?_⟩
  have hlow := H.mul_gaussian_le_flow hs.1 x
  have hρ : 0 < heat f s x := H.flow_pos hs.1 x
  rw [abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  calc |pdList (heat f s) l x| ≤ K * (1 + ‖x‖) ^ m * gaussian d (T + s) x := hK s hs x
    _ = K / c * (1 + ‖x‖) ^ m * (c * gaussian d (T + s) x) := by
        rw [show K / c * (1 + ‖x‖) ^ m * (c * gaussian d (T + s) x) =
          K / c * c * (1 + ‖x‖) ^ m * gaussian d (T + s) x by ring,
          div_mul_cancel₀ K H.hc.ne']
    _ ≤ K / c * (1 + ‖x‖) ^ m * heat f s x :=
        mul_le_mul_of_nonneg_left hlow (mul_nonneg (div_nonneg hK0 H.hc.le) (by positivity))

/-- **The heat equation**: `∂ₛ heat f s x = ½ Σₖ ∂ₖ∂ₖ (heat f s) x` for `s > 0`. -/
theorem hasDerivAt_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) (x : E d) :
    HasDerivAt (fun r => heat f r x) ((1 / 2) * ∑ k, pd (pd (heat f s) k) k x) s :=
  hasDerivAt_heat_sum_pd H.aestronglyMeasurable H.ae_norm_le hs x

/-- **The heat equation for first derivatives**:
`∂ₛ ∂ᵢ heat f s x = ½ Σₖ ∂ₖ∂ₖ ∂ᵢ (heat f s) x` for `s > 0`. -/
theorem hasDerivAt_pd_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) (i : Fin d)
    (x : E d) :
    HasDerivAt (fun r => pd (heat f r) i x)
      ((1 / 2) * ∑ k, pd (pd (pd (heat f s) i) k) k x) s := by
  obtain ⟨M', hM'⟩ := H.gtame.exists_norm_fderiv_le H.hT
  exact hasDerivAt_pd_heat (DensityFlow.contDiff_one_of_contDiff H.contDiff) H.abs_le hM' hs i x

/-- **The heat equation for second derivatives**:
`∂ₛ ∂ⱼ∂ᵢ heat f s x = ½ Σₖ ∂ₖ∂ₖ ∂ⱼ∂ᵢ (heat f s) x` for `s > 0`. -/
theorem hasDerivAt_pd_pd_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s)
    (i j : Fin d) (x : E d) :
    HasDerivAt (fun r => pd (pd (heat f r) i) j x)
      ((1 / 2) * ∑ k, pd (pd (pd (pd (heat f s) i) j) k) k x) s := by
  have hGi := H.gtame.gtame_pd i
  obtain ⟨N, hN⟩ := DensityFlow.exists_abs_le_of_polyGauss H.hT (hGi.polyGauss H.hT.le)
  obtain ⟨N', hN'⟩ := hGi.exists_norm_fderiv_le H.hT
  have key := hasDerivAt_pd_heat (DensityFlow.contDiff_one_of_contDiff hGi.contDiff) hN hN' hs j x
  rw [← H.pd_flow hs i] at key
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hs] with r hr
  rw [H.pd_flow hr i]

/-- The heat flow is smooth at positive times. -/
theorem contDiff_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (heat f s) :=
  contDiff_heat H.aestronglyMeasurable H.ae_norm_le hs

/-- The iterated partial derivatives of the heat flow are smooth at positive times. -/
theorem contDiff_pdList_flow (H : DensityFlowHyp d T c Q q f) {s : ℝ} (hs : 0 < s)
    (l : List (Fin d)) : ContDiff ℝ ∞ (pdList (heat f s) l) :=
  DensityFlow.contDiff_pdList (H.contDiff_flow hs) l

end DensityFlowHyp

end Fisher41
