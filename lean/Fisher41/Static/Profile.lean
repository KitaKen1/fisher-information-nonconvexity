/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Defs
import Fisher41.Density
import Fisher41.Static.Cutoff
import Fisher41.Numerics.JetSound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The radial profile `u`, its cut-off `ũ`, and the cut-off error

Notation: `V(s) = 15 - 2s - s²` (`Vfun`), `u = uprof = (4/3) log(1 + e^V)`,
`σ = Num.sigma` (`σ t = eᵗ/(1+eᵗ)`), `ũ = ucut = η(s/16) u(s)`.

## Main definitions

* `u1`, `u2`, `u3`: the first three derivatives of `u`, written with `σ(V)`.
* `uc1`, `uc2`, `uc3`: the first three derivatives of `ũ` (Leibniz rule).
* `Fmath`, `Fcut`: the radial integrands `r⁴⁰ e^{u} K₄₁(s, -u', u'', u''')` at `s = r²/2`,
  built from `u` resp. `ũ`.

## Main results

* `hasDerivAt_uprof`, `hasDerivAt_u1`, `hasDerivAt_u2`: `u' = u1`, `u1' = u2`, `u2' = u3`.
* `radialC2_f_eq`: the computer-checked integrand `Num.radialC2.f` equals `Fmath`.
* `hasDerivAt_ucut`, `hasDerivAt_uc1`, `hasDerivAt_uc2`: `ũ' = uc1`, `uc1' = uc2`, `uc2' = uc3`.
* `ucut_eq_uprof`, `uc1_eq_u1`, `uc2_eq_u2`, `uc3_eq_u3` (for `s ≤ 16`) and
  `ucut_eq_zero`, `uc1_eq_zero`, `uc2_eq_zero`, `uc3_eq_zero` (for `32 ≤ s`).
* `Fcut_eq_Fmath`, `Fcut_eq_zero`, `abs_Fcut_le_one`, `abs_Fmath_le_one`, and the cut-off
  error bound `integral_Fcut_le`.

## Proof notes

* The derivatives of `η` vanish on `(-∞, 1]` and on `[2, ∞)`: this is read off from the
  differentiated identities `η · G = b(2 - ·)` of `Fisher41.Static.Cutoff`, since there the
  relevant `bₖ`-terms vanish and `G > 0`.
* Tail bounds (`s ≥ 16`, `τ = e^{V(s)}`): `σ(V) ≤ τ`, so `|u|, |u'|, |u''|, |u'''| ≤ 100 s³ τ`,
  and with `|η⁽ᵏ⁾(s/16)/16ᵏ| ≤ 1000` also `|ũ⁽ᵏ⁾| ≤ 10⁶ s³ τ`.  Then `|K₄₁| ≤ 500 s³ M²` with
  `M = 10⁶ s³ τ ≤ 1`, and the decay `s³⁰ τ ≤ 15!`, `τ ≤ 2⁻²⁰⁰` makes the integrand tiny.
  These bounds hold for every `s ≥ 16`, so no upper bound on `r` is needed for them.
-/

open MeasureTheory

noncomputable section

namespace Fisher41

/-! ### The derivatives of `u` -/

/-- First derivative of `u`: `u' = (4/3) σ(V) V'` with `V' = -2 - 2s`. -/
def u1 (s : ℝ) : ℝ := 4 / 3 * (Num.sigma (Vfun s) * (-2 - 2 * s))

/-- Second derivative of `u`: `u'' = (4/3) (σ(V) V'' + σ(V)(1 - σ(V)) V'²)`. -/
def u2 (s : ℝ) : ℝ := 4 / 3 * (-2 * Num.sigma (Vfun s) +
    Num.sigma (Vfun s) * (1 - Num.sigma (Vfun s)) * (-2 - 2 * s) ^ 2)

/-- Third derivative of `u`. -/
def u3 (s : ℝ) : ℝ := 4 / 3 * (-6 * Num.sigma (Vfun s) * (1 - Num.sigma (Vfun s)) * (-2 - 2 * s) +
    Num.sigma (Vfun s) * (1 - Num.sigma (Vfun s)) * (1 - 2 * Num.sigma (Vfun s)) * (-2 - 2 * s) ^ 3)

namespace Profile

/-- `V' = -2 - 2s`. -/
theorem hasDerivAt_Vfun (s : ℝ) : HasDerivAt Vfun (-2 - 2 * s) s :=
  (((hasDerivAt_const s (15 : ℝ)).fun_sub ((hasDerivAt_id' s).const_mul (2 : ℝ))).fun_sub
    (hasDerivAt_pow 2 s)).congr_deriv (by ring)

/-- `(σ ∘ V)' = σ(V) (1 - σ(V)) V'`. -/
theorem hasDerivAt_sigmaV (s : ℝ) :
    HasDerivAt (fun t => Num.sigma (Vfun t))
      (Num.sigma (Vfun s) * (1 - Num.sigma (Vfun s)) * (-2 - 2 * s)) s :=
  (Num.C2F.hasDerivAt_sigma (Vfun s)).comp s (hasDerivAt_Vfun s)

/-- `V'` has derivative `V'' = -2`. -/
theorem hasDerivAt_W (s : ℝ) : HasDerivAt (fun t : ℝ => -2 - 2 * t) (-2) s :=
  ((hasDerivAt_const s (-2 : ℝ)).fun_sub ((hasDerivAt_id' s).const_mul (2 : ℝ))).congr_deriv
    (by ring)

end Profile

/-- `u' = u1`. -/
theorem hasDerivAt_uprof (s : ℝ) : HasDerivAt uprof (u1 s) s := by
  have h1 := (hasDerivAt_const s (1 : ℝ)).fun_add (Profile.hasDerivAt_Vfun s).exp
  have hpos : 1 + Real.exp (Vfun s) ≠ 0 := by positivity
  refine ((h1.log hpos).const_mul (4 / 3 : ℝ)).congr_deriv ?_
  simp only [u1, Num.sigma]
  ring

/-- `u1' = u2`. -/
theorem hasDerivAt_u1 (s : ℝ) : HasDerivAt u1 (u2 s) s := by
  refine (((Profile.hasDerivAt_sigmaV s).fun_mul (Profile.hasDerivAt_W s)).const_mul
    (4 / 3 : ℝ)).congr_deriv ?_
  simp only [u2]
  ring

/-- `u2' = u3`. -/
theorem hasDerivAt_u2 (s : ℝ) : HasDerivAt u2 (u3 s) s := by
  have hσ := Profile.hasDerivAt_sigmaV s
  have hW := Profile.hasDerivAt_W s
  refine (((hσ.const_mul (-2 : ℝ)).fun_add
    ((hσ.fun_mul ((hasDerivAt_const s (1 : ℝ)).fun_sub hσ)).fun_mul (hW.fun_pow 2))).const_mul
    (4 / 3 : ℝ)).congr_deriv ?_
  simp only [u3]
  ring

/-! ### The computer-checked integrand -/

/-- The radial integrand of the manuscript: `r⁴⁰ e^{u(s)} K₄₁(s, -u'(s), u''(s), u'''(s))`
at `s = r²/2`. -/
def Fmath (r : ℝ) : ℝ := r ^ 40 * Real.exp (uprof (r ^ 2 / 2)) *
  Kd 41 (r ^ 2 / 2) (-u1 (r ^ 2 / 2)) (u2 (r ^ 2 / 2)) (u3 (r ^ 2 / 2))

namespace Profile

/-! Values of the `C2F` operations (all by `rfl`). -/

theorem id_f (x : ℝ) : Num.C2F.id.f x = x := rfl

theorem ofInt_f (n : ℤ) (x : ℝ) : (Num.C2F.ofInt n).f x = (n : ℝ) := rfl

theorem add_f (g h : Num.C2F) (x : ℝ) : (g.add h).f x = g.f x + h.f x := rfl

theorem neg_f (g : Num.C2F) (x : ℝ) : g.neg.f x = -g.f x := rfl

theorem sub_f (g h : Num.C2F) (x : ℝ) : (g.sub h).f x = g.f x - h.f x :=
  (sub_eq_add_neg _ _).symm

theorem mul_f (g h : Num.C2F) (x : ℝ) : (g.mul h).f x = g.f x * h.f x := rfl

theorem divInt_f (g : Num.C2F) (n : ℤ) (x : ℝ) : (g.divInt n).f x = g.f x / (n : ℝ) := rfl

theorem pow_f (g : Num.C2F) : ∀ (n : ℕ) (x : ℝ), (g.pow n).f x = g.f x ^ n
  | 0, x => by show ((1 : ℤ) : ℝ) = g.f x ^ 0; simp
  | 1, x => by show g.f x = g.f x ^ 1; simp
  | _ + 2, _ => rfl

theorem exp_f (g : Num.C2F) (x : ℝ) : g.exp.f x = Real.exp (g.f x) := rfl

theorem logistic_f (g : Num.C2F) (x : ℝ) : g.logistic.f x = Num.sigma (g.f x) := rfl

theorem cbrt_f (g : Num.C2F) (h : ∀ x, 0 < g.f x) (x : ℝ) :
    (g.cbrt h).f x = g.f x ^ ((1 : ℝ) / 3) := rfl

/-- `e^u = y · y^{1/3}` with `y = e^V + 1`. -/
theorem exp_uprof (s : ℝ) :
    Real.exp (uprof s) = (Real.exp (Vfun s) + 1) * (Real.exp (Vfun s) + 1) ^ ((1 : ℝ) / 3) := by
  have hy : 0 < Real.exp (Vfun s) + 1 := by positivity
  have h1 : Real.exp (uprof s) = (Real.exp (Vfun s) + 1) ^ ((4 : ℝ) / 3) := by
    rw [Real.rpow_def_of_pos hy, uprof, add_comm (Real.exp (Vfun s)) 1]
    congr 1
    ring
  have h2 : (Real.exp (Vfun s) + 1) ^ ((4 : ℝ) / 3) =
      (Real.exp (Vfun s) + 1) * (Real.exp (Vfun s) + 1) ^ ((1 : ℝ) / 3) := by
    rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num, Real.rpow_add hy, Real.rpow_one]
  rw [h1, h2]

end Profile

/-- **The computer-checked integrand is the radial integrand of the manuscript.** -/
theorem radialC2_f_eq (r : ℝ) : Num.radialC2.f r = Fmath r := by
  have c1 : ((1 : ℤ) : ℝ) = 1 := by norm_num
  have c2 : ((2 : ℤ) : ℝ) = 2 := by norm_num
  have c3 : ((3 : ℤ) : ℝ) = 3 := by norm_num
  have c4 : ((4 : ℤ) : ℝ) = 4 := by norm_num
  have c8 : ((8 : ℤ) : ℝ) = 8 := by norm_num
  have c15 : ((15 : ℤ) : ℝ) = 15 := by norm_num
  have c24 : ((24 : ℤ) : ℝ) = 24 := by norm_num
  have c40 : ((40 : ℤ) : ℝ) = 40 := by norm_num
  have c258 : ((258 : ℤ) : ℝ) = 258 := by norm_num
  have cm2 : ((-2 : ℤ) : ℝ) = -2 := by norm_num
  have cm6 : ((-6 : ℤ) : ℝ) = -6 := by norm_num
  simp only [Num.radialC2, Profile.id_f, Profile.ofInt_f, Profile.add_f, Profile.neg_f,
    Profile.sub_f, Profile.mul_f, Profile.divInt_f, Profile.pow_f, Profile.exp_f,
    Profile.logistic_f, Profile.cbrt_f, c1, c2, c3, c4, c8, c15, c24, c40, c258, cm2, cm6]
  rw [Fmath, Profile.exp_uprof]
  simp only [Kd, u1, u2, u3, Vfun, Nat.cast_ofNat]
  generalize Num.sigma (15 - 2 * (r ^ 2 / 2) - (r ^ 2 / 2) ^ 2) = σ
  generalize Real.exp (15 - 2 * (r ^ 2 / 2) - (r ^ 2 / 2) ^ 2) = E
  generalize r ^ 2 / 2 = s
  ring

/-! ### The cut-off profile -/

namespace Profile

/-- `e₀(s) = η(s/16)`. -/
def e0 (s : ℝ) : ℝ := eta (s / 16)

/-- `e₁(s) = η'(s/16)/16`, the derivative of `e₀`. -/
def e1 (s : ℝ) : ℝ := deriv eta (s / 16) / 16

/-- `e₂(s) = η''(s/16)/16²`, the second derivative of `e₀`. -/
def e2 (s : ℝ) : ℝ := iteratedDeriv 2 eta (s / 16) / 16 ^ 2

/-- `e₃(s) = η'''(s/16)/16³`, the third derivative of `e₀`. -/
def e3 (s : ℝ) : ℝ := iteratedDeriv 3 eta (s / 16) / 16 ^ 3

theorem iteratedDeriv_two_eta : iteratedDeriv 2 eta = deriv (deriv eta) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

theorem iteratedDeriv_three_eta : iteratedDeriv 3 eta = deriv (deriv (deriv eta)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]

theorem hasDerivAt_eta (v : ℝ) : HasDerivAt eta (deriv eta v) v :=
  (Cutoff.differentiable_eta v).hasDerivAt

theorem hasDerivAt_deriv_eta (v : ℝ) : HasDerivAt (deriv eta) (iteratedDeriv 2 eta v) v := by
  rw [iteratedDeriv_two_eta]
  exact (Cutoff.differentiable_deriv_eta v).hasDerivAt

theorem hasDerivAt_iteratedDeriv_two_eta (v : ℝ) :
    HasDerivAt (iteratedDeriv 2 eta) (iteratedDeriv 3 eta v) v := by
  rw [iteratedDeriv_three_eta, iteratedDeriv_two_eta]
  exact (Cutoff.differentiable_deriv_deriv_eta v).hasDerivAt

theorem continuous_iteratedDeriv_three_eta : Continuous (iteratedDeriv 3 eta) := by
  rw [iteratedDeriv_three_eta]
  exact (contDiff_infty_iff_deriv.1
    (contDiff_infty_iff_deriv.1 Cutoff.contDiff_deriv_eta).2).2.continuous

theorem hasDerivAt_e0 (s : ℝ) : HasDerivAt e0 (e1 s) s := by
  have h := (hasDerivAt_eta (s / 16)).comp s ((hasDerivAt_id' s).div_const 16)
  refine h.congr_deriv ?_
  simp only [e1]
  ring

theorem hasDerivAt_e1 (s : ℝ) : HasDerivAt e1 (e2 s) s := by
  have h := ((hasDerivAt_deriv_eta (s / 16)).comp s ((hasDerivAt_id' s).div_const 16)).div_const
    16
  refine h.congr_deriv ?_
  simp only [e2]
  ring

theorem hasDerivAt_e2 (s : ℝ) : HasDerivAt e2 (e3 s) s := by
  have h := ((hasDerivAt_iteratedDeriv_two_eta (s / 16)).comp s
    ((hasDerivAt_id' s).div_const 16)).div_const (16 ^ 2)
  refine h.congr_deriv ?_
  simp only [e3]
  ring

end Profile

/-- First derivative of the cut-off profile: `ũ' = e₁ u + e₀ u'`. -/
def uc1 (s : ℝ) : ℝ := Profile.e1 s * uprof s + Profile.e0 s * u1 s

/-- Second derivative of the cut-off profile: `ũ'' = e₂ u + 2 e₁ u' + e₀ u''`. -/
def uc2 (s : ℝ) : ℝ := Profile.e2 s * uprof s + 2 * Profile.e1 s * u1 s + Profile.e0 s * u2 s

/-- Third derivative of the cut-off profile: `ũ''' = e₃ u + 3 e₂ u' + 3 e₁ u'' + e₀ u'''`. -/
def uc3 (s : ℝ) : ℝ := Profile.e3 s * uprof s + 3 * Profile.e2 s * u1 s +
  3 * Profile.e1 s * u2 s + Profile.e0 s * u3 s

/-- `ũ' = uc1`. -/
theorem hasDerivAt_ucut (s : ℝ) : HasDerivAt ucut (uc1 s) s :=
  (Profile.hasDerivAt_e0 s).fun_mul (hasDerivAt_uprof s)

/-- `uc1' = uc2`. -/
theorem hasDerivAt_uc1 (s : ℝ) : HasDerivAt uc1 (uc2 s) s := by
  refine (((Profile.hasDerivAt_e1 s).fun_mul (hasDerivAt_uprof s)).fun_add
    ((Profile.hasDerivAt_e0 s).fun_mul (hasDerivAt_u1 s))).congr_deriv ?_
  simp only [uc2]
  ring

/-- `uc2' = uc3`. -/
theorem hasDerivAt_uc2 (s : ℝ) : HasDerivAt uc2 (uc3 s) s := by
  refine ((((Profile.hasDerivAt_e2 s).fun_mul (hasDerivAt_uprof s)).fun_add
    (((Profile.hasDerivAt_e1 s).const_mul (2 : ℝ)).fun_mul (hasDerivAt_u1 s))).fun_add
    ((Profile.hasDerivAt_e0 s).fun_mul (hasDerivAt_u2 s))).congr_deriv ?_
  simp only [uc3]
  ring

/-! ### Agreement for `s ≤ 16` and vanishing for `s ≥ 32` -/

namespace Profile

theorem b1_of_nonpos {x : ℝ} (hx : x ≤ 0) : Cutoff.b1 x = 0 := by
  rw [Cutoff.b1, expNegInvGlue.zero_of_nonpos hx, mul_zero]

theorem b2_of_nonpos {x : ℝ} (hx : x ≤ 0) : Cutoff.b2 x = 0 := by
  rw [Cutoff.b2, expNegInvGlue.zero_of_nonpos hx, mul_zero]

theorem b3_of_nonpos {x : ℝ} (hx : x ≤ 0) : Cutoff.b3 x = 0 := by
  rw [Cutoff.b3, expNegInvGlue.zero_of_nonpos hx, mul_zero]

/-- `x · G(v) = 0` forces `x = 0`, since `G > 0`. -/
theorem eq_zero_of_mul_den {x : ℝ} (v : ℝ) (h : x * Cutoff.den v = 0) : x = 0 :=
  (mul_eq_zero.1 h).resolve_right (Cutoff.den_pos v).ne'

/-- `η' = η'' = η''' = 0` on `(-∞, 1]` (including the point `1`). -/
theorem derivs_eta_of_le_one {v : ℝ} (hv : v ≤ 1) :
    deriv eta v = 0 ∧ deriv (deriv eta) v = 0 ∧ deriv (deriv (deriv eta)) v = 0 := by
  have hb1 : Cutoff.b1 (v - 1) = 0 := b1_of_nonpos (by linarith)
  have hb2 : Cutoff.b2 (v - 1) = 0 := b2_of_nonpos (by linarith)
  have hb3 : Cutoff.b3 (v - 1) = 0 := b3_of_nonpos (by linarith)
  have he : eta v = 1 := eta_of_le_one hv
  have h1 := Cutoff.deriv_eta_identity v
  have h2 := Cutoff.deriv2_eta_identity v
  have h3 := Cutoff.deriv3_eta_identity v
  simp only [Cutoff.den1, Cutoff.den2, Cutoff.den3, hb1, hb2, hb3, he] at h1 h2 h3
  have d1 : deriv eta v = 0 := eq_zero_of_mul_den v (by linarith)
  rw [d1] at h2 h3
  have d2 : deriv (deriv eta) v = 0 := eq_zero_of_mul_den v (by linarith)
  rw [d2] at h3
  exact ⟨d1, d2, eq_zero_of_mul_den v (by linarith)⟩

/-- `η' = η'' = η''' = 0` on `[2, ∞)` (including the point `2`). -/
theorem derivs_eta_of_two_le {v : ℝ} (hv : 2 ≤ v) :
    deriv eta v = 0 ∧ deriv (deriv eta) v = 0 ∧ deriv (deriv (deriv eta)) v = 0 := by
  have hb1 : Cutoff.b1 (2 - v) = 0 := b1_of_nonpos (by linarith)
  have hb2 : Cutoff.b2 (2 - v) = 0 := b2_of_nonpos (by linarith)
  have hb3 : Cutoff.b3 (2 - v) = 0 := b3_of_nonpos (by linarith)
  have he : eta v = 0 := eta_of_two_le hv
  have h1 := Cutoff.deriv_eta_identity v
  have h2 := Cutoff.deriv2_eta_identity v
  have h3 := Cutoff.deriv3_eta_identity v
  simp only [hb1, hb2, hb3, he] at h1 h2 h3
  have d1 : deriv eta v = 0 := eq_zero_of_mul_den v (by linarith)
  rw [d1] at h2 h3
  have d2 : deriv (deriv eta) v = 0 := eq_zero_of_mul_den v (by linarith)
  rw [d2] at h3
  exact ⟨d1, d2, eq_zero_of_mul_den v (by linarith)⟩

theorem e0_of_le {s : ℝ} (hs : s ≤ 16) : e0 s = 1 :=
  eta_of_le_one (by linarith)

theorem e1_of_le {s : ℝ} (hs : s ≤ 16) : e1 s = 0 := by
  rw [e1, (derivs_eta_of_le_one (by linarith : s / 16 ≤ 1)).1, zero_div]

theorem e2_of_le {s : ℝ} (hs : s ≤ 16) : e2 s = 0 := by
  rw [e2, iteratedDeriv_two_eta, (derivs_eta_of_le_one (by linarith : s / 16 ≤ 1)).2.1,
    zero_div]

theorem e3_of_le {s : ℝ} (hs : s ≤ 16) : e3 s = 0 := by
  rw [e3, iteratedDeriv_three_eta, (derivs_eta_of_le_one (by linarith : s / 16 ≤ 1)).2.2,
    zero_div]

theorem e0_of_ge {s : ℝ} (hs : 32 ≤ s) : e0 s = 0 :=
  eta_of_two_le (by linarith)

theorem e1_of_ge {s : ℝ} (hs : 32 ≤ s) : e1 s = 0 := by
  rw [e1, (derivs_eta_of_two_le (by linarith : 2 ≤ s / 16)).1, zero_div]

theorem e2_of_ge {s : ℝ} (hs : 32 ≤ s) : e2 s = 0 := by
  rw [e2, iteratedDeriv_two_eta, (derivs_eta_of_two_le (by linarith : 2 ≤ s / 16)).2.1,
    zero_div]

theorem e3_of_ge {s : ℝ} (hs : 32 ≤ s) : e3 s = 0 := by
  rw [e3, iteratedDeriv_three_eta, (derivs_eta_of_two_le (by linarith : 2 ≤ s / 16)).2.2,
    zero_div]

end Profile

/-- For `s ≤ 16` the cut-off profile is the profile. -/
theorem ucut_eq_uprof {s : ℝ} (hs : s ≤ 16) : ucut s = uprof s := by
  rw [ucut, eta_of_le_one (by linarith : s / 16 ≤ 1), one_mul]

/-- For `s ≤ 16`, `ũ' = u'`. -/
theorem uc1_eq_u1 {s : ℝ} (hs : s ≤ 16) : uc1 s = u1 s := by
  rw [uc1, Profile.e1_of_le hs, Profile.e0_of_le hs]
  ring

/-- For `s ≤ 16`, `ũ'' = u''`. -/
theorem uc2_eq_u2 {s : ℝ} (hs : s ≤ 16) : uc2 s = u2 s := by
  rw [uc2, Profile.e2_of_le hs, Profile.e1_of_le hs, Profile.e0_of_le hs]
  ring

/-- For `s ≤ 16`, `ũ''' = u'''`. -/
theorem uc3_eq_u3 {s : ℝ} (hs : s ≤ 16) : uc3 s = u3 s := by
  rw [uc3, Profile.e3_of_le hs, Profile.e2_of_le hs, Profile.e1_of_le hs, Profile.e0_of_le hs]
  ring

/-- For `s ≥ 32` the cut-off profile vanishes. -/
theorem ucut_eq_zero {s : ℝ} (hs : 32 ≤ s) : ucut s = 0 := by
  rw [ucut, eta_of_two_le (by linarith : 2 ≤ s / 16), zero_mul]

/-- For `s ≥ 32`, `ũ' = 0`. -/
theorem uc1_eq_zero {s : ℝ} (hs : 32 ≤ s) : uc1 s = 0 := by
  rw [uc1, Profile.e1_of_ge hs, Profile.e0_of_ge hs]
  ring

/-- For `s ≥ 32`, `ũ'' = 0`. -/
theorem uc2_eq_zero {s : ℝ} (hs : 32 ≤ s) : uc2 s = 0 := by
  rw [uc2, Profile.e2_of_ge hs, Profile.e1_of_ge hs, Profile.e0_of_ge hs]
  ring

/-- For `s ≥ 32`, `ũ''' = 0`. -/
theorem uc3_eq_zero {s : ℝ} (hs : 32 ≤ s) : uc3 s = 0 := by
  rw [uc3, Profile.e3_of_ge hs, Profile.e2_of_ge hs, Profile.e1_of_ge hs, Profile.e0_of_ge hs]
  ring

/-! ### The cut integrand -/

/-- The radial integrand built from the cut-off profile `ũ`. -/
def Fcut (r : ℝ) : ℝ := r ^ 40 * Real.exp (ucut (r ^ 2 / 2)) *
  Kd 41 (r ^ 2 / 2) (-uc1 (r ^ 2 / 2)) (uc2 (r ^ 2 / 2)) (uc3 (r ^ 2 / 2))

/-- Inside `r² ≤ 32` the cut integrand is the integrand of the manuscript. -/
theorem Fcut_eq_Fmath {r : ℝ} (hr : r ^ 2 ≤ 32) : Fcut r = Fmath r := by
  have hs : r ^ 2 / 2 ≤ 16 := by linarith
  rw [Fcut, Fmath, ucut_eq_uprof hs, uc1_eq_u1 hs, uc2_eq_u2 hs, uc3_eq_u3 hs]

/-- Outside `r² < 64` the cut integrand vanishes. -/
theorem Fcut_eq_zero {r : ℝ} (hr : 64 ≤ r ^ 2) : Fcut r = 0 := by
  have hs : 32 ≤ r ^ 2 / 2 := by linarith
  rw [Fcut, ucut_eq_zero hs, uc1_eq_zero hs, uc2_eq_zero hs, uc3_eq_zero hs]
  simp only [Kd]
  ring

/-! ### Tail bounds -/

namespace Profile

theorem bnd_add {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x + y| ≤ X + Y :=
  (abs_add_le x y).trans (add_le_add hx hy)

theorem bnd_sub {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x - y| ≤ X + Y := by
  rw [sub_eq_add_neg]
  exact bnd_add hx (by rwa [abs_neg])

theorem bnd_mul {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y :=
  Cutoff.abs_mul_le_of_le hx hy

theorem bnd_pow {x X : ℝ} (hx : |x| ≤ X) (n : ℕ) : |x ^ n| ≤ X ^ n := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) hx n

theorem bnd_const {c : ℝ} (hc : 0 ≤ c) : |c| ≤ c := le_of_eq (abs_of_nonneg hc)

theorem bnd_neg_const {c : ℝ} (hc : 0 ≤ c) : |-c| ≤ c := by
  rw [abs_neg]
  exact bnd_const hc

/-- `|K₄₁(s, a, B, C)| ≤ 500 s³ M²` if `|a|, |B|, |C| ≤ M ≤ 1` and `s ≥ 1`. -/
theorem abs_Kd_le {s a B C M : ℝ} (hs : 1 ≤ s) (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (ha : |a| ≤ M) (hB : |B| ≤ M) (hC : |C| ≤ M) :
    |Kd 41 s a B C| ≤ 500 * s ^ 3 * M ^ 2 := by
  have hs0 : 0 ≤ s := by linarith
  have hsa : |s| ≤ s := bnd_const hs0
  have h41a : |((41 : ℕ) : ℝ) + 2| ≤ 43 := by
    rw [abs_of_nonneg (by positivity)]
    norm_num
  have h41b : |((41 : ℕ) : ℝ) - 1| ≤ 40 := by
    rw [abs_of_nonneg (by norm_num)]
    norm_num
  have hK := bnd_add (bnd_add (bnd_add
    (bnd_mul (bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 8)) (bnd_pow hsa 3)) (bnd_pow hC 2))
    (bnd_mul (bnd_mul (bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 24)) (bnd_pow hsa 2)) hB) hC))
    (bnd_mul (bnd_mul (bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 6)) h41a) hsa) (bnd_pow hB 2)))
    (bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 2))
      (bnd_add (bnd_mul h41b (bnd_pow ha 3))
        (bnd_pow (bnd_sub ha (bnd_mul (bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 2)) hsa) hB))
          3)))
  refine hK.trans ?_
  have hs2 : s ^ 2 ≤ s ^ 3 := pow_le_pow_right₀ hs (by norm_num)
  have hs1 : s ≤ s ^ 3 := le_self_pow₀ hs (by norm_num)
  have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hM32 : M ^ 3 ≤ M ^ 2 := pow_le_pow_of_le_one hM0 hM1 (by norm_num)
  have p1 : s ^ 2 * M ^ 2 ≤ s ^ 3 * M ^ 2 := mul_le_mul_of_nonneg_right hs2 hM2
  have p2 : s * M ^ 2 ≤ s ^ 3 * M ^ 2 := mul_le_mul_of_nonneg_right hs1 hM2
  have p3 : M ^ 2 ≤ s ^ 3 * M ^ 2 := le_mul_of_one_le_left hM2 hs3
  have hlin : M + 2 * s * M ≤ 3 * s * M := by
    linarith [mul_nonneg hM0 (sub_nonneg.2 hs)]
  have p4 : (M + 2 * s * M) ^ 3 ≤ (3 * s * M) ^ 3 :=
    pow_le_pow_left₀ (add_nonneg hM0 (mul_nonneg (mul_nonneg (by norm_num) hs0) hM0)) hlin 3
  have p5 : s ^ 3 * M ^ 3 ≤ s ^ 3 * M ^ 2 :=
    mul_le_mul_of_nonneg_left hM32 (pow_nonneg hs0 3)
  have p6 : 0 ≤ s ^ 3 * M ^ 2 := mul_nonneg (pow_nonneg hs0 3) hM2
  linarith [p1, p2, p3, p4, p5, p6, hM32]

/-- `σ(t) ≤ eᵗ`. -/
theorem sigma_le_exp (t : ℝ) : Num.sigma t ≤ Real.exp t := by
  have h := Real.exp_pos t
  rw [Num.sigma, div_le_iff₀ (by positivity)]
  nlinarith

theorem abs_sigma_le (t : ℝ) : |Num.sigma t| ≤ Real.exp t := by
  rw [abs_of_pos (Num.sigma_pos t)]
  exact sigma_le_exp t

theorem abs_one_sub_sigma_le (t : ℝ) : |1 - Num.sigma t| ≤ 1 := by
  have := Num.sigma_pos t
  have := Num.sigma_lt_one t
  rw [abs_le]
  constructor <;> linarith

theorem abs_one_sub_two_sigma_le (t : ℝ) : |1 - 2 * Num.sigma t| ≤ 1 := by
  have := Num.sigma_pos t
  have := Num.sigma_lt_one t
  rw [abs_le]
  constructor <;> linarith

theorem abs_W_le {s : ℝ} (hs : 2 ≤ s) : |-2 - 2 * s| ≤ 3 * s := by
  rw [abs_le]
  constructor <;> linarith

/-- Elementary consequences of `s ≥ 16` used in the tail bounds, with `τ = e^{V(s)}`. -/
theorem tail_facts {s : ℝ} (hs : 16 ≤ s) :
    0 ≤ s ^ 3 * Real.exp (Vfun s) ∧ Real.exp (Vfun s) ≤ s ^ 3 * Real.exp (Vfun s) ∧
      s * Real.exp (Vfun s) ≤ s ^ 3 * Real.exp (Vfun s) ∧
      s ^ 2 * Real.exp (Vfun s) ≤ s ^ 3 * Real.exp (Vfun s) := by
  have hτ := (Real.exp_pos (Vfun s)).le
  have hs1 : (1 : ℝ) ≤ s := by linarith
  exact ⟨mul_nonneg (pow_nonneg (by linarith) 3) hτ, le_mul_of_one_le_left hτ (one_le_pow₀ hs1),
    mul_le_mul_of_nonneg_right (le_self_pow₀ hs1 (by norm_num)) hτ,
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs1 (by norm_num)) hτ⟩

/-- Weakening `100 s³ τ` to `10⁶ s³ τ`. -/
theorem bound_mono {s x : ℝ} (hs : 16 ≤ s) (hx : |x| ≤ 100 * s ^ 3 * Real.exp (Vfun s)) :
    |x| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, -, -, -⟩ := tail_facts hs
  linarith

theorem abs_uprof_le {s : ℝ} (hs : 16 ≤ s) : |uprof s| ≤ 100 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, f1, -, -⟩ := tail_facts hs
  have hτ := Real.exp_pos (Vfun s)
  have hlog0 : 0 ≤ Real.log (1 + Real.exp (Vfun s)) := Real.log_nonneg (by linarith)
  have hlog1 : Real.log (1 + Real.exp (Vfun s)) ≤ Real.exp (Vfun s) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + Real.exp (Vfun s))
    linarith
  rw [uprof, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) hlog0)]
  linarith

theorem abs_u1_le {s : ℝ} (hs : 16 ≤ s) : |u1 s| ≤ 100 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, -, f2, -⟩ := tail_facts hs
  have h := bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 4 / 3))
    (bnd_mul (abs_sigma_le (Vfun s)) (abs_W_le (by linarith : (2 : ℝ) ≤ s)))
  refine h.trans ?_
  linarith

theorem abs_u2_le {s : ℝ} (hs : 16 ≤ s) : |u2 s| ≤ 100 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, f1, -, f3⟩ := tail_facts hs
  have h := bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 4 / 3))
    (bnd_add (bnd_mul (bnd_neg_const (by norm_num : (0 : ℝ) ≤ 2)) (abs_sigma_le (Vfun s)))
      (bnd_mul (bnd_mul (abs_sigma_le (Vfun s)) (abs_one_sub_sigma_le (Vfun s)))
        (bnd_pow (abs_W_le (by linarith : (2 : ℝ) ≤ s)) 2)))
  refine h.trans ?_
  linarith

theorem abs_u3_le {s : ℝ} (hs : 16 ≤ s) : |u3 s| ≤ 100 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, -, f2, -⟩ := tail_facts hs
  have hW := abs_W_le (by linarith : (2 : ℝ) ≤ s)
  have h := bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 4 / 3))
    (bnd_add
      (bnd_mul (bnd_mul (bnd_mul (bnd_neg_const (by norm_num : (0 : ℝ) ≤ 6))
        (abs_sigma_le (Vfun s))) (abs_one_sub_sigma_le (Vfun s))) hW)
      (bnd_mul (bnd_mul (bnd_mul (abs_sigma_le (Vfun s)) (abs_one_sub_sigma_le (Vfun s)))
        (abs_one_sub_two_sigma_le (Vfun s))) (bnd_pow hW 3)))
  refine h.trans ?_
  linarith

theorem abs_e0_le (s : ℝ) : |e0 s| ≤ 1000 :=
  (abs_eta_le_one _).trans (by norm_num)

theorem abs_e1_le (s : ℝ) : |e1 s| ≤ 1000 := by
  have := abs_deriv_eta_le (s / 16)
  rw [e1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
  linarith

theorem abs_e2_le (s : ℝ) : |e2 s| ≤ 1000 := by
  have := abs_iteratedDeriv_two_eta_le (s / 16)
  rw [e2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16 ^ 2),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 16 ^ 2)]
  linarith

theorem abs_e3_le (s : ℝ) : |e3 s| ≤ 1000 := by
  have := abs_iteratedDeriv_three_eta_le (s / 16)
  rw [e3, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16 ^ 3),
    div_le_iff₀ (by norm_num : (0 : ℝ) < 16 ^ 3)]
  linarith

theorem abs_ucut_le {s : ℝ} (hs : 16 ≤ s) :
    |ucut s| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, -, -, -⟩ := tail_facts hs
  refine (bnd_mul (abs_e0_le s) (abs_uprof_le hs)).trans ?_
  linarith

theorem abs_uc1_le {s : ℝ} (hs : 16 ≤ s) :
    |uc1 s| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, -, -, -⟩ := tail_facts hs
  refine (bnd_add (bnd_mul (abs_e1_le s) (abs_uprof_le hs))
    (bnd_mul (abs_e0_le s) (abs_u1_le hs))).trans ?_
  linarith

theorem abs_uc2_le {s : ℝ} (hs : 16 ≤ s) :
    |uc2 s| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, -, -, -⟩ := tail_facts hs
  refine (bnd_add (bnd_add (bnd_mul (abs_e2_le s) (abs_uprof_le hs))
    (bnd_mul (bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 2)) (abs_e1_le s)) (abs_u1_le hs)))
    (bnd_mul (abs_e0_le s) (abs_u2_le hs))).trans ?_
  linarith

theorem abs_uc3_le {s : ℝ} (hs : 16 ≤ s) :
    |uc3 s| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s) := by
  obtain ⟨f0, -, -, -⟩ := tail_facts hs
  refine (bnd_add (bnd_add (bnd_add (bnd_mul (abs_e3_le s) (abs_uprof_le hs))
    (bnd_mul (bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 3)) (abs_e2_le s)) (abs_u1_le hs)))
    (bnd_mul (bnd_mul (bnd_const (by norm_num : (0 : ℝ) ≤ 3)) (abs_e1_le s)) (abs_u2_le hs)))
    (bnd_mul (abs_e0_le s) (abs_u3_le hs))).trans ?_
  linarith

/-- Gaussian decay: `s³⁰ e^{V(s)} ≤ 15!` for `s ≥ 16`. -/
theorem pow30_mul_exp_Vfun_le {s : ℝ} (hs : 16 ≤ s) :
    s ^ 30 * Real.exp (Vfun s) ≤ 1307674368000 := by
  have hfac := Real.pow_div_factorial_le_exp (s ^ 2) (sq_nonneg s) 15
  have hf : ((Nat.factorial 15 : ℕ) : ℝ) = 1307674368000 := by norm_num [Nat.factorial]
  rw [hf, div_le_iff₀ (by norm_num : (0 : ℝ) < 1307674368000)] at hfac
  have hV : Vfun s + s ^ 2 ≤ 0 := by
    unfold Vfun
    linarith
  have hprod : Real.exp (Vfun s) * Real.exp (s ^ 2) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.2 hV
  have hτ := Real.exp_pos (Vfun s)
  calc s ^ 30 * Real.exp (Vfun s) = (s ^ 2) ^ 15 * Real.exp (Vfun s) := by ring
    _ ≤ Real.exp (s ^ 2) * 1307674368000 * Real.exp (Vfun s) := by gcongr
    _ = 1307674368000 * (Real.exp (Vfun s) * Real.exp (s ^ 2)) := by ring
    _ ≤ 1307674368000 * 1 := by gcongr
    _ = 1307674368000 := by ring

/-- `e^{V(s)} ≤ 2⁻²⁰⁰` for `s ≥ 16` (in fact `V(s) ≤ -273` there). -/
theorem exp_Vfun_le {s : ℝ} (hs : 16 ≤ s) : Real.exp (Vfun s) ≤ (2 ^ 200)⁻¹ := by
  have hV : Vfun s ≤ -200 := by
    unfold Vfun
    nlinarith
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h200 : (2 : ℝ) ^ 200 ≤ Real.exp 200 :=
    calc (2 : ℝ) ^ 200 ≤ Real.exp 1 ^ 200 := pow_le_pow_left₀ (by norm_num) h2 200
      _ = Real.exp 200 := by rw [← Real.exp_nat_mul]; norm_num
  calc Real.exp (Vfun s) ≤ Real.exp (-200) := Real.exp_le_exp.2 hV
    _ = (Real.exp 200)⁻¹ := by rw [Real.exp_neg]
    _ ≤ (2 ^ 200)⁻¹ := inv_anti₀ (by positivity) h200

/-- The common tail estimate for `Fmath` and `Fcut`. -/
theorem abs_tail_le {r s U0 A B C : ℝ} (hr : r ^ 2 / 2 = s) (hs : 16 ≤ s)
    (hU : |U0| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s))
    (hA : |A| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s))
    (hB : |B| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s))
    (hC : |C| ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s)) :
    |r ^ 40 * Real.exp U0 * Kd 41 s (-A) B C| ≤ 1 := by
  have hs0 : 0 ≤ s := by linarith
  have hτ0 := Real.exp_pos (Vfun s)
  have h30 := pow30_mul_exp_Vfun_le hs
  have hτs := exp_Vfun_le hs
  have hX : 0 ≤ s ^ 3 * Real.exp (Vfun s) := mul_nonneg (pow_nonneg hs0 3) hτ0.le
  have hM0 : 0 ≤ 10 ^ 6 * s ^ 3 * Real.exp (Vfun s) := by linarith
  have hM1 : 10 ^ 6 * s ^ 3 * Real.exp (Vfun s) ≤ 1 := by
    have h27 : (16 : ℝ) ^ 27 ≤ s ^ 27 := pow_le_pow_left₀ (by norm_num) hs 27
    have h := mul_le_mul_of_nonneg_left h27 hX
    linarith
  have hK := abs_Kd_le (s := s) (a := -A) (by linarith) hM0 hM1 (by rwa [abs_neg]) hB hC
  have hE : Real.exp U0 ≤ 3 := by
    have h1 : U0 ≤ 1 := (le_abs_self U0).trans (hU.trans hM1)
    have h2 := Real.exp_le_exp.2 h1
    have h3 := Real.exp_one_lt_d9
    linarith
  have hr40 : r ^ 40 = 2 ^ 20 * s ^ 20 := by
    rw [← hr]
    ring
  rw [hr40, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ 20 * s ^ 20),
    abs_of_pos (Real.exp_pos U0)]
  calc 2 ^ 20 * s ^ 20 * Real.exp U0 * |Kd 41 s (-A) B C|
      ≤ 2 ^ 20 * s ^ 20 * 3 * (500 * s ^ 3 * (10 ^ 6 * s ^ 3 * Real.exp (Vfun s)) ^ 2) := by
        gcongr
    _ = 1500 * 2 ^ 20 * 10 ^ 12 * (s ^ 29 * Real.exp (Vfun s) ^ 2) := by ring
    _ ≤ 1500 * 2 ^ 20 * 10 ^ 12 * (s ^ 30 * Real.exp (Vfun s) * Real.exp (Vfun s)) := by
        have h29 : s ^ 29 ≤ s ^ 30 := pow_le_pow_right₀ (by linarith) (by norm_num)
        have h := mul_le_mul_of_nonneg_right h29 (mul_nonneg hτ0.le hτ0.le)
        linarith
    _ ≤ 1500 * 2 ^ 20 * 10 ^ 12 * (1307674368000 * (2 ^ 200)⁻¹) := by gcongr
    _ ≤ 1 := by norm_num

end Profile

-- The hypothesis `h2 : r ≤ 8` is not needed: the bound holds for every `r` with `32 ≤ r²`.
set_option linter.unusedVariables false in
/-- The cut integrand is tiny on the transition region `32 ≤ r²` (no upper bound on `r` is
actually needed). -/
theorem abs_Fcut_le_one {r : ℝ} (h1 : 32 ≤ r ^ 2) (h2 : r ≤ 8) : |Fcut r| ≤ 1 := by
  have hs : 16 ≤ r ^ 2 / 2 := by linarith
  exact Profile.abs_tail_le (r := r) rfl hs (Profile.abs_ucut_le hs) (Profile.abs_uc1_le hs)
    (Profile.abs_uc2_le hs) (Profile.abs_uc3_le hs)

-- The hypothesis `h2 : r ≤ 8` is not needed: the bound holds for every `r` with `32 ≤ r²`.
set_option linter.unusedVariables false in
/-- The integrand of the manuscript is tiny on the transition region `32 ≤ r²` (no upper bound
on `r` is actually needed). -/
theorem abs_Fmath_le_one {r : ℝ} (h1 : 32 ≤ r ^ 2) (h2 : r ≤ 8) : |Fmath r| ≤ 1 := by
  have hs : 16 ≤ r ^ 2 / 2 := by linarith
  exact Profile.abs_tail_le (r := r) rfl hs (Profile.bound_mono hs (Profile.abs_uprof_le hs))
    (Profile.bound_mono hs (Profile.abs_u1_le hs)) (Profile.bound_mono hs (Profile.abs_u2_le hs))
    (Profile.bound_mono hs (Profile.abs_u3_le hs))

/-! ### Continuity and the cut-off error of the integral -/

namespace Profile

theorem continuous_of_forall_hasDerivAt {f f' : ℝ → ℝ} (h : ∀ x, HasDerivAt f (f' x) x) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt

theorem continuous_u3 : Continuous u3 := by
  have hσ : Continuous Num.sigma := continuous_of_forall_hasDerivAt Num.C2F.hasDerivAt_sigma
  have hV : Continuous Vfun := continuous_of_forall_hasDerivAt hasDerivAt_Vfun
  show Continuous fun s => u3 s
  simp only [u3]
  fun_prop

theorem continuous_uc3 : Continuous uc3 := by
  have he0 : Continuous e0 := continuous_of_forall_hasDerivAt hasDerivAt_e0
  have he1 : Continuous e1 := continuous_of_forall_hasDerivAt hasDerivAt_e1
  have he2 : Continuous e2 := continuous_of_forall_hasDerivAt hasDerivAt_e2
  have he3 : Continuous e3 :=
    (continuous_iteratedDeriv_three_eta.comp (continuous_id.div_const 16)).div_const _
  have hu : Continuous uprof := continuous_of_forall_hasDerivAt hasDerivAt_uprof
  have hu1 : Continuous u1 := continuous_of_forall_hasDerivAt hasDerivAt_u1
  have hu2 : Continuous u2 := continuous_of_forall_hasDerivAt hasDerivAt_u2
  have hu3 : Continuous u3 := continuous_u3
  show Continuous fun s => uc3 s
  simp only [uc3]
  fun_prop

theorem continuous_Fcut : Continuous Fcut := by
  have hu : Continuous ucut := continuous_of_forall_hasDerivAt hasDerivAt_ucut
  have h1 : Continuous uc1 := continuous_of_forall_hasDerivAt hasDerivAt_uc1
  have h2 : Continuous uc2 := continuous_of_forall_hasDerivAt hasDerivAt_uc2
  have h3 : Continuous uc3 := continuous_uc3
  show Continuous fun r => Fcut r
  simp only [Fcut, Kd]
  fun_prop

theorem continuous_Fmath : Continuous Fmath := by
  have h : Fmath = Num.radialC2.f := funext fun r => (radialC2_f_eq r).symm
  rw [h]
  exact continuous_of_forall_hasDerivAt Num.radialC2.hf

end Profile

/-- **Cut-off error.** Replacing `u` by the cut-off profile `ũ` changes the radial integral
over `[0, 8]` by at most `16`: the integrands agree for `r² ≤ 32` and both are bounded by `1`
in absolute value on `[√32, 8]`. -/
theorem integral_Fcut_le :
    (∫ r in (0 : ℝ)..8, Fcut r) ≤ (∫ r in (0 : ℝ)..8, Fmath r) + 16 := by
  have hFm := Profile.continuous_Fmath
  have hFc := Profile.continuous_Fcut
  have hle : ∀ r ∈ Set.Icc (0 : ℝ) 8, Fcut r ≤ Fmath r + 2 := by
    intro r hr
    rcases le_or_gt (r ^ 2) 32 with h | h
    · rw [Fcut_eq_Fmath h]
      linarith
    · have a := abs_le.1 (abs_Fcut_le_one h.le hr.2)
      have b := abs_le.1 (abs_Fmath_le_one h.le hr.2)
      linarith [a.2, b.1]
  have hg : IntervalIntegrable (fun r => Fmath r + 2) volume 0 8 :=
    (hFm.add continuous_const).intervalIntegrable 0 8
  have hmono : (∫ r in (0 : ℝ)..8, Fcut r) ≤ ∫ r in (0 : ℝ)..8, (Fmath r + 2) :=
    intervalIntegral.integral_mono_on (by norm_num) (hFc.intervalIntegrable 0 8) hg hle
  have hsplit : (∫ r in (0 : ℝ)..8, (Fmath r + 2)) = (∫ r in (0 : ℝ)..8, Fmath r) + 16 := by
    rw [intervalIntegral.integral_add (hFm.intervalIntegrable 0 8) intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
  linarith

end Fisher41
