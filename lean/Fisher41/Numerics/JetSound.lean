/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Fisher41.Numerics.ExpSound

/-!
# Soundness of the order-two jets and of the radial evaluator

`C2F` bundles a real function with explicit first and second derivatives valid at every
point.  `JetOn J g C` says that on the set `C` the three components of the jet `J`
enclose `g`, `g'` and `g''/2`.  Each jet operation of `Fisher41.Numerics.Compute` is
sound for the corresponding operation on `C2F`, and `radial?_sound` composes them:
the computed jet of the radial integrand encloses the actual function `radialC2`.
-/

namespace Fisher41.Num

open Real

noncomputable section

/-- A real function with explicit first and second derivatives, valid everywhere. -/
structure C2F where
  f : ℝ → ℝ
  f1 : ℝ → ℝ
  f2 : ℝ → ℝ
  hf : ∀ x, HasDerivAt f (f1 x) x
  hf1 : ∀ x, HasDerivAt f1 (f2 x) x

namespace C2F

/-- The identity function. -/
def id : C2F where
  f := fun x => x
  f1 := fun _ => 1
  f2 := fun _ => 0
  hf := fun x => hasDerivAt_id' x
  hf1 := fun x => hasDerivAt_const x 1

/-- A constant function. -/
def const (c : ℝ) : C2F where
  f := fun _ => c
  f1 := fun _ => 0
  f2 := fun _ => 0
  hf := fun x => hasDerivAt_const x c
  hf1 := fun x => hasDerivAt_const x 0

/-- Integer constants, cast exactly as in `JetOn.ofInt`. -/
def ofInt (n : ℤ) : C2F := const (n : ℝ)

def add (g h : C2F) : C2F where
  f := fun x => g.f x + h.f x
  f1 := fun x => g.f1 x + h.f1 x
  f2 := fun x => g.f2 x + h.f2 x
  hf := fun x => (g.hf x).fun_add (h.hf x)
  hf1 := fun x => (g.hf1 x).fun_add (h.hf1 x)

def neg (g : C2F) : C2F where
  f := fun x => -g.f x
  f1 := fun x => -g.f1 x
  f2 := fun x => -g.f2 x
  hf := fun x => (g.hf x).fun_neg
  hf1 := fun x => (g.hf1 x).fun_neg

def sub (g h : C2F) : C2F := add g (neg h)

def mul (g h : C2F) : C2F where
  f := fun x => g.f x * h.f x
  f1 := fun x => g.f1 x * h.f x + g.f x * h.f1 x
  f2 := fun x => g.f2 x * h.f x + g.f1 x * h.f1 x + (g.f1 x * h.f1 x + g.f x * h.f2 x)
  hf := fun x => (g.hf x).fun_mul (h.hf x)
  hf1 := fun x => ((g.hf1 x).fun_mul (h.hf x)).fun_add ((g.hf x).fun_mul (h.hf1 x))

def divInt (g : C2F) (n : ℤ) : C2F where
  f := fun x => g.f x / n
  f1 := fun x => g.f1 x / n
  f2 := fun x => g.f2 x / n
  hf := fun x => (g.hf x).div_const _
  hf1 := fun x => (g.hf1 x).div_const _

/-- Powers, by the same case split as `Jet.pow`. -/
def pow (g : C2F) : ℕ → C2F
  | 0 => ofInt 1
  | 1 => g
  | n + 2 =>
    { f := fun x => g.f x ^ (n + 2)
      f1 := fun x => ((n + 2 : ℕ) : ℝ) * g.f x ^ (n + 2 - 1) * g.f1 x
      f2 := fun x => ((n + 2 : ℕ) : ℝ) *
        (((n + 2 - 1 : ℕ) : ℝ) * g.f x ^ (n + 2 - 1 - 1) * g.f1 x * g.f1 x +
          g.f x ^ (n + 2 - 1) * g.f2 x)
      hf := fun x => (g.hf x).fun_pow (n + 2)
      hf1 := fun x => by
        have h := (((g.hf x).fun_pow (n + 2 - 1)).fun_mul (g.hf1 x)).const_mul
          ((n + 2 : ℕ) : ℝ)
        convert h using 1
        funext y; ring }

/-- The logistic function `σ t = eᵗ/(1+eᵗ)` has derivative `σ(1-σ)`. -/
theorem hasDerivAt_sigma (t : ℝ) : HasDerivAt sigma (sigma t * (1 - sigma t)) t := by
  have h1 : HasDerivAt (fun t => Real.exp t) (Real.exp t) t := Real.hasDerivAt_exp t
  have h2 : HasDerivAt (fun t => 1 + Real.exp t) (0 + Real.exp t) t :=
    (hasDerivAt_const t (1 : ℝ)).fun_add h1
  have hne : (1 + Real.exp t) ≠ 0 := by positivity
  have := h1.fun_div h2 hne
  have hs : sigma = fun t => Real.exp t / (1 + Real.exp t) := rfl
  rw [hs]
  convert this using 1
  field_simp
  ring

def exp (g : C2F) : C2F where
  f := fun x => Real.exp (g.f x)
  f1 := fun x => Real.exp (g.f x) * g.f1 x
  f2 := fun x => Real.exp (g.f x) * g.f1 x * g.f1 x + Real.exp (g.f x) * g.f2 x
  hf := fun x => (g.hf x).exp
  hf1 := fun x => ((g.hf x).exp).fun_mul (g.hf1 x)

def logistic (g : C2F) : C2F where
  f := fun x => sigma (g.f x)
  f1 := fun x => sigma (g.f x) * (1 - sigma (g.f x)) * g.f1 x
  f2 := fun x => (sigma (g.f x) * (1 - sigma (g.f x)) * g.f1 x * (1 - sigma (g.f x)) +
      sigma (g.f x) * (0 - sigma (g.f x) * (1 - sigma (g.f x)) * g.f1 x)) * g.f1 x +
    sigma (g.f x) * (1 - sigma (g.f x)) * g.f2 x
  hf := fun x => (hasDerivAt_sigma (g.f x)).comp x (g.hf x)
  hf1 := fun x => by
    have hs : HasDerivAt (fun y => sigma (g.f y))
        (sigma (g.f x) * (1 - sigma (g.f x)) * g.f1 x) x :=
      (hasDerivAt_sigma (g.f x)).comp x (g.hf x)
    exact (hs.fun_mul ((hasDerivAt_const x (1 : ℝ)).fun_sub hs)).fun_mul (g.hf1 x)

/-- Cube root of an everywhere-positive function. -/
def cbrt (g : C2F) (hpos : ∀ x, 0 < g.f x) : C2F where
  f := fun x => g.f x ^ ((1 : ℝ) / 3)
  f1 := fun x => g.f1 x / (3 * (g.f x ^ ((1 : ℝ) / 3)) ^ 2)
  f2 := fun x => (g.f2 x * (3 * (g.f x ^ ((1 : ℝ) / 3)) ^ 2) -
      g.f1 x * (3 * (((2 : ℕ) : ℝ) * (g.f x ^ ((1 : ℝ) / 3)) ^ (2 - 1) *
        (g.f1 x / (3 * (g.f x ^ ((1 : ℝ) / 3)) ^ 2))))) /
    (3 * (g.f x ^ ((1 : ℝ) / 3)) ^ 2) ^ 2
  hf := fun x => by
    have h := (g.hf x).rpow_const (p := (1 : ℝ) / 3) (Or.inl (hpos x).ne')
    convert h using 1
    have hg := hpos x
    have hc : (g.f x ^ ((1 : ℝ) / 3)) ^ 2 = g.f x ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le]; norm_num
    have hm : g.f x ^ ((1 : ℝ) / 3 - 1) = (g.f x ^ ((2 : ℝ) / 3))⁻¹ := by
      rw [← Real.rpow_neg hg.le]; norm_num
    rw [hc, hm]
    field_simp
  hf1 := fun x => by
    have hg := hpos x
    have hc' : HasDerivAt (fun y => g.f y ^ ((1 : ℝ) / 3))
        (g.f1 x / (3 * (g.f x ^ ((1 : ℝ) / 3)) ^ 2)) x := by
      have h := (g.hf x).rpow_const (p := (1 : ℝ) / 3) (Or.inl hg.ne')
      convert h using 1
      have hc : (g.f x ^ ((1 : ℝ) / 3)) ^ 2 = g.f x ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le]; norm_num
      have hm : g.f x ^ ((1 : ℝ) / 3 - 1) = (g.f x ^ ((2 : ℝ) / 3))⁻¹ := by
        rw [← Real.rpow_neg hg.le]; norm_num
      rw [hc, hm]
      field_simp
    have hden := (hc'.fun_pow 2).const_mul (3 : ℝ)
    have hne : 3 * (g.f x ^ ((1 : ℝ) / 3)) ^ 2 ≠ 0 := by
      have := Real.rpow_pos_of_pos hg ((1 : ℝ) / 3)
      positivity
    exact (g.hf1 x).fun_div hden hne

end C2F

/-- The jet `J` encloses `g`, `g'`, `g''/2` at every point of `C`. -/
def JetOn (J : Jet) (g : C2F) (C : Set ℝ) : Prop :=
  ∀ x ∈ C, J.v.mem (g.f x) ∧ J.d.mem (g.f1 x) ∧ J.e.mem (g.f2 x / 2)

namespace JetOn

variable {J K : Jet} {g h : C2F} {C : Set ℝ}

theorem ofInt (n : ℤ) : JetOn (Jet.ofInt n) (C2F.ofInt n) C := by
  intro x _
  refine ⟨IV.rat_one_mem n, ?_, ?_⟩
  · show (IV.rat 0).mem 0
    simpa using IV.rat_one_mem 0
  · show (IV.rat 0).mem (0 / 2)
    simpa using IV.rat_one_mem 0

theorem add (hJ : JetOn J g C) (hK : JetOn K h C) : JetOn (Jet.add J K) (C2F.add g h) C := by
  intro x hx
  obtain ⟨a1, a2, a3⟩ := hJ x hx
  obtain ⟨b1, b2, b3⟩ := hK x hx
  refine ⟨IV.add_mem a1 b1, IV.add_mem a2 b2, ?_⟩
  rw [show (C2F.add g h).f2 x / 2 = g.f2 x / 2 + h.f2 x / 2 by simp only [C2F.add]; ring]
  exact IV.add_mem a3 b3

theorem neg (hJ : JetOn J g C) : JetOn (Jet.neg J) (C2F.neg g) C := by
  intro x hx
  obtain ⟨a1, a2, a3⟩ := hJ x hx
  refine ⟨IV.neg_mem a1, IV.neg_mem a2, ?_⟩
  rw [show (C2F.neg g).f2 x / 2 = -(g.f2 x / 2) by simp only [C2F.neg]; ring]
  exact IV.neg_mem a3

theorem sub (hJ : JetOn J g C) (hK : JetOn K h C) : JetOn (Jet.sub J K) (C2F.sub g h) C :=
  hJ.add hK.neg

theorem mul (hJ : JetOn J g C) (hK : JetOn K h C) : JetOn (Jet.mul J K) (C2F.mul g h) C := by
  intro x hx
  obtain ⟨a1, a2, a3⟩ := hJ x hx
  obtain ⟨b1, b2, b3⟩ := hK x hx
  refine ⟨IV.mul_mem a1 b1, IV.add_mem (IV.mul_mem a2 b1) (IV.mul_mem a1 b2), ?_⟩
  rw [show (C2F.mul g h).f2 x / 2 =
      g.f2 x / 2 * h.f x + g.f1 x * h.f1 x + g.f x * (h.f2 x / 2) by
    simp only [C2F.mul]; ring]
  exact IV.add_mem (IV.add_mem (IV.mul_mem a3 b1) (IV.mul_mem a2 b2)) (IV.mul_mem a1 b3)

theorem divInt {n : ℤ} (hn : 0 < n) (hJ : JetOn J g C) :
    JetOn (Jet.divInt J n) (C2F.divInt g n) C := by
  intro x hx
  obtain ⟨a1, a2, a3⟩ := hJ x hx
  refine ⟨IV.divInt_mem hn a1, IV.divInt_mem hn a2, ?_⟩
  rw [show (C2F.divInt g n).f2 x / 2 = g.f2 x / 2 / n by simp only [C2F.divInt]; ring]
  exact IV.divInt_mem hn a3

theorem pow (hJ : JetOn J g C) : ∀ n : ℕ, JetOn (Jet.pow J n) (C2F.pow g n) C
  | 0 => ofInt 1
  | 1 => hJ
  | n + 2 => by
    intro x hx
    obtain ⟨a1, a2, a3⟩ := hJ x hx
    have hm : (IV.rat ((n + 2 : ℕ) : ℤ)).mem (((n + 2 : ℕ) : ℤ) : ℝ) := IV.rat_one_mem _
    have hc : (IV.rat (((n + 2) * (n + 1) / 2 : ℕ) : ℤ)).mem
        ((((n + 2) * (n + 1) / 2 : ℕ) : ℤ) : ℝ) := IV.rat_one_mem _
    have heven : 2 ∣ (n + 2) * (n + 1) := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨(k + 1) * (n + 1), by subst hk; ring⟩
      · exact ⟨(n + 2) * (k + 1), by subst hk; ring⟩
    have hcval : ((((n + 2) * (n + 1) / 2 : ℕ) : ℤ) : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
      rw [Int.cast_natCast, Nat.cast_div heven (by norm_num)]
      push_cast
      ring
    rw [hcval] at hc
    have hmval : (((n + 2 : ℕ) : ℤ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [hmval] at hm
    refine ⟨IV.pow_mem a1 _, ?_, ?_⟩
    · rw [show (C2F.pow g (n + 2)).f1 x = ((n : ℝ) + 2) * g.f x ^ (n + 1) * g.f1 x by
        simp only [C2F.pow, show n + 2 - 1 = n + 1 by omega]; push_cast; ring]
      exact IV.mul_mem (IV.mul_mem hm (IV.pow_mem a1 (n + 1))) a2
    · rw [show (C2F.pow g (n + 2)).f2 x / 2 =
          ((n : ℝ) + 2) * g.f x ^ (n + 1) * (g.f2 x / 2) +
            ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 * g.f x ^ n * g.f1 x ^ 2 by
        simp only [C2F.pow, show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega]
        push_cast; ring]
      exact IV.add_mem (IV.mul_mem (IV.mul_mem hm (IV.pow_mem a1 (n + 1))) a3)
        (IV.mul_mem (IV.mul_mem hc (IV.pow_mem a1 n)) (IV.pow_mem a2 2))

theorem exp? (hJ : JetOn J g C) (h : Jet.exp? J = some K) : JetOn K (C2F.exp g) C := by
  simp only [Jet.exp?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨y, hy, rfl⟩ := h
  intro x hx
  obtain ⟨a1, a2, a3⟩ := hJ x hx
  have hey := IV.exp?_mem a1 hy
  refine ⟨hey, IV.mul_mem hey a2, ?_⟩
  rw [show (C2F.exp g).f2 x / 2 = Real.exp (g.f x) * (g.f2 x / 2 + g.f1 x ^ 2 / 2) by
    simp only [C2F.exp]; ring]
  exact IV.mul_mem hey (IV.add_mem a3 (IV.divInt_mem (n := 2) two_pos (IV.pow_mem a2 2)))

theorem cbrt? (hJ : JetOn J g C) (hpos : ∀ x, 0 < g.f x) (h : Jet.cbrt? J = some K) :
    JetOn K (C2F.cbrt g hpos) C := by
  simp only [Jet.cbrt?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨y, hy, r3, hr3, r9, hr9, rfl⟩ := h
  intro x hx
  obtain ⟨a1, a2, a3⟩ := hJ x hx
  obtain ⟨hc, -⟩ := IV.cbrt?_mem a1 hy
  have hcpos : 0 < g.f x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (hpos x) _
  obtain ⟨h3, -⟩ := IV.recip?_mem (IV.mul_mem (IV.rat_one_mem 3) (IV.pow_mem hc 2)) hr3
  obtain ⟨h9, -⟩ := IV.recip?_mem (IV.mul_mem (IV.rat_one_mem 9) (IV.pow_mem hc 5)) hr9
  refine ⟨hc, ?_, ?_⟩
  · rw [show (C2F.cbrt g hpos).f1 x =
        g.f1 x * ((3 : ℤ) * (g.f x ^ ((1 : ℝ) / 3)) ^ 2 : ℝ)⁻¹ by
      simp only [C2F.cbrt]; push_cast; ring]
    exact IV.mul_mem a2 h3
  · rw [show (C2F.cbrt g hpos).f2 x / 2 =
        g.f2 x / 2 * ((3 : ℤ) * (g.f x ^ ((1 : ℝ) / 3)) ^ 2 : ℝ)⁻¹ -
          g.f1 x ^ 2 * ((9 : ℤ) * (g.f x ^ ((1 : ℝ) / 3)) ^ 5 : ℝ)⁻¹ by
      simp only [C2F.cbrt]; push_cast; field_simp; ring]
    exact IV.sub_mem (IV.mul_mem a3 h3) (IV.mul_mem (IV.pow_mem a2 2) h9)

theorem logistic? (hJ : JetOn J g C) (h : Jet.logistic? J = some K) :
    JetOn K (C2F.logistic g) C := by
  simp only [Jet.logistic?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨pl, hpl, ph, hph, rfl⟩ := h
  intro x hx
  obtain ⟨a1, a2, a3⟩ := hJ x hx
  have hS := S_pos
  have hl := logPoint?_mem hpl
  have hh := logPoint?_mem hph
  have hσ0 := sigma_pos (g.f x)
  have hσ1 := sigma_lt_one (g.f x)
  -- value enclosure by monotonicity, clamped to [0, 1]
  have hy : (IV.mk (max 0 pl.lo) (min S ph.hi)).mem (sigma (g.f x)) := by
    constructor
    · rw [Int.cast_max, Int.cast_zero, ← max_div_div_right hS.le, zero_div]
      exact max_le hσ0.le (hl.1.trans (sigma_mono a1.1))
    · rw [Int.cast_min, ← min_div_div_right hS.le, div_self hS.ne']
      exact le_min hσ1.le ((sigma_mono a1.2).trans hh.2)
  have hz := IV.mul_mem hy (IV.sub_mem (IV.rat_one_mem 1) hy)
  refine ⟨hy, ?_, ?_⟩
  · rw [show (C2F.logistic g).f1 x =
        sigma (g.f x) * (((1 : ℤ) : ℝ) - sigma (g.f x)) * g.f1 x by
      simp only [C2F.logistic]; push_cast; ring]
    exact IV.mul_mem hz a2
  · rw [show (C2F.logistic g).f2 x / 2 =
        sigma (g.f x) * (((1 : ℤ) : ℝ) - sigma (g.f x)) * (g.f2 x / 2) +
          sigma (g.f x) * (((1 : ℤ) : ℝ) - sigma (g.f x)) *
            (((1 : ℤ) : ℝ) - ((2 : ℤ) : ℝ) * sigma (g.f x)) * g.f1 x ^ 2 / (2 : ℤ) by
      simp only [C2F.logistic]; push_cast; ring]
    exact IV.add_mem (IV.mul_mem hz a3)
      (IV.divInt_mem (n := 2) two_pos (IV.mul_mem (IV.mul_mem hz
        (IV.sub_mem (IV.rat_one_mem 1) (IV.mul_mem (IV.rat_one_mem 2) hy))) (IV.pow_mem a2 2)))

end JetOn

/-! ### The radial integrand -/

/-- `y = e^V + 1` is positive. -/
theorem exp_add_one_pos (v : C2F) : ∀ x, 0 < ((C2F.exp v).add (C2F.ofInt 1)).f x := by
  intro x
  simp only [C2F.add, C2F.exp, C2F.ofInt, C2F.const, Int.cast_one]
  positivity

/-- The radial integrand as an actual `C²` function, built by the same operation tree as
`radial?`. -/
noncomputable def radialC2 : C2F :=
  let r := C2F.id
  let s := (r.pow 2).divInt 2
  let v := ((C2F.ofInt 15).sub ((C2F.ofInt 2).mul s)).sub (s.pow 2)
  let p := v.logistic
  let vs := (C2F.ofInt (-2)).sub ((C2F.ofInt 2).mul s)
  let q := (C2F.ofInt 1).sub p
  let u1 := (((C2F.ofInt 4).mul p).mul vs).divInt 3
  let u2 := ((C2F.ofInt 4).mul
      (((C2F.ofInt (-2)).mul p).add ((p.mul q).mul (vs.pow 2)))).divInt 3
  let u3 := ((C2F.ofInt 4).mul
      ((((C2F.ofInt (-6)).mul p).mul q).mul vs |>.add
        (((p.mul q).mul ((C2F.ofInt 1).sub ((C2F.ofInt 2).mul p))).mul (vs.pow 3)))).divInt 3
  let a := u1.neg
  let k := ((((C2F.ofInt 8).mul (s.pow 3)).mul (u3.pow 2)).add
      ((((C2F.ofInt 24).mul (s.pow 2)).mul u2).mul u3)).add
      (((C2F.ofInt 258).mul s).mul (u2.pow 2)) |>.add
      ((C2F.ofInt 2).mul (((C2F.ofInt 40).mul (a.pow 3)).add
        ((a.sub (((C2F.ofInt 2).mul s).mul u2)).pow 3)))
  let y := (C2F.exp v).add (C2F.ofInt 1)
  let cy := y.cbrt (exp_add_one_pos v)
  ((r.pow 40).mul y).mul cy |>.mul k

/-- **Soundness of the radial evaluator**: if the input jet encloses the identity on `C`,
the computed jet encloses the radial integrand `radialC2` and its derivatives on `C`. -/
theorem radial?_sound {J K : Jet} {C : Set ℝ} (hJ : JetOn J C2F.id C)
    (h : radial? J = some K) : JetOn K radialC2 C := by
  simp only [radial?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨p, hp, ev, hev, cy, hcy, rfl⟩ := h
  have hs := (hJ.pow 2).divInt (n := 2) two_pos
  have hv := ((JetOn.ofInt 15).sub ((JetOn.ofInt 2).mul hs)).sub (hs.pow 2)
  have hpp := hv.logistic? hp
  have hvs := (JetOn.ofInt (-2)).sub ((JetOn.ofInt 2).mul hs)
  have hq := (JetOn.ofInt 1).sub hpp
  have hu1 := (((JetOn.ofInt 4).mul hpp).mul hvs).divInt (n := 3) (by norm_num)
  have hu2 := ((JetOn.ofInt 4).mul
      (((JetOn.ofInt (-2)).mul hpp).add ((hpp.mul hq).mul (hvs.pow 2)))).divInt (n := 3)
      (by norm_num)
  have hu3 := ((JetOn.ofInt 4).mul
      ((((JetOn.ofInt (-6)).mul hpp).mul hq).mul hvs |>.add
        (((hpp.mul hq).mul ((JetOn.ofInt 1).sub ((JetOn.ofInt 2).mul hpp))).mul
          (hvs.pow 3)))).divInt (n := 3) (by norm_num)
  have ha := hu1.neg
  have hk := ((((JetOn.ofInt 8).mul (hs.pow 3)).mul (hu3.pow 2)).add
      ((((JetOn.ofInt 24).mul (hs.pow 2)).mul hu2).mul hu3)).add
      (((JetOn.ofInt 258).mul hs).mul (hu2.pow 2)) |>.add
      ((JetOn.ofInt 2).mul (((JetOn.ofInt 40).mul (ha.pow 3)).add
        ((ha.sub (((JetOn.ofInt 2).mul hs).mul hu2)).pow 3)))
  have hy := (hv.exp? hev).add (JetOn.ofInt 1)
  have hcy' := hy.cbrt? (exp_add_one_pos _) hcy
  have hF := (((hJ.pow 40).mul hy).mul hcy').mul hk
  exact hF

end

end Fisher41.Num
