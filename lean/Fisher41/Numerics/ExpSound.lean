/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Fisher41.Numerics.IVSound

/-!
# Soundness of `exp`, the cube root and the logistic function on intervals

* `expPoint?_mem`: the 32-term Taylor evaluation with argument reduction encloses
  `exp (x / S)`; the remainder bound comes from `Real.exp_bound`.
* `IV.cbrt?_mem`: the checked integer witnesses enclose the real cube root
  `x ^ (1/3 : ℝ)` (the Newton search itself is never verified).
* `logPoint?_mem`: enclosure of the logistic function `σ t = eᵗ / (1 + eᵗ)`.
-/

namespace Fisher41.Num

open Real Finset

/-! ### Taylor polynomial of `exp` -/

theorem taylor_mem {z : IV} {zr : ℝ} (hz : z.mem zr) :
    ∀ (fuel j : ℕ) (term total : IV), 1 ≤ j →
      term.mem (zr ^ (j - 1) / ((j - 1).factorial : ℝ)) →
      total.mem (∑ i ∈ range j, zr ^ i / (i.factorial : ℝ)) →
      (taylor z fuel j term total).mem (∑ i ∈ range (j + fuel), zr ^ i / (i.factorial : ℝ))
  | 0, j, term, total, _, _, htot => by simpa [taylor] using htot
  | fuel + 1, j, term, total, hj, hterm, htot => by
    simp only [taylor]
    have hj0 : (0 : ℤ) < (j : ℤ) := by exact_mod_cast (show 0 < j by omega)
    have hterm' : (IV.divInt (IV.mul term z) (j : ℤ)).mem (zr ^ j / (j.factorial : ℝ)) := by
      have h := IV.divInt_mem hj0 (IV.mul_mem hterm hz)
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      convert h using 1
      simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      field_simp
    have h := taylor_mem hz fuel (j + 1) _ _ (by omega) (by simpa using hterm')
      (by rw [sum_range_succ]; exact IV.add_mem htot hterm')
    simpa [show j + 1 + fuel = j + (fuel + 1) by omega] using h

/-- Squaring `k` times encloses the `2^k`-th power. -/
theorem squareN_mem {I : IV} {y : ℝ} (hy : I.mem y) : ∀ k : ℕ, (squareN k I).mem (y ^ (2 ^ k))
  | 0 => by simpa [squareN] using hy
  | k + 1 => by
    have h := squareN_mem (I := IV.pow I 2) (y := y ^ 2) (IV.pow_mem hy 2) k
    show (squareN k (IV.pow I 2)).mem (y ^ 2 ^ (k + 1))
    rw [pow_succ', pow_mul]
    exact h

/-- The fixed remainder bound `(1/8)^33 · 34 / (33! · 33) < 2^(-160)`. -/
theorem taylor_remainder_small :
    ((1 : ℝ) / 8) ^ 33 * ((Nat.succ 33 : ℝ) / ((Nat.factorial 33 : ℝ) * 33)) ≤ 1 / (S : ℝ) := by
  unfold S
  norm_num [Nat.factorial]

theorem exp_mem_of_taylor {zr : ℝ} {t : IV} (h0 : 0 ≤ zr) (h8 : zr ≤ 1 / 8)
    (ht : t.mem (∑ i ∈ range 33, zr ^ i / (i.factorial : ℝ))) :
    (⟨t.lo, t.hi + 1⟩ : IV).mem (Real.exp zr) := by
  obtain ⟨h1, h2⟩ := ht
  have hS := S_pos
  constructor
  · exact h1.trans (Real.sum_le_exp_of_nonneg h0 33)
  · have hb := Real.exp_bound (x := zr) (by rw [abs_of_nonneg h0]; linarith) (n := 33) (by norm_num)
    have hpow : |zr| ^ 33 ≤ ((1 : ℝ) / 8) ^ 33 := by
      rw [abs_of_nonneg h0]; exact pow_le_pow_left₀ h0 h8 33
    have hrem : |Real.exp zr - ∑ i ∈ range 33, zr ^ i / (i.factorial : ℝ)| ≤ 1 / (S : ℝ) := by
      refine hb.trans ((mul_le_mul_of_nonneg_right hpow (by positivity)).trans ?_)
      exact taylor_remainder_small
    have := (abs_le.1 hrem).2
    simp only [Int.cast_add, Int.cast_one, add_div]
    linarith

theorem findK_spec (x : ℤ) : ∀ fuel k : ℕ, k ≤ findK x fuel k
  | 0, k => le_rfl
  | fuel + 1, k => by
    simp only [findK]
    split_ifs
    · exact (Nat.le_succ k).trans (findK_spec x fuel (k + 1))
    · exact le_rfl

/-- The reduced Taylor enclosure: if `8 |x| ≤ S 2^k` (with `k` the search result), the
Taylor interval plus one unit encloses `exp (|x| / S / 2^k)`. -/
theorem expPoint_core (x : ℤ)
    (h8 : 8 * (x.natAbs : ℤ) ≤ S * ((2 ^ findK (x.natAbs : ℤ) 64 0 : ℕ) : ℤ)) :
    (⟨(taylor ⟨(x.natAbs : ℤ) / ((2 ^ findK (x.natAbs : ℤ) 64 0 : ℕ) : ℤ),
        cdiv (x.natAbs : ℤ) ((2 ^ findK (x.natAbs : ℤ) 64 0 : ℕ) : ℤ)⟩ 32 1
          (IV.rat 1) (IV.rat 1)).lo,
      (taylor ⟨(x.natAbs : ℤ) / ((2 ^ findK (x.natAbs : ℤ) 64 0 : ℕ) : ℤ),
        cdiv (x.natAbs : ℤ) ((2 ^ findK (x.natAbs : ℤ) 64 0 : ℕ) : ℤ)⟩ 32 1
          (IV.rat 1) (IV.rat 1)).hi + 1⟩ : IV).mem
      (Real.exp ((x.natAbs : ℝ) / ((2 ^ findK (x.natAbs : ℤ) 64 0 : ℕ) : ℝ) / S)) := by
  set ax : ℤ := (x.natAbs : ℤ) with hax
  set k := findK ax 64 0 with hk
  set p : ℤ := ((2 ^ k : ℕ) : ℤ) with hp
  have hS := S_pos
  have hp0 : (0 : ℤ) < p := by rw [hp]; exact_mod_cast pow_pos (by norm_num) k
  have hax0 : (0 : ℤ) ≤ ax := by rw [hax]; exact Int.natCast_nonneg _
  have hcast : ((2 ^ k : ℕ) : ℝ) = (p : ℝ) := by rw [hp]; push_cast; rfl
  have haxr : (x.natAbs : ℝ) = (ax : ℝ) := by rw [hax]; exact (Int.cast_natCast _).symm
  rw [hcast, haxr]
  set zr : ℝ := (ax : ℝ) / p / S with hzr
  have hz : (IV.mk (ax / p) (cdiv ax p)).mem zr := by
    constructor
    · rw [hzr]; gcongr; exact cast_ediv_le _ _ hp0
    · rw [hzr]; gcongr; exact le_cast_cdiv _ _ hp0
  have hzr0 : 0 ≤ zr := by
    rw [hzr]
    have : (0 : ℝ) ≤ ax := by exact_mod_cast hax0
    have : (0 : ℝ) < p := by exact_mod_cast hp0
    positivity
  have hzr8 : zr ≤ 1 / 8 := by
    have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
    rw [hzr, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ((8 * ax : ℤ) : ℝ) ≤ ((S * p : ℤ) : ℝ) := by exact_mod_cast h8
    push_cast at this
    linarith
  have htay := taylor_mem hz 32 1 (IV.rat 1) (IV.rat 1) le_rfl
    (by simpa using IV.rat_one_mem 1) (by simpa using IV.rat_one_mem 1)
  exact exp_mem_of_taylor hzr0 hzr8 (by simpa using htay)

theorem exp_pow_two_pow (y : ℝ) (k : ℕ) : Real.exp y ^ (2 ^ k) = Real.exp (y * 2 ^ k) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- Enclosure of `exp (x / S)` at an integer endpoint. -/
theorem expPoint?_mem {x : ℤ} {I : IV} (h : expPoint? x = some I) : I.mem (Real.exp (x / S)) := by
  have hS := S_pos
  simp only [expPoint?] at h
  split_ifs at h with h8 hneg
  · -- negative input: reciprocal, then squaring
    obtain ⟨J, hJ, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hJm, -⟩ := IV.recip?_mem (expPoint_core x h8) hJ
    have hsq := squareN_mem hJm (findK (x.natAbs : ℤ) 64 0)
    rw [← Real.exp_neg, exp_pow_two_pow] at hsq
    convert hsq using 2
    have hx : (x.natAbs : ℝ) = -x := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
    rw [hx]
    push_cast
    field_simp
  · cases h
    have hsq := squareN_mem (expPoint_core x h8) (findK (x.natAbs : ℤ) 64 0)
    rw [exp_pow_two_pow] at hsq
    convert hsq using 2
    have hx : (x.natAbs : ℝ) = x := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast (not_lt.1 hneg))]
    rw [hx]
    push_cast
    field_simp

/-- Monotone enclosure of `exp` on an interval. -/
theorem IV.exp?_mem {I J : IV} {x : ℝ} (hx : I.mem x) (h : I.exp? = some J) :
    J.mem (Real.exp x) := by
  unfold IV.exp? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  obtain ⟨ha1, -⟩ := expPoint?_mem ha
  obtain ⟨-, hb2⟩ := expPoint?_mem hb
  obtain ⟨hx1, hx2⟩ := hx
  exact ⟨ha1.trans (Real.exp_le_exp.2 hx1), (Real.exp_le_exp.2 hx2).trans hb2⟩

/-! ### Cube root -/

theorem rpow_third_pow_three {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem IV.cbrt?_mem {I J : IV} {x : ℝ} (hx : I.mem x) (h : I.cbrt? = some J) :
    J.mem (x ^ ((1 : ℝ) / 3)) ∧ 0 < x := by
  simp only [IV.cbrt?] at h
  split_ifs at h with hlo hchk
  cases h
  obtain ⟨h1, h2⟩ := hx
  have hS := S_pos
  have hlo' : (0 : ℝ) < I.lo := by exact_mod_cast hlo
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) h1
  set c := x ^ ((1 : ℝ) / 3) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hxpos.le _
  have hc3 : c ^ 3 = x := rpow_third_pow_three hxpos.le
  -- integer facts
  have hA : (0 : ℤ) ≤ I.lo * S * S :=
    mul_nonneg (mul_nonneg hlo.le S_pos_int.le) S_pos_int.le
  have hB : (0 : ℤ) ≤ I.hi * S * S := by
    have : (0 : ℝ) < I.hi := by
      have := lt_of_lt_of_le hxpos h2
      exact (div_pos_iff_of_pos_right hS).1 this
    have : (0 : ℤ) < I.hi := by exact_mod_cast this
    exact mul_nonneg (mul_nonneg this.le S_pos_int.le) S_pos_int.le
  obtain ⟨ha3, hb3⟩ := hchk
  have ha3' : ((icbrt (I.lo * S * S).toNat : ℕ) : ℝ) ^ 3 ≤ (I.lo : ℝ) * S * S := by
    have : ((icbrt (I.lo * S * S).toNat ^ 3 : ℕ) : ℤ) ≤ ((I.lo * S * S).toNat : ℤ) := by
      exact_mod_cast ha3
    rw [Int.toNat_of_nonneg hA] at this
    exact_mod_cast this
  refine ⟨⟨?_, ?_⟩, hxpos⟩
  · -- a / S ≤ c  since (a/S)^3 ≤ lo/S ≤ x = c^3
    set a : ℝ := ((icbrt (I.lo * S * S).toNat : ℕ) : ℝ)
    have ha0 : 0 ≤ a := Nat.cast_nonneg _
    have : (a / S) ^ 3 ≤ c ^ 3 := by
      rw [hc3, div_pow]
      calc a ^ 3 / (S : ℝ) ^ 3 ≤ (I.lo : ℝ) * S * S / (S : ℝ) ^ 3 := by gcongr
        _ = (I.lo : ℝ) / S := by field_simp
        _ ≤ x := h1
    have := le_of_pow_le_pow_left₀ (by norm_num) hc0 this
    simpa using this
  · -- c ≤ b' / S  since c^3 = x ≤ hi/S ≤ (b'/S)^3
    set B := (I.hi * S * S).toNat
    set b' := icbrt B + 1
    have hb3' : (I.hi : ℝ) * S * S ≤ (b' : ℝ) ^ 3 := by
      have : ((B : ℕ) : ℤ) ≤ ((b' ^ 3 : ℕ) : ℤ) := by exact_mod_cast hb3
      rw [show ((B : ℕ) : ℤ) = I.hi * S * S from Int.toNat_of_nonneg hB] at this
      exact_mod_cast this
    have hb0 : (0 : ℝ) ≤ (b' : ℝ) / S := by positivity
    have : c ^ 3 ≤ ((b' : ℝ) / S) ^ 3 := by
      rw [hc3, div_pow]
      calc x ≤ (I.hi : ℝ) / S := h2
        _ = (I.hi : ℝ) * S * S / (S : ℝ) ^ 3 := by field_simp
        _ ≤ (b' : ℝ) ^ 3 / (S : ℝ) ^ 3 := by gcongr
    have := le_of_pow_le_pow_left₀ (by norm_num) hb0 this
    simpa using this

/-! ### Logistic function -/

/-- The logistic function `σ t = eᵗ / (1 + eᵗ)`. -/
noncomputable def sigma (t : ℝ) : ℝ := Real.exp t / (1 + Real.exp t)

theorem sigma_eq (t : ℝ) : sigma t = 1 + -(Real.exp t + 1)⁻¹ := by
  unfold sigma
  have : 0 < 1 + Real.exp t := by positivity
  field_simp
  ring

theorem sigma_pos (t : ℝ) : 0 < sigma t := by unfold sigma; positivity

theorem sigma_lt_one (t : ℝ) : sigma t < 1 := by
  unfold sigma
  rw [div_lt_one (by positivity)]
  linarith

theorem sigma_mono : Monotone sigma := by
  intro a b hab
  rw [sigma_eq, sigma_eq]
  have h := Real.exp_le_exp.2 hab
  have ha : 0 < Real.exp a + 1 := by positivity
  have : (Real.exp b + 1)⁻¹ ≤ (Real.exp a + 1)⁻¹ := by
    apply inv_anti₀ ha; linarith
  linarith

theorem logPoint?_mem {a : ℤ} {I : IV} (h : logPoint? a = some I) : I.mem (sigma (a / S)) := by
  unfold logPoint? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨e, he, r, hr, rfl⟩ := h
  have hem := expPoint?_mem he
  obtain ⟨hrm, -⟩ := IV.recip?_mem (IV.add_mem hem (IV.rat_one_mem 1)) hr
  rw [sigma_eq]
  have := IV.add_mem (IV.rat_one_mem 1) (IV.neg_mem hrm)
  simpa using this

end Fisher41.Num
