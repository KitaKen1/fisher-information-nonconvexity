/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Fisher41.Numerics.Compute

/-!
# Soundness of the integer interval arithmetic

`IV.mem I x` means `x ∈ [I.lo / S, I.hi / S]`.  Every operation of
`Fisher41.Numerics.Compute` on intervals maps enclosures to enclosures.
-/

namespace Fisher41.Num

/-- Real semantics of an interval: `x ∈ [lo / S, hi / S]`. -/
def IV.mem (I : IV) (x : ℝ) : Prop := (I.lo : ℝ) / (S : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) / (S : ℝ)

theorem S_pos_int : (0 : ℤ) < S := by unfold S; norm_num

theorem S_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos_int

/-- Floor division is below real division. -/
theorem cast_ediv_le (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  exact_mod_cast Int.ediv_mul_le a hb.ne'

/-- Ceiling division is above real division. -/
theorem le_cast_cdiv (a b : ℤ) (hb : 0 < b) : (a : ℝ) / (b : ℝ) ≤ ((cdiv a b : ℤ) : ℝ) := by
  have h := cast_ediv_le (-a) b hb
  simp only [cdiv, Int.cast_neg] at h ⊢
  rw [neg_div] at h
  linarith

namespace IV

theorem mem_def {I : IV} {x : ℝ} : I.mem x ↔ (I.lo : ℝ) / S ≤ x ∧ x ≤ (I.hi : ℝ) / S := Iff.rfl

theorem rat_mem (n d : ℤ) (hd : 0 < d) : (rat n d).mem ((n : ℝ) / d) := by
  have hS := S_pos
  constructor
  · have h := cast_ediv_le (n * S) d hd
    rw [div_le_iff₀ hS]
    calc ((n * S / d : ℤ) : ℝ) ≤ ((n * S : ℤ) : ℝ) / d := h
      _ = (n : ℝ) / d * S := by push_cast; ring
  · have h := le_cast_cdiv (n * S) d hd
    rw [le_div_iff₀ hS]
    calc (n : ℝ) / d * S = ((n * S : ℤ) : ℝ) / d := by push_cast; ring
      _ ≤ _ := h

theorem rat_one_mem (n : ℤ) : (rat n).mem (n : ℝ) := by
  simpa using rat_mem n 1 one_pos

theorem add_mem {I J : IV} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) : (add I J).mem (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  simp only [mem, add, Int.cast_add, add_div]
  constructor <;> linarith

theorem neg_mem {I : IV} {x : ℝ} (hx : I.mem x) : (neg I).mem (-x) := by
  obtain ⟨h1, h2⟩ := hx
  simp only [mem, neg, Int.cast_neg, neg_div]
  constructor <;> linarith

theorem sub_mem {I J : IV} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) : (sub I J).mem (x - y) := by
  rw [sub_eq_add_neg]
  exact add_mem hx (neg_mem hy)

/-- The product of two reals in two intervals lies between the extreme endpoint products. -/
theorem mul_bounds {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  constructor
  · have h1 : min (a * y) (b * y) ≤ x * y := by
      rcases le_total 0 y with hy | hy
      · exact min_le_of_left_le (by nlinarith)
      · exact min_le_of_right_le (by nlinarith)
    have h2 : min (a * c) (a * d) ≤ a * y := by
      rcases le_total 0 a with ha | ha
      · exact min_le_of_left_le (by nlinarith)
      · exact min_le_of_right_le (by nlinarith)
    have h3 : min (b * c) (b * d) ≤ b * y := by
      rcases le_total 0 b with hb | hb
      · exact min_le_of_left_le (by nlinarith)
      · exact min_le_of_right_le (by nlinarith)
    exact (min_le_min h2 h3).trans h1
  · have h1 : x * y ≤ max (a * y) (b * y) := by
      rcases le_total 0 y with hy | hy
      · exact le_max_of_le_right (by nlinarith)
      · exact le_max_of_le_left (by nlinarith)
    have h2 : a * y ≤ max (a * c) (a * d) := by
      rcases le_total 0 a with ha | ha
      · exact le_max_of_le_right (by nlinarith)
      · exact le_max_of_le_left (by nlinarith)
    have h3 : b * y ≤ max (b * c) (b * d) := by
      rcases le_total 0 b with hb | hb
      · exact le_max_of_le_right (by nlinarith)
      · exact le_max_of_le_left (by nlinarith)
    exact h1.trans (max_le_max h2 h3)

theorem mul_mem {I J : IV} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) : (mul I J).mem (x * y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hS := S_pos
  obtain ⟨hlo, hhi⟩ := mul_bounds hx1 hx2 hy1 hy2
  have key : ∀ p q : ℤ, (p : ℝ) / S * ((q : ℝ) / S) = ((p * q : ℤ) : ℝ) / S / S := by
    intro p q; push_cast; field_simp
  simp only [key] at hlo hhi
  set a := I.lo * J.lo
  set b := I.lo * J.hi
  set c := I.hi * J.lo
  set d := I.hi * J.hi
  simp only [mul]
  constructor
  · set m := min (min a b) (min c d) with hm
    have hm' : (m : ℝ) / S / S ≤ x * y := by
      refine le_trans ?_ hlo
      have hS2 : (0 : ℝ) ≤ S := hS.le
      refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;>
        · gcongr
          exact_mod_cast (by omega : _)
    calc ((m / S : ℤ) : ℝ) / S ≤ (m : ℝ) / S / S := by
          gcongr; exact cast_ediv_le m S S_pos_int
      _ ≤ x * y := hm'
  · set m := max (max a b) (max c d) with hm
    have hm' : x * y ≤ (m : ℝ) / S / S := by
      refine le_trans hhi ?_
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;>
        · gcongr
          exact_mod_cast (by omega : _)
    calc x * y ≤ (m : ℝ) / S / S := hm'
      _ ≤ ((cdiv m S : ℤ) : ℝ) / S := by
          gcongr; exact le_cast_cdiv m S S_pos_int

theorem divInt_mem {I : IV} {x : ℝ} {n : ℤ} (hn : 0 < n) (hx : I.mem x) :
    (divInt I n).mem (x / n) := by
  obtain ⟨h1, h2⟩ := hx
  have hS := S_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [mem, divInt]
  constructor
  · calc ((I.lo / n : ℤ) : ℝ) / S ≤ (I.lo : ℝ) / n / S := by
          gcongr; exact cast_ediv_le _ _ hn
      _ = (I.lo : ℝ) / S / n := by ring
      _ ≤ x / n := by gcongr
  · calc x / n ≤ (I.hi : ℝ) / S / n := by gcongr
      _ = (I.hi : ℝ) / n / S := by ring
      _ ≤ ((cdiv I.hi n : ℤ) : ℝ) / S := by gcongr; exact le_cast_cdiv _ _ hn

theorem recip?_mem {I J : IV} {x : ℝ} (hx : I.mem x) (h : recip? I = some J) :
    J.mem x⁻¹ ∧ 0 < x := by
  unfold recip? at h
  split_ifs at h with hlo
  cases h
  obtain ⟨h1, h2⟩ := hx
  have hS := S_pos
  have hlo' : (0 : ℝ) < I.lo := by exact_mod_cast hlo
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity) h1
  have hhi' : (0 : ℝ) < I.hi := by
    have : (0 : ℝ) < (I.hi : ℝ) / S := lt_of_lt_of_le hxpos h2
    exact (div_pos_iff_of_pos_right hS).1 this
  have hhi : (0 : ℤ) < I.hi := by exact_mod_cast hhi'
  refine ⟨⟨?_, ?_⟩, hxpos⟩
  · -- floor(S²/hi)/S ≤ S/hi ≤ 1/x
    calc ((S * S / I.hi : ℤ) : ℝ) / S ≤ ((S * S : ℤ) : ℝ) / I.hi / S := by
          gcongr; exact cast_ediv_le _ _ hhi
      _ = 1 / ((I.hi : ℝ) / S) := by push_cast; field_simp
      _ ≤ 1 / x := by gcongr
      _ = x⁻¹ := one_div x
  · calc x⁻¹ = 1 / x := (one_div x).symm
      _ ≤ 1 / ((I.lo : ℝ) / S) := by gcongr
      _ = ((S * S : ℤ) : ℝ) / I.lo / S := by push_cast; field_simp
      _ ≤ ((cdiv (S * S) I.lo : ℤ) : ℝ) / S := by gcongr; exact le_cast_cdiv _ _ hlo

theorem abs_le_absUpper {I : IV} {x : ℝ} (hx : I.mem x) : |x| ≤ (absUpper I : ℝ) / S := by
  obtain ⟨h1, h2⟩ := hx
  have hS := S_pos
  have hlo : |(I.lo : ℝ)| ≤ (absUpper I : ℝ) := by
    simp only [absUpper]
    push_cast
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast le_max_left _ _
  have hhi : |(I.hi : ℝ)| ≤ (absUpper I : ℝ) := by
    simp only [absUpper]
    push_cast
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast le_max_right _ _
  have hlo2 : -(absUpper I : ℝ) ≤ (I.lo : ℝ) := by linarith [neg_abs_le (I.lo : ℝ)]
  have hhi2 : (I.hi : ℝ) ≤ (absUpper I : ℝ) := le_trans (le_abs_self _) hhi
  rw [abs_le]
  constructor
  · have : -((absUpper I : ℝ) / S) ≤ (I.lo : ℝ) / S := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right hlo2 hS.le
    linarith
  · have : (I.hi : ℝ) / S ≤ (absUpper I : ℝ) / S := div_le_div_of_nonneg_right hhi2 hS.le
    linarith

/-- Natural powers. -/
theorem pow_mem {I : IV} {x : ℝ} (hx : I.mem x) : ∀ n : ℕ, (pow I n).mem (x ^ n)
  | 0 => by simpa [pow] using rat_one_mem 1
  | n + 1 => by
    obtain ⟨h1, h2⟩ := hx
    have hS := S_pos
    have hSnZ : (0 : ℤ) < S ^ n := pow_pos S_pos_int n
    -- `(p / S)^(n+1) = p^(n+1) / S^n / S`
    have key : ∀ p : ℤ, ((p : ℝ) / S) ^ (n + 1) =
        ((p ^ (n + 1) : ℤ) : ℝ) / ((S ^ n : ℤ) : ℝ) / S := by
      intro p; push_cast; rw [div_pow, div_div, ← pow_succ]
    have hcmin : ((min (I.lo ^ (n + 1)) (I.hi ^ (n + 1)) : ℤ) : ℝ) / ((S ^ n : ℤ) : ℝ) / S =
        min (((I.lo : ℝ) / S) ^ (n + 1)) (((I.hi : ℝ) / S) ^ (n + 1)) := by
      rw [key, key, Int.cast_min, min_div_div_right (by positivity),
        min_div_div_right (by positivity)]
    have hcmax : ((max (I.lo ^ (n + 1)) (I.hi ^ (n + 1)) : ℤ) : ℝ) / ((S ^ n : ℤ) : ℝ) / S =
        max (((I.lo : ℝ) / S) ^ (n + 1)) (((I.hi : ℝ) / S) ^ (n + 1)) := by
      rw [key, key, Int.cast_max, max_div_div_right (by positivity),
        max_div_div_right (by positivity)]
    -- upper bound shared by the even cases
    have hupper : (Even (n + 1)) →
        x ^ (n + 1) ≤ ((cdiv (max (I.lo ^ (n + 1)) (I.hi ^ (n + 1))) (S ^ n) : ℤ) : ℝ) / S := by
      intro heven
      have habs : |x| ≤ max |(I.lo : ℝ) / S| |(I.hi : ℝ) / S| := by
        rw [abs_le]
        constructor
        · have := neg_abs_le ((I.lo : ℝ) / S)
          have := le_max_left |(I.lo : ℝ) / S| |(I.hi : ℝ) / S|
          linarith
        · have := le_abs_self ((I.hi : ℝ) / S)
          have := le_max_right |(I.lo : ℝ) / S| |(I.hi : ℝ) / S|
          linarith
      have hup : x ^ (n + 1) ≤ max (((I.lo : ℝ) / S) ^ (n + 1)) (((I.hi : ℝ) / S) ^ (n + 1)) := by
        rw [← heven.pow_abs x, ← heven.pow_abs ((I.lo : ℝ) / S),
          ← heven.pow_abs ((I.hi : ℝ) / S)]
        calc |x| ^ (n + 1) ≤ (max |(I.lo : ℝ) / S| |(I.hi : ℝ) / S|) ^ (n + 1) :=
              pow_le_pow_left₀ (abs_nonneg x) habs _
          _ = max (|(I.lo : ℝ) / S| ^ (n + 1)) (|(I.hi : ℝ) / S| ^ (n + 1)) := by
              rcases le_total |(I.lo : ℝ) / S| |(I.hi : ℝ) / S| with h | h
              · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (abs_nonneg _) h _)]
              · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (abs_nonneg _) h _)]
      calc x ^ (n + 1) ≤ _ := hup
        _ = _ := hcmax.symm
        _ ≤ ((cdiv (max (I.lo ^ (n + 1)) (I.hi ^ (n + 1))) (S ^ n) : ℤ) : ℝ) / S := by
            gcongr; exact le_cast_cdiv _ _ hSnZ
    have heven_of : ¬((n + 1) % 2 == 1) = true → Even (n + 1) := by
      intro hodd
      rcases Nat.even_or_odd (n + 1) with h | h
      · exact h
      · exfalso; apply hodd; rw [Nat.odd_iff] at h; simp [h]
    simp only [pow]
    split_ifs with hodd hz
    · -- odd exponent: monotone
      have hodd' : Odd (n + 1) := by
        rw [Nat.odd_iff]; simpa using hodd
      have hm : StrictMono fun a : ℝ => a ^ (n + 1) := hodd'.strictMono_pow
      constructor
      · calc (((I.lo ^ (n + 1) / S ^ n : ℤ)) : ℝ) / S
            ≤ ((I.lo ^ (n + 1) : ℤ) : ℝ) / ((S ^ n : ℤ) : ℝ) / S := by
              gcongr; exact cast_ediv_le _ _ hSnZ
          _ = ((I.lo : ℝ) / S) ^ (n + 1) := (key _).symm
          _ ≤ x ^ (n + 1) := hm.monotone h1
      · calc x ^ (n + 1) ≤ ((I.hi : ℝ) / S) ^ (n + 1) := hm.monotone h2
          _ = ((I.hi ^ (n + 1) : ℤ) : ℝ) / ((S ^ n : ℤ) : ℝ) / S := key _
          _ ≤ ((cdiv (I.hi ^ (n + 1)) (S ^ n) : ℤ) : ℝ) / S := by
              gcongr; exact le_cast_cdiv _ _ hSnZ
    · -- even exponent, interval contains 0
      have heven := heven_of hodd
      refine ⟨?_, hupper heven⟩
      simp only [Int.zero_ediv, Int.cast_zero, zero_div]
      exact heven.pow_nonneg x
    · -- even exponent, interval of constant sign
      have heven := heven_of hodd
      refine ⟨?_, hupper heven⟩
      have hmin : min (((I.lo : ℝ) / S) ^ (n + 1)) (((I.hi : ℝ) / S) ^ (n + 1)) ≤ x ^ (n + 1) := by
        rcases not_and_or.1 hz with hlo | hhi
        · have hlo' : (0 : ℝ) < (I.lo : ℝ) / S := by
            have : (0 : ℝ) < I.lo := by exact_mod_cast (lt_of_not_ge hlo)
            positivity
          exact min_le_of_left_le (pow_le_pow_left₀ hlo'.le h1 _)
        · have hhi' : (I.hi : ℝ) / S < 0 := by
            have : (I.hi : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hhi)
            exact div_neg_of_neg_of_pos this hS
          refine min_le_of_right_le ?_
          rw [← heven.pow_abs x, ← heven.pow_abs ((I.hi : ℝ) / S)]
          apply pow_le_pow_left₀ (abs_nonneg _)
          rw [abs_of_neg hhi', abs_of_neg (lt_of_le_of_lt h2 hhi')]
          linarith
      calc ((min (I.lo ^ (n + 1)) (I.hi ^ (n + 1)) / S ^ n : ℤ) : ℝ) / S
          ≤ ((min (I.lo ^ (n + 1)) (I.hi ^ (n + 1)) : ℤ) : ℝ) / ((S ^ n : ℤ) : ℝ) / S := by
            gcongr; exact cast_ediv_le _ _ hSnZ
        _ = _ := hcmin
        _ ≤ x ^ (n + 1) := hmin

end IV

end Fisher41.Num
