/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Computational kernel of the radial certificate

A faithful port of `verify/intervals.py` (integer intervals at scale `S = 2^160`,
order-two jets `(g, g', g''/2)`, the radial integrand `F`) that the Lean kernel can
evaluate with `decide +kernel`.  This file deliberately imports nothing beyond core
Lean, so that kernel reduction only meets core `Int`/`Nat` instances.

Operations that can fail (reciprocal of a non-positive interval, cube root of a
non-positive interval, argument reduction of `exp`) return `Option`; every check is
performed at run time, so the soundness proofs never need to know *why* a
computed candidate (e.g. a Newton cube root) is correct — only that the final
inequalities were checked.  Soundness is proved in `Fisher41.Numerics.Sound`.
-/

namespace Fisher41.Num

/-- The common scale `2^160`. -/
def S : Int := 1461501637330902918203684832716283019655932542976

/-- Ceiling division for a positive divisor. -/
def cdiv (a b : Int) : Int := -((-a) / b)

/-- The closed interval `[lo / S, hi / S]`. -/
structure IV where
  lo : Int
  hi : Int
deriving Repr, DecidableEq

namespace IV

/-- Outward enclosure of the rational `n / d` (`d > 0`). -/
def rat (n : Int) (d : Int := 1) : IV := ⟨n * S / d, cdiv (n * S) d⟩

def add (x y : IV) : IV := ⟨x.lo + y.lo, x.hi + y.hi⟩

def neg (x : IV) : IV := ⟨-x.hi, -x.lo⟩

def sub (x y : IV) : IV := add x (neg y)

def mul (x y : IV) : IV :=
  let a := x.lo * y.lo
  let b := x.lo * y.hi
  let c := x.hi * y.lo
  let d := x.hi * y.hi
  ⟨(min (min a b) (min c d)) / S, cdiv (max (max a b) (max c d)) S⟩

/-- Division by a positive integer constant. -/
def divInt (x : IV) (n : Int) : IV := ⟨x.lo / n, cdiv x.hi n⟩

/-- Natural powers, with the zero-crossing case for even exponents. -/
def pow (x : IV) : Nat → IV
  | 0 => rat 1
  | n + 1 =>
    let m := n + 1
    let den := S ^ n
    if m % 2 == 1 then ⟨x.lo ^ m / den, cdiv (x.hi ^ m) den⟩
    else
      let a := if x.lo ≤ 0 ∧ 0 ≤ x.hi then 0 else min (x.lo ^ m) (x.hi ^ m)
      let b := max (x.lo ^ m) (x.hi ^ m)
      ⟨a / den, cdiv b den⟩

/-- Reciprocal of a positive interval. -/
def recip? (x : IV) : Option IV :=
  if 0 < x.lo then some ⟨S * S / x.hi, cdiv (S * S) x.lo⟩ else none

def absUpper (x : IV) : Int := max x.lo.natAbs x.hi.natAbs

end IV

/-- Smallest `k ≤ k₀ + fuel` (searching upwards from `k₀`) with `8 x ≤ S 2^k`. -/
def findK (x : Int) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => if 8 * x > S * ((2 ^ k : Nat) : Int) then findK x fuel (k + 1) else k

/-- `taylor z fuel j term total`: adds the terms `z^i / i!` for `i = j, …, j + fuel - 1`,
where `term` encloses `z^(j-1) / (j-1)!` and `total` the partial sum up to `j - 1`. -/
def taylor (z : IV) : Nat → Nat → IV → IV → IV
  | 0, _, _, total => total
  | fuel + 1, j, term, total =>
    let term' := IV.divInt (IV.mul term z) j
    taylor z fuel (j + 1) term' (IV.add total term')

/-- Square `k` times. -/
def squareN : Nat → IV → IV
  | 0, t => t
  | k + 1, t => squareN k (IV.pow t 2)

/-- Enclosure of `exp (x / S)`: reduce to `z ≤ 1/8`, degree-32 Taylor polynomial,
one unit for the remainder, reciprocal for negative inputs, then square `k` times. -/
def expPoint? (x : Int) : Option IV :=
  let ax : Int := x.natAbs
  let k := findK ax 64 0
  let p : Int := ((2 ^ k : Nat) : Int)
  if 8 * ax ≤ S * p then
    let z : IV := ⟨ax / p, cdiv ax p⟩
    let t := taylor z 32 1 (IV.rat 1) (IV.rat 1)
    let t : IV := ⟨t.lo, t.hi + 1⟩
    if x < 0 then (IV.recip? t).map (squareN k) else some (squareN k t)
  else none

/-- Monotone enclosure of `exp` on an interval. -/
def IV.exp? (x : IV) : Option IV := do
  let a ← expPoint? x.lo
  let b ← expPoint? x.hi
  pure ⟨a.lo, b.hi⟩

/-- Integer cube root by Newton iteration (a *candidate*; never trusted). -/
def icbrtLoop (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := (2 * x + n / (x * x)) / 3
    if y ≥ x then x else icbrtLoop n fuel y

def icbrt (n : Nat) : Nat :=
  if n = 0 then 0 else icbrtLoop n 400 (2 ^ ((Nat.log2 n + 1 + 2) / 3))

/-- Cube root of a positive interval; the two cube inequalities are checked.  (The upper
witness is always `⌊∛B⌋ + 1`; `verify/intervals.py` uses `⌊∛B⌋` when `B` is an exact cube,
which never happens for the certificate data and only affects the last bit.) -/
def IV.cbrt? (x : IV) : Option IV :=
  if 0 < x.lo then
    let A := (x.lo * S * S).toNat
    let B := (x.hi * S * S).toNat
    let a := icbrt A
    let b := icbrt B + 1
    if a ^ 3 ≤ A ∧ B ≤ b ^ 3 then some ⟨(a : Int), (b : Int)⟩ else none
  else none

/-- `1 - 1 / (1 + exp (a / S))`, the logistic function at an endpoint. -/
def logPoint? (a : Int) : Option IV := do
  let e ← expPoint? a
  let r ← IV.recip? (IV.add e (IV.rat 1))
  pure (IV.add (IV.rat 1) (IV.neg r))

/-- Order-two jet `(g, g', g''/2)` of a function on a cell. -/
structure Jet where
  v : IV
  d : IV
  e : IV
deriving Repr

namespace Jet

def const (x : IV) : Jet := ⟨x, IV.rat 0, IV.rat 0⟩

def ofInt (n : Int) : Jet := const (IV.rat n)

def add (x y : Jet) : Jet := ⟨x.v.add y.v, x.d.add y.d, x.e.add y.e⟩

def neg (x : Jet) : Jet := ⟨x.v.neg, x.d.neg, x.e.neg⟩

def sub (x y : Jet) : Jet := add x (neg y)

def mul (x y : Jet) : Jet :=
  ⟨x.v.mul y.v, (x.d.mul y.v).add (x.v.mul y.d),
    ((x.e.mul y.v).add (x.d.mul y.d)).add (x.v.mul y.e)⟩

def divInt (x : Jet) (n : Int) : Jet := ⟨x.v.divInt n, x.d.divInt n, x.e.divInt n⟩

def pow (x : Jet) : Nat → Jet
  | 0 => ofInt 1
  | 1 => x
  | n + 2 =>
    let m := n + 2
    ⟨x.v.pow m, ((IV.rat m).mul (x.v.pow (n + 1))).mul x.d,
      (((IV.rat m).mul (x.v.pow (n + 1))).mul x.e).add
        (((IV.rat (m * (n + 1) / 2)).mul (x.v.pow n)).mul (x.d.pow 2))⟩

def exp? (x : Jet) : Option Jet := do
  let y ← x.v.exp?
  pure ⟨y, y.mul x.d, y.mul (x.e.add ((x.d.pow 2).divInt 2))⟩

def cbrt? (x : Jet) : Option Jet := do
  let y ← x.v.cbrt?
  let r3 ← IV.recip? ((IV.rat 3).mul (y.pow 2))
  let r9 ← IV.recip? ((IV.rat 9).mul (y.pow 5))
  pure ⟨y, x.d.mul r3, (x.e.mul r3).sub ((x.d.pow 2).mul r9)⟩

def logistic? (x : Jet) : Option Jet := do
  let pl ← logPoint? x.v.lo
  let ph ← logPoint? x.v.hi
  let y : IV := ⟨max 0 pl.lo, min S ph.hi⟩
  let z := y.mul ((IV.rat 1).sub y)
  pure ⟨y, z.mul x.d,
    (z.mul x.e).add (((z.mul ((IV.rat 1).sub ((IV.rat 2).mul y))).mul (x.d.pow 2)).divInt 2)⟩

end Jet

/-- The radial integrand `F(r) = r^40 (1+e^V)^{4/3} K₄₁[u](r²/2)` on jets; the same
operation tree as `radial` in `verify/intervals.py`. -/
def radial? (r : Jet) : Option Jet := do
  let s := (r.pow 2).divInt 2
  let v := ((Jet.ofInt 15).sub ((Jet.ofInt 2).mul s)).sub (s.pow 2)
  let p ← v.logistic?
  let vs := (Jet.ofInt (-2)).sub ((Jet.ofInt 2).mul s)
  let q := (Jet.ofInt 1).sub p
  let u1 := (((Jet.ofInt 4).mul p).mul vs).divInt 3
  let u2 := ((Jet.ofInt 4).mul
      (((Jet.ofInt (-2)).mul p).add ((p.mul q).mul (vs.pow 2)))).divInt 3
  let u3 := ((Jet.ofInt 4).mul
      ((((Jet.ofInt (-6)).mul p).mul q).mul vs |>.add
        (((p.mul q).mul ((Jet.ofInt 1).sub ((Jet.ofInt 2).mul p))).mul (vs.pow 3)))).divInt 3
  let a := u1.neg
  let k := ((((Jet.ofInt 8).mul (s.pow 3)).mul (u3.pow 2)).add
      ((((Jet.ofInt 24).mul (s.pow 2)).mul u2).mul u3)).add
      (((Jet.ofInt 258).mul s).mul (u2.pow 2)) |>.add
      ((Jet.ofInt 2).mul (((Jet.ofInt 40).mul (a.pow 3)).add
        ((a.sub (((Jet.ofInt 2).mul s).mul u2)).pow 3)))
  let ev ← v.exp?
  let y := ev.add (Jet.ofInt 1)
  let cy ← y.cbrt?
  pure (((r.pow 40).mul y).mul cy |>.mul k)

/-- Denominator of the partition endpoints: all endpoints are `A / 2^14`. -/
def D : Int := 16384

/-- Check of one cell `[A/D, B/D]` against an integer upper bound `q` for the
integral: midpoint value plus the midpoint-rule remainder `h³ B / (12 S)`, i.e.
`12 h D² U + h³ B ≤ 12 S D³ q` with `h = B - A`. -/
def cellCheck (A B : Nat) (q : Int) : Bool :=
  let left := IV.rat A D
  let right := IV.rat B D
  let cell : Jet := ⟨⟨left.lo, right.hi⟩, IV.rat 1, IV.rat 0⟩
  -- the identity jet on the one-point cell `{(A+B)/(2D)}`; its value component is
  -- the same as for a constant jet, and it satisfies the same jet semantics
  let mid : Jet := ⟨IV.rat ((A : Int) + B) (2 * D), IV.rat 1, IV.rat 0⟩
  match radial? mid, radial? cell with
  | some M, some K =>
    let h : Int := (B : Int) - A
    decide (A < B) && decide (12 * h * D ^ 2 * M.v.hi + h ^ 3 * K.e.absUpper ≤ 12 * S * D ^ 3 * q)
  | _, _ => false

/-- Consecutive cells `[p₀,p₁], [p₁,p₂], …` with bounds `q₀, q₁, …`. -/
def blockCheck : List Nat → List Int → Bool
  | a :: b :: rest, q :: qs => cellCheck a b q && blockCheck (b :: rest) qs
  | [_], [] => true
  | _, _ => false

end Fisher41.Num
