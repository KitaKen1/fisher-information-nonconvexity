/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Numerics.Compute

/-!
# The per-cell check used by the certificate (core only)

`cellOK A B q` evaluates the radial jet on the midpoint and on the cell `[A/D, B/D]` and
compares the midpoint-rule bound with `q`.  The decision is separated from the evaluation
(`cellDecide`), so that soundness proofs never unfold the evaluator.
-/

namespace Fisher41.Num

/-- Identity jet on the one-point cell `{(A+B)/(2D)}`. -/
def midJet (A B : Nat) : Jet := ⟨IV.rat ((A : Int) + B) (2 * D), IV.rat 1, IV.rat 0⟩

/-- Identity jet on the cell `[A/D, B/D]`. -/
def cellJet (A B : Nat) : Jet := ⟨⟨(IV.rat A D).lo, (IV.rat B D).hi⟩, IV.rat 1, IV.rat 0⟩

/-- `12 h D² U + h³ B ≤ 12 S D³ q` with `h = B - A`, i.e. midpoint value plus remainder `≤ q`. -/
def cellDecide (A B : Nat) (q : Int) : Option Jet → Option Jet → Bool
  | some M, some K =>
    decide (A < B) &&
      decide (12 * ((B : Int) - A) * D ^ 2 * M.v.hi + ((B : Int) - A) ^ 3 * K.e.absUpper ≤
        12 * S * D ^ 3 * q)
  | _, _ => false

/-- The cell check: evaluate both jets, then decide. -/
def cellOK (A B : Nat) (q : Int) : Bool :=
  cellDecide A B q (radial? (midJet A B)) (radial? (cellJet A B))

end Fisher41.Num
