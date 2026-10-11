/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license.
-/
import Fisher41.Numerics.MainBound
import Fisher41.Static.Profile

/-!
# The cut radial integral is negative

Combining the kernel-checked bound on the uncut integrand (`integral_radial_le`), the
identification of the computed integrand with the mathematical one (`radialC2_f_eq`), and the
cutoff error (`integral_Fcut_le`).
-/

namespace Fisher41

/-- `J_cut = ∫₀⁸ r^40 e^{ũ(r²/2)} K₄₁[ũ](r²/2) dr ≤ -5·10¹⁸ + 16`. -/
theorem integral_Fcut_le_neg : (∫ r in (0 : ℝ)..8, Fcut r) ≤ -5000000000000000000 + 16 := by
  have h1 := integral_Fcut_le
  have h2 : (∫ r in (0 : ℝ)..8, Fmath r) = ∫ r in (0 : ℝ)..8, Num.radialC2.f r := by
    congr 1
    funext r
    exact (radialC2_f_eq r).symm
  have h3 := Num.integral_radial_le
  linarith

end Fisher41
