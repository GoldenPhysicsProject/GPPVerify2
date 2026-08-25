import Mathlib.Tactic

/-!
# Algebra of the mu^4 dimension-shift rational limit

Discovery2 identifies the scalar-integral relation
`I4^(4-2ε)[mu^4] = -ε(1-ε) I4^(8-2ε)` and the universal raised-box
pole `I4^(8-2ε) = 1/(6ε) + O(1)` in the stated normalization.

This file formalizes the exact algebraic cancellation underlying the finite `-1/6`
limit. The analytic Feynman-integral residue itself is not encoded here.
-/

namespace GppMu4DimensionShift

/-- Exact Gamma-recursion polynomial appearing in the `mu^4` dimension shift. -/
def shiftFactor (ε : ℝ) : ℝ := -ε * (1 - ε)

/-- Multiplying the shift factor by the universal box pole `1/(6ε)` cancels
`ε` exactly away from `ε=0`. -/
theorem shiftFactor_mul_boxPole {ε : ℝ} (hε : ε ≠ 0) :
    shiftFactor ε * (1 / (6 * ε)) = -(1 - ε) / 6 := by
  unfold shiftFactor
  field_simp [hε]
  ring

/-- The finite residue tends algebraically to `-1/6`; at the exact endpoint this
is simply the value of the regularized closed expression. -/
theorem regularizedResidue_at_zero :
    (-(1 - (0 : ℝ)) / 6) = -(1 / 6 : ℝ) := by
  norm_num

/-- Difference from the rational limit is exactly linear in the regulator. -/
theorem regularizedResidue_error (ε : ℝ) :
    (-(1 - ε) / 6) - (-(1 / 6 : ℝ)) = ε / 6 := by
  ring

end GppMu4DimensionShift

#print axioms GppMu4DimensionShift.shiftFactor_mul_boxPole
#print axioms GppMu4DimensionShift.regularizedResidue_error
