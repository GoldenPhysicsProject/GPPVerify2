import Mathlib.Tactic

/-!
# Generic massive-vector state-sum defect algebra

The exact symbolic five-dimensional Yang--Mills audit found that the threshold
identity `C_V = 3 C_S` is not a generic cut identity.  In the rational kinematic
parameters `r,t`, its same-helicity defect is

  4 (r^2 - 1)^2 (1+t^2)^2 / (r^2+t^2)^2.

This file certifies only the algebraic positivity and threshold consequences of
that rational expression.  The identification of `C_V` and `C_S` with explicit
sewn tree amplitudes is deliberately kept as an explicit hypothesis below; this
module does not replace the still-required Yang--Mills tree-current derivation.
-/

namespace GppMassiveVectorGenericDefect

/-- Exact rational defect found by the generic symbolic state-sum audit. -/
def sameHelicityDefect (r t : ℝ) : ℝ :=
  4 * (r ^ 2 - 1) ^ 2 * (1 + t ^ 2) ^ 2 / (r ^ 2 + t ^ 2) ^ 2

/-- The generic correction is manifestly nonnegative. -/
theorem sameHelicityDefect_nonneg (r t : ℝ) :
    0 ≤ sameHelicityDefect r t := by
  unfold sameHelicityDefect
  positivity

/-- The old `3:1` relation is recovered exactly on the threshold slice `r=1`. -/
@[simp] theorem sameHelicityDefect_one (t : ℝ) :
    sameHelicityDefect 1 t = 0 := by
  simp [sameHelicityDefect]

/-- The opposite threshold orientation `r=-1` has the same vanishing defect. -/
@[simp] theorem sameHelicityDefect_neg_one (t : ℝ) :
    sameHelicityDefect (-1) t = 0 := by
  simp [sameHelicityDefect]

/-- If an explicit Yang--Mills sewing calculation identifies its vector/scalar
state-sum difference with the audited rational defect, then the vector sewing is
at least three scalar sewings.  The amplitude identification remains an explicit
input rather than being smuggled into the algebraic theorem. -/
theorem vector_ge_three_scalar_of_defect
    {Cv Cs r t : ℝ}
    (hdef : Cv - 3 * Cs = sameHelicityDefect r t) :
    3 * Cs ≤ Cv := by
  have h := sameHelicityDefect_nonneg r t
  linarith

/-- On the threshold slice, the same explicit identification reduces exactly to
`C_V = 3 C_S`. -/
theorem vector_eq_three_scalar_at_threshold
    {Cv Cs t : ℝ}
    (hdef : Cv - 3 * Cs = sameHelicityDefect 1 t) :
    Cv = 3 * Cs := by
  simpa using hdef

end GppMassiveVectorGenericDefect

#print axioms GppMassiveVectorGenericDefect.sameHelicityDefect_nonneg
#print axioms GppMassiveVectorGenericDefect.vector_ge_three_scalar_of_defect
#print axioms GppMassiveVectorGenericDefect.vector_eq_three_scalar_at_threshold
