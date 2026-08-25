import GppVerify.CelestialHolography.ScalarBoxRegulatorBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
# Elementary logarithm bounds for the scalar-box regulator

Mathlib already proves a sharp local Taylor bound for the complex logarithm.  Restricting
that theorem to a positive real segment yields the real estimate needed for the
regulated scalar-box endpoint errors, without introducing a separate logarithm series.
-/

namespace GppScalarBoxLogBounds

/-- For `0 ≤ x ≤ 1/2`, the real logarithm obeys the uniform local estimate
`|log(1-x)| ≤ (3/2)x`. -/
theorem abs_log_one_sub_le_three_halves
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ (3 / 2 : ℝ) * x := by
  have hz : ‖(-(x : ℂ))‖ ≤ (1 / 2 : ℝ) := by
    simpa [Complex.norm_real, abs_of_nonneg hx0] using hx
  have h := Complex.norm_log_one_add_half_le_self hz
  have hpos : 0 ≤ 1 - x := by linarith
  have hlog : Complex.log ((1 - x : ℝ) : ℂ) = (Real.log (1 - x) : ℂ) := by
    simpa using Complex.ofReal_log hpos
  have hone : (1 : ℂ) + (-(x : ℂ)) = ((1 - x : ℝ) : ℂ) := by norm_num
  rw [hone, hlog] at h
  simpa [Complex.norm_real, abs_of_nonneg hx0] using h

/-- A convenient squared consequence used for the lower endpoint remainder. -/
theorem half_log_one_sub_sq_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 / 2 : ℝ) * (Real.log (1 - x)) ^ 2 ≤ (9 / 8 : ℝ) * x ^ 2 := by
  have h := abs_log_one_sub_le_three_halves hx0 hx
  have hsquare : (Real.log (1 - x)) ^ 2 ≤ ((3 / 2 : ℝ) * x) ^ 2 := by
    nlinarith [sq_nonneg (|Real.log (1 - x)| - (3 / 2 : ℝ) * x)]
  nlinarith

end GppScalarBoxLogBounds

#print axioms GppScalarBoxLogBounds.abs_log_one_sub_le_three_halves
#print axioms GppScalarBoxLogBounds.half_log_one_sub_sq_le
