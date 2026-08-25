import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Real logarithm series kernel for the regulated scalar box

Mathlib already proves the complex Taylor series

  sum_{n>=0} z^(n+1)/(n+1) = -Log(1-z)

on the open unit disk.  This file extracts the real-axis form needed to identify the
termwise derivative of the project's local dilogarithm series.
-/

namespace GppRegulatedBoxLogSeriesKernel

/-- Real-axis shifted Taylor series for the negative logarithm. -/
theorem hasSum_pow_succ_div_succ_eq_neg_log
    {x : ℝ} (hx : |x| < 1) :
    HasSum
      (fun n : ℕ => x ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
      (-Real.log (1 - x)) := by
  have hxc : ‖(x : ℂ)‖ < 1 := by
    simpa [Complex.norm_real] using hx
  have h := Complex.hasSum_taylorSeries_neg_log' hxc
  have hre := hasSum_re h
  simpa using hre

/-- After dividing by a nonzero `x`, the derivative series is exactly
`-log(1-x)/x`. -/
theorem hasSum_pow_div_succ_eq_neg_log_div
    {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasSum
      (fun n : ℕ => x ^ n / ((n + 1 : ℕ) : ℝ))
      (-Real.log (1 - x) / x) := by
  have h := (hasSum_pow_succ_div_succ_eq_neg_log hx).div_const x
  refine h.congr ?_
  intro n
  rw [pow_succ]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hx0, hn]

/-- `tsum` form used by the eventual derivative theorem for `li2Series`. -/
theorem tsum_pow_div_succ_eq_neg_log_div
    {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    (∑' n : ℕ, x ^ n / ((n + 1 : ℕ) : ℝ)) =
      -Real.log (1 - x) / x :=
  (hasSum_pow_div_succ_eq_neg_log_div hx hx0).tsum_eq

end GppRegulatedBoxLogSeriesKernel

#print axioms GppRegulatedBoxLogSeriesKernel.hasSum_pow_succ_div_succ_eq_neg_log
#print axioms GppRegulatedBoxLogSeriesKernel.tsum_pow_div_succ_eq_neg_log_div
