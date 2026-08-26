import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Real logarithm series kernel for the regulated scalar box

The pinned Mathlib version proves the complex Taylor series for `log (1+z)` as
`Complex.hasSum_taylorSeries_log`.  Substituting `z=-x`, negating, dropping the zero
`n=0` term, and shifting the index gives the real-axis form needed to identify the
termwise derivative of the project's local dilogarithm series.
-/

namespace GppRegulatedBoxLogSeriesKernel

/-- Real-axis shifted Taylor series for the negative logarithm. -/
theorem hasSum_pow_succ_div_succ_eq_neg_log
    {x : ℝ} (hx : |x| < 1) :
    HasSum
      (fun n : ℕ => x ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
      (-Real.log (1 - x)) := by
  have hxc : ‖(-(x : ℂ))‖ < 1 := by
    simpa [Complex.norm_real] using hx
  have hlog := Complex.hasSum_taylorSeries_log hxc
  have hcomplex :
      HasSum
        (fun n : ℕ => (x : ℂ) ^ n / (n : ℂ))
        (-Complex.log (1 - (x : ℂ))) := by
    have hneg := hlog.neg
    have hterm : ∀ n : ℕ,
        -(((-1 : ℂ) ^ (n + 1) * (-(x : ℂ)) ^ n / (n : ℂ))) =
          (x : ℂ) ^ n / (n : ℂ) := by
      intro n
      have hsign :
          (-1 : ℂ) ^ (n + 1) * (-(x : ℂ)) ^ n = -((x : ℂ) ^ n) := by
        rw [neg_pow, pow_succ]
        calc
          ((-1 : ℂ) ^ n * -1) * ((-1 : ℂ) ^ n * (x : ℂ) ^ n) =
              -((((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n)) * (x : ℂ) ^ n) := by ring
          _ = -((x : ℂ) ^ n) := by
            rw [← mul_pow]
            norm_num
      rw [hsign]
      ring
    have hneg' := hneg.congr hterm
    simpa [sub_eq_add_neg] using hneg'
  have htail :
      HasSum
        (fun n : ℕ => (x : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
        (-Complex.log (1 - (x : ℂ))) := by
    apply (hasSum_nat_add_iff 1).2
    simpa using hcomplex
  have hre := hasSum_re htail
  have hx1 : x < 1 := lt_of_le_of_lt (le_abs_self x) hx
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  simpa [Complex.log_ofReal_re, hpos.le] using hre

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

/-- `tsum` form used by the derivative theorem for `li2Series`. -/
theorem tsum_pow_div_succ_eq_neg_log_div
    {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    (∑' n : ℕ, x ^ n / ((n + 1 : ℕ) : ℝ)) =
      -Real.log (1 - x) / x :=
  (hasSum_pow_div_succ_eq_neg_log_div hx hx0).tsum_eq

end GppRegulatedBoxLogSeriesKernel

#print axioms GppRegulatedBoxLogSeriesKernel.hasSum_pow_succ_div_succ_eq_neg_log
#print axioms GppRegulatedBoxLogSeriesKernel.tsum_pow_div_succ_eq_neg_log_div
