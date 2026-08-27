import GppVerify.CelestialHolography.SechConvolutionPrimitive
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Endpoint limits for the shifted sech-convolution primitive

This file converts the quantitative remainder bounds from
`SechConvolutionPrimitive` into genuine endpoint limits.  The right endpoint is
proved first; the left endpoint is its mirrored companion and is kept separate so
CI can discriminate the filter algebra cleanly.
-/

namespace GppSechConvolutionEndpoints

open Filter
open GppSechConvolutionPrimitive

/-- The first log-cosh remainder vanishes as `x → +∞`. -/
theorem logCoshRemainder_pi_mul_tendsto_atTop :
    Tendsto (fun x : ℝ => logCoshRemainder (Real.pi * x)) atTop (nhds 0) := by
  have hlin : Tendsto (fun x : ℝ => (2 * Real.pi) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hupper :
      Tendsto (fun x : ℝ => Real.exp (-((2 * Real.pi) * x))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro x
    exact logCoshRemainder_nonneg (Real.pi * x)
  · intro x
    calc
      logCoshRemainder (Real.pi * x)
          ≤ Real.exp (-2 * |Real.pi * x|) := logCoshRemainder_le_exp _
      _ ≤ Real.exp (-((2 * Real.pi) * x)) := by
        apply Real.exp_le_exp.mpr
        have habs : Real.pi * x ≤ |Real.pi * x| := le_abs_self _
        linarith

/-- The reflected remainder also vanishes as `x → +∞`. -/
theorem logCoshRemainder_pi_shift_tendsto_atTop (lam : ℝ) :
    Tendsto (fun x : ℝ => logCoshRemainder (Real.pi * (lam - x))) atTop (nhds 0) := by
  have hlin0 : Tendsto (fun x : ℝ => (2 * Real.pi) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hlin :
      Tendsto (fun x : ℝ => (2 * Real.pi) * x + (-(2 * Real.pi * lam))) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hlin0
  have hupper0 :
      Tendsto
        (fun x : ℝ => Real.exp (-((2 * Real.pi) * x + (-(2 * Real.pi * lam)))))
        atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hupper :
      Tendsto (fun x : ℝ => Real.exp (-((2 * Real.pi) * (x - lam))))
        atTop (nhds 0) := by
    simpa [mul_sub] using hupper0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro x
    exact logCoshRemainder_nonneg (Real.pi * (lam - x))
  · intro x
    calc
      logCoshRemainder (Real.pi * (lam - x))
          ≤ Real.exp (-2 * |Real.pi * (lam - x)|) := logCoshRemainder_le_exp _
      _ ≤ Real.exp (-((2 * Real.pi) * (x - lam))) := by
        apply Real.exp_le_exp.mpr
        have habs0 : -(Real.pi * (lam - x)) ≤ |Real.pi * (lam - x)| := neg_le_abs _
        have habs : Real.pi * (x - lam) ≤ |Real.pi * (lam - x)| := by
          rw [show Real.pi * (x - lam) = -(Real.pi * (lam - x)) by ring]
          exact habs0
        linarith

/-- **Right endpoint of the log-cosh primitive.** -/
theorem logCoshDifference_tendsto_atTop (lam : ℝ) :
    Tendsto (logCoshDifference lam) atTop (nhds (Real.pi * lam)) := by
  have h1 := logCoshRemainder_pi_mul_tendsto_atTop
  have h2 := logCoshRemainder_pi_shift_tendsto_atTop lam
  have hrem :
      Tendsto
        (fun x : ℝ => logCoshRemainder (Real.pi * x) -
          logCoshRemainder (Real.pi * (lam - x))) atTop (nhds 0) := by
    simpa using h1.sub h2
  have heq :
      (fun x : ℝ => logCoshDifference lam x - Real.pi * lam) =ᶠ[atTop]
        (fun x : ℝ => logCoshRemainder (Real.pi * x) -
          logCoshRemainder (Real.pi * (lam - x))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop lam] with x hx0 hxlam
    exact logCoshDifference_right_remainder hx0 hxlam
  have hzero :
      Tendsto (fun x : ℝ => logCoshDifference lam x - Real.pi * lam)
        atTop (nhds 0) :=
    hrem.congr' heq.symm
  have hadd := hzero.add_const (Real.pi * lam)
  simpa using hadd

end GppSechConvolutionEndpoints

#print axioms GppSechConvolutionEndpoints.logCoshRemainder_pi_mul_tendsto_atTop
#print axioms GppSechConvolutionEndpoints.logCoshRemainder_pi_shift_tendsto_atTop
#print axioms GppSechConvolutionEndpoints.logCoshDifference_tendsto_atTop
