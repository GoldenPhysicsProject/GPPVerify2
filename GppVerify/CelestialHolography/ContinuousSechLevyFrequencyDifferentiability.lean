import GppVerify.CelestialHolography.ContinuousSechLevyFrequencyDerivativeMajorant

/-!
# Frequency differentiability of the continuous sech Lévy kernel

For fixed spatial coordinate `x`, the compensated kernel

  K_c(t,x) = (1 - cos(t x)) nu_c(x)

is differentiable in the frequency parameter `t`, with exact derivative

  D_c(t,x) = x sin(t x) nu_c(x).

The parameter-uniform Cauchy majorant from
`ContinuousSechLevyFrequencyDerivativeMajorant` also implies that, for every
fixed frequency, the derivative kernel is genuinely Lebesgue integrable in `x`.
This is the final integrability input before a dominated differentiation theorem
can exchange the frequency derivative with the spatial integral.
-/

namespace GppContinuousSechLevyFrequencyDifferentiability

open MeasureTheory
open GppContinuousSechLevyKernel
open GppContinuousSechLevyFrequencyDerivative
open GppContinuousSechLevyFrequencyDerivativeMajorant

/-- For every fixed spatial coordinate, the compensated Lévy kernel has the
expected frequency derivative.  No positivity or integrability assumption is
needed for this pointwise statement. -/
theorem hasDerivAt_compensatedLevyKernel_frequency (c x t : ℝ) :
    HasDerivAt (fun u : ℝ => compensatedLevyKernel c u x)
      (frequencyDerivativeKernel c t x) t := by
  unfold compensatedLevyKernel frequencyDerivativeKernel
  have hlin : HasDerivAt (fun u : ℝ => u * x) x t := by
    simpa using (hasDerivAt_id t).mul_const x
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (u * x))
      (-Real.sin (t * x) * x) t :=
    (Real.hasDerivAt_cos (t * x)).comp t hlin
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have hsub : HasDerivAt (fun u : ℝ => 1 - Real.cos (u * x))
      (Real.sin (t * x) * x) t := by
    convert hone.sub hcos using 1 <;> ring
  convert hsub.mul_const (levyDensity c x) using 1 <;> ring

/-- For fixed chamber parameter and frequency, the derivative kernel is Borel measurable
as a function of the spatial variable. -/
theorem measurable_frequencyDerivativeKernel (c t : ℝ) :
    Measurable (fun x : ℝ => frequencyDerivativeKernel c t x) := by
  unfold frequencyDerivativeKernel levyDensity
  fun_prop

/-- Hence the fixed-frequency derivative kernel is strongly measurable. -/
theorem aestronglyMeasurable_frequencyDerivativeKernel (c t : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => frequencyDerivativeKernel c t x) :=
  (measurable_frequencyDerivativeKernel c t).aestronglyMeasurable

/-- For every nonnegative chamber parameter and every fixed frequency, the derivative
kernel is Lebesgue integrable on the real line.  The proof takes the compact frequency
window `T = |t|` in the certified Cauchy majorant. -/
theorem integrable_frequencyDerivativeKernel {c t : ℝ} (hc : 0 ≤ c) :
    Integrable (fun x : ℝ => frequencyDerivativeKernel c t x) := by
  let T : ℝ := |t|
  have hg : Integrable (fun x : ℝ =>
      frequencyDerivativeCauchyConstant c T * (1 + x ^ 2)⁻¹) :=
    integrable_frequencyDerivativeCauchyMajorant c T
  refine Integrable.mono' hg
    (aestronglyMeasurable_frequencyDerivativeKernel c t) ?_
  filter_upwards with x
  have hmaj := abs_frequencyDerivativeKernel_le_cauchy
    (c := c) (T := T) (t := t) (x := x) hc (le_refl |t|)
  have hT : 0 ≤ T := abs_nonneg t
  have hgap : 0 < 1 - Real.exp (-(2 * Real.pi)) := by
    have : Real.exp (-(2 * Real.pi)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hC : 0 ≤ frequencyDerivativeCauchyConstant c T := by
    unfold frequencyDerivativeCauchyConstant
    positivity
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC hinv)]
  exact hmaj

end GppContinuousSechLevyFrequencyDifferentiability

#print axioms GppContinuousSechLevyFrequencyDifferentiability.hasDerivAt_compensatedLevyKernel_frequency
#print axioms GppContinuousSechLevyFrequencyDifferentiability.measurable_frequencyDerivativeKernel
#print axioms GppContinuousSechLevyFrequencyDifferentiability.integrable_frequencyDerivativeKernel
