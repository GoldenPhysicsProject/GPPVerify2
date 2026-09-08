import GppVerify.CelestialHolography.ContinuousSechLevyFrequencyDerivativeMajorant

/-!
# Pointwise frequency differentiability of the continuous sech Lévy kernel

For fixed spatial coordinate `x`, the compensated kernel

  K_c(t,x) = (1 - cos(t x)) nu_c(x)

is differentiable in the frequency parameter `t`, with exact derivative

  D_c(t,x) = x sin(t x) nu_c(x).

This file records only the pointwise calculus statement.  Differentiating the
Lebesgue integral in `x` is a separate step and uses the parameter-uniform
integrable Cauchy majorant from
`ContinuousSechLevyFrequencyDerivativeMajorant`.
-/

namespace GppContinuousSechLevyFrequencyDifferentiability

open GppContinuousSechLevyKernel
open GppContinuousSechLevyFrequencyDerivative

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

end GppContinuousSechLevyFrequencyDifferentiability

#print axioms GppContinuousSechLevyFrequencyDifferentiability.hasDerivAt_compensatedLevyKernel_frequency
