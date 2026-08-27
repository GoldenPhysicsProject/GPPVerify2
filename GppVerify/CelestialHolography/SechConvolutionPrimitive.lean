import GppVerify.CelestialHolography.SechConvolutionKernel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Log-cosh primitive for the shifted sech convolution

This is the differential layer between the pointwise hyperbolic identity in
`SechConvolutionKernel` and the eventual whole-line improper integral.  For fixed
`lambda`, the difference of two log-cosh terms differentiates to the shifted
reciprocal-cosh product multiplied by the constant channel factor
`pi * sinh (pi * lambda)`.

No improper-integral or endpoint claim is made in this file.
-/

namespace GppSechConvolutionPrimitive

open GppSechConvolutionKernel

/-- The numerator primitive whose endpoint jump produces the sech self-convolution. -/
noncomputable def logCoshDifference (lam x : ℝ) : ℝ :=
  Real.log (Real.cosh (Real.pi * x)) -
    Real.log (Real.cosh (Real.pi * (lam - x)))

/-- The first log-cosh term has derivative `pi * tanh(pi*x)`. -/
theorem hasDerivAt_log_cosh_pi_mul (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.log (Real.cosh (Real.pi * y)))
      (Real.pi * (Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x))) x := by
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * y) Real.pi x := by
    convert (hasDerivAt_const x Real.pi).mul (hasDerivAt_id x) using 1 <;> ring
  have hc : Real.cosh (Real.pi * x) ≠ 0 := (Real.cosh_pos _).ne'
  have h := ((Real.hasDerivAt_cosh (Real.pi * x)).comp x hlin).log hc
  convert h using 1
  field_simp [hc]
  ring

/-- The reflected log-cosh term has derivative `-pi * tanh(pi*(lambda-x))`. -/
theorem hasDerivAt_log_cosh_pi_shift (lam x : ℝ) :
    HasDerivAt
      (fun y : ℝ => Real.log (Real.cosh (Real.pi * (lam - y))))
      (-Real.pi *
        (Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x)))) x := by
  have hsub : HasDerivAt (fun y : ℝ => lam - y) (-1) x := by
    convert (hasDerivAt_const x lam).sub (hasDerivAt_id x) using 1 <;> ring
  have hlin : HasDerivAt (fun y : ℝ => Real.pi * (lam - y)) (-Real.pi) x := by
    convert (hasDerivAt_const x Real.pi).mul hsub using 1 <;> ring
  have hc : Real.cosh (Real.pi * (lam - x)) ≠ 0 := (Real.cosh_pos _).ne'
  have h := ((Real.hasDerivAt_cosh (Real.pi * (lam - x))).comp x hlin).log hc
  convert h using 1
  field_simp [hc]
  ring

/-- Exact primitive derivative for the shifted sech-product kernel:

`d/dx [log cosh(pi*x) - log cosh(pi*(lambda-x))]
 = pi*sinh(pi*lambda)/(cosh(pi*x) cosh(pi*(lambda-x)))`.

This is the finite-endpoint interface needed before taking the whole-line limit. -/
theorem hasDerivAt_logCoshDifference (lam x : ℝ) :
    HasDerivAt (logCoshDifference lam)
      (Real.pi * Real.sinh (Real.pi * lam) /
        (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (lam - x)))) x := by
  have h1 := hasDerivAt_log_cosh_pi_mul x
  have h2 := hasDerivAt_log_cosh_pi_shift lam x
  have h := h1.sub h2
  have hx : Real.cosh (Real.pi * x) ≠ 0 := (Real.cosh_pos _).ne'
  have hshift : Real.cosh (Real.pi * (lam - x)) ≠ 0 := (Real.cosh_pos _).ne'
  have hk := pi_shift_kernel_identity x lam hx hshift
  convert h using 1
  · rfl
  · rw [show
      Real.pi * (Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x)) -
          (-Real.pi *
            (Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x)))) =
        Real.pi *
          (Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x) +
            Real.sinh (Real.pi * (lam - x)) / Real.cosh (Real.pi * (lam - x))) by ring]
    rw [hk]
    ring

end GppSechConvolutionPrimitive

#print axioms GppSechConvolutionPrimitive.hasDerivAt_log_cosh_pi_mul
#print axioms GppSechConvolutionPrimitive.hasDerivAt_log_cosh_pi_shift
#print axioms GppSechConvolutionPrimitive.hasDerivAt_logCoshDifference
