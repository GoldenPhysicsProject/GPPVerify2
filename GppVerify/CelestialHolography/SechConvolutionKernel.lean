import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Elementary kernel behind the sech self-convolution

This is the pointwise hyperbolic identity used in the Discovery2 elementary proof of
`sech(pi * ·) * sech(pi * ·)` convolution.  The improper integral and endpoint limits
are intentionally left for the next layer.
-/

namespace GppSechConvolutionKernel

/-- Addition-law form of the product of two reciprocal coshes. -/
theorem reciprocal_cosh_product_identity
    (A B : ℝ)
    (hA : Real.cosh A ≠ 0)
    (hB : Real.cosh B ≠ 0) :
    Real.sinh A / Real.cosh A + Real.sinh B / Real.cosh B =
      Real.sinh (A + B) / (Real.cosh A * Real.cosh B) := by
  rw [Real.sinh_add]
  field_simp [hA, hB]
  ring

/-- Specialized kernel identity for `A = pi*x`, `B = pi*(lambda-x)`.
It is the algebraic heart of the elementary self-convolution proof. -/
theorem pi_shift_kernel_identity
    (x λ : ℝ)
    (hx : Real.cosh (Real.pi * x) ≠ 0)
    (hshift : Real.cosh (Real.pi * (λ - x)) ≠ 0) :
    Real.sinh (Real.pi * x) / Real.cosh (Real.pi * x) +
      Real.sinh (Real.pi * (λ - x)) / Real.cosh (Real.pi * (λ - x)) =
      Real.sinh (Real.pi * λ) /
        (Real.cosh (Real.pi * x) * Real.cosh (Real.pi * (λ - x))) := by
  have h := reciprocal_cosh_product_identity
    (Real.pi * x) (Real.pi * (λ - x)) hx hshift
  convert h using 1 <;> ring

end GppSechConvolutionKernel

#print axioms GppSechConvolutionKernel.reciprocal_cosh_product_identity
#print axioms GppSechConvolutionKernel.pi_shift_kernel_identity
