import Mathlib

/-!
# Continuous sech Lévy kernel algebra

This file isolates the exact algebraic kernel suggested by the Lévy–Khintchine
representation of the continuous chamber transform

  `Phi_c(t) = sech(t/2)^(2c)`.

For `x ≠ 0`, the candidate symmetric Lévy density is

  `nu_c(x) = c / (|x| * sinh(pi * |x|))`.

The analytic identity

  `log Phi_c(t) = ∫ (cos(t*x)-1) nu_c(x) dx`

is deliberately *not* asserted here.  The present file formalizes only the
parameter-additive and reflection symmetries of the candidate density and its
pointwise Lévy exponent kernel.  These are reusable prerequisites for a later
integrability and integral-identification theorem.
-/

namespace GppContinuousSechLevyKernel

/-- Candidate symmetric Lévy density for continuous chamber parameter `c`. -/
noncomputable def levyDensity (c x : ℝ) : ℝ :=
  c / (|x| * Real.sinh (Real.pi * |x|))

/-- Pointwise symmetric Lévy exponent kernel. -/
noncomputable def levyExponentKernel (c t x : ℝ) : ℝ :=
  (Real.cos (t * x) - 1) * levyDensity c x

/-- The candidate Lévy density is exactly additive in the chamber parameter. -/
theorem levyDensity_add (c d x : ℝ) :
    levyDensity (c + d) x = levyDensity c x + levyDensity d x := by
  unfold levyDensity
  exact add_div c d (|x| * Real.sinh (Real.pi * |x|))

/-- The zero chamber parameter has zero candidate Lévy density. -/
theorem levyDensity_zero (x : ℝ) : levyDensity 0 x = 0 := by
  simp [levyDensity]

/-- The candidate Lévy density is spatially even. -/
theorem levyDensity_neg (c x : ℝ) : levyDensity c (-x) = levyDensity c x := by
  simp [levyDensity]

/-- The pointwise Lévy exponent kernel is additive in the chamber parameter. -/
theorem levyExponentKernel_add (c d t x : ℝ) :
    levyExponentKernel (c + d) t x =
      levyExponentKernel c t x + levyExponentKernel d t x := by
  unfold levyExponentKernel
  rw [levyDensity_add]
  ring

/-- Frequency reflection leaves the pointwise Lévy exponent kernel unchanged. -/
theorem levyExponentKernel_neg_frequency (c t x : ℝ) :
    levyExponentKernel c (-t) x = levyExponentKernel c t x := by
  unfold levyExponentKernel
  rw [show (-t) * x = -(t * x) by ring, Real.cos_neg]

/-- Spatial reflection leaves the pointwise Lévy exponent kernel unchanged. -/
theorem levyExponentKernel_neg_space (c t x : ℝ) :
    levyExponentKernel c t (-x) = levyExponentKernel c t x := by
  unfold levyExponentKernel
  rw [levyDensity_neg]
  rw [show t * (-x) = -(t * x) by ring, Real.cos_neg]

end GppContinuousSechLevyKernel

#print axioms GppContinuousSechLevyKernel.levyDensity_add
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_add
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_neg_frequency
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_neg_space
