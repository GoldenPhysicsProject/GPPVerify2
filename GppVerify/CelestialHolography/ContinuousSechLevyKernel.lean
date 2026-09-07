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
parameter-additive, reflection, and pointwise sign properties of the candidate
density and its Lévy exponent kernel.  These are reusable prerequisites for a
later Lévy-integrability and integral-identification theorem.

Important analytic boundary: `nu_c(x)` behaves like `c / (pi * x^2)` at the
origin, so the density itself is not locally integrable there for `c > 0`.
The correct target is the Lévy condition for `(1 ∧ x^2) * nu_c(x)`, or,
equivalently for the exponent calculation, local integrability after the
quadratic cancellation in `1 - cos(t*x)`.
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

/-- Away from the origin, a positive chamber parameter gives a strictly positive Lévy density. -/
theorem levyDensity_pos {c x : ℝ} (hc : 0 < c) (hx : x ≠ 0) :
    0 < levyDensity c x := by
  unfold levyDensity
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hsinh : 0 < Real.sinh (Real.pi * |x|) := by
    exact Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hxabs)
  exact div_pos hc (mul_pos hxabs hsinh)

/-- Away from the origin, a nonnegative chamber parameter gives a nonnegative Lévy density. -/
theorem levyDensity_nonneg {c x : ℝ} (hc : 0 ≤ c) (hx : x ≠ 0) :
    0 ≤ levyDensity c x := by
  unfold levyDensity
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hsinh : 0 < Real.sinh (Real.pi * |x|) := by
    exact Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hxabs)
  exact div_nonneg hc (le_of_lt (mul_pos hxabs hsinh))

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

/-- For nonnegative chamber parameter, the pointwise Lévy exponent kernel is nonpositive away from zero. -/
theorem levyExponentKernel_nonpos {c t x : ℝ} (hc : 0 ≤ c) (hx : x ≠ 0) :
    levyExponentKernel c t x ≤ 0 := by
  unfold levyExponentKernel
  have hcos : Real.cos (t * x) - 1 ≤ 0 := sub_nonpos.mpr (Real.cos_le_one (t * x))
  have hnu : 0 ≤ levyDensity c x := levyDensity_nonneg hc hx
  exact mul_nonpos_of_nonpos_of_nonneg hcos hnu

end GppContinuousSechLevyKernel

#print axioms GppContinuousSechLevyKernel.levyDensity_add
#print axioms GppContinuousSechLevyKernel.levyDensity_pos
#print axioms GppContinuousSechLevyKernel.levyDensity_nonneg
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_add
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_neg_frequency
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_neg_space
#print axioms GppContinuousSechLevyKernel.levyExponentKernel_nonpos
