import GppVerify.RiemannHypothesis.HeatTraceCriterion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Causal Dirichlet-heat boundary anomaly: finite-cutoff core

The causal replacement in the arithmetic heat-trace program uses the Dirichlet heat kernel
on the positive half-line and the unilateral translation by `a > 0`.  On the diagonal, the
commutator kernel has the two pieces

  g(a) - g(a + 2x),             0 < x < a,
  g(2x - a) - g(2x + a),       x >= a,

where for the heat problem `g = g_t` is the normalized Gaussian.

Before invoking trace-class theory, there is a purely one-dimensional cancellation.  If the
second integral is truncated at `R`, affine changes of variables give exactly

  T_R(a) = a g(a) - (1/2) integral_[2R-a,2R+a] g.

Thus the trace anomaly `Tr(E_t V_a - V_a E_t) = a g_t(a)` is reduced to one honest
analytic endpoint: the moving Gaussian-window integral tends to zero as `R -> infinity`.
This file formalizes the finite-cutoff identity.  It does not yet package the operators or
claim trace-classness.
-/

namespace GppCausalHeatBoundaryAnomaly

open intervalIntegral

/-- The normalized one-dimensional heat Gaussian. -/
noncomputable def heatKernelGaussian (t x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (4 * t)) / Real.sqrt (4 * Real.pi * t)

/-- Finite-cutoff diagonal integral of the causal heat/translation commutator. -/
noncomputable def truncatedBoundaryTrace (g : ℝ → ℝ) (a R : ℝ) : ℝ :=
  (∫ x in 0..a, (g a - g (a + 2 * x))) +
    ∫ x in a..R, (g (2 * x - a) - g (2 * x + a))

/-- Affine substitution for the boundary piece `g(a+2x)`. -/
theorem two_mul_integral_zero_a_add_two
    (g : ℝ → ℝ) (a : ℝ) :
    2 * (∫ x in 0..a, g (a + 2 * x)) = ∫ y in a..(3 * a), g y := by
  have h := intervalIntegral.mul_integral_comp_add_mul g 2 a (a := 0) (b := a)
  simpa [add_comm, add_left_comm, add_assoc] using h

/-- Affine substitution for `g(2x-a)` on the bulk interval. -/
theorem two_mul_integral_a_R_two_sub
    (g : ℝ → ℝ) (a R : ℝ) :
    2 * (∫ x in a..R, g (2 * x - a)) =
      ∫ y in a..(2 * R - a), g y := by
  have h := intervalIntegral.mul_integral_comp_mul_sub g 2 a (a := a) (b := R)
  simpa using h

/-- Affine substitution for `g(2x+a)` on the bulk interval. -/
theorem two_mul_integral_a_R_two_add
    (g : ℝ → ℝ) (a R : ℝ) :
    2 * (∫ x in a..R, g (2 * x + a)) =
      ∫ y in (3 * a)..(2 * R + a), g y := by
  have h := intervalIntegral.mul_integral_comp_mul_add g 2 a (a := a) (b := R)
  simpa using h

/-- **Exact finite-cutoff boundary cancellation.**  The only remainder is a moving window
of the underlying kernel at the far endpoint. -/
theorem truncatedBoundaryTrace_eq_boundary_minus_tail
    (g : ℝ → ℝ) (a R : ℝ) :
    truncatedBoundaryTrace g a R =
      a * g a - (1 / 2 : ℝ) * (∫ y in (2 * R - a)..(2 * R + a), g y) := by
  unfold truncatedBoundaryTrace
  rw [integral_sub, integral_sub]
  have hconst : (∫ _x in (0 : ℝ)..a, g a) = a * g a := by
    simp [intervalIntegral.integral_const]
    ring
  rw [hconst]
  have h1 := two_mul_integral_zero_a_add_two g a
  have h2 := two_mul_integral_a_R_two_sub g a R
  have h3 := two_mul_integral_a_R_two_add g a R
  have hadd1 :
      (∫ y in a..(3 * a), g y) + (∫ y in (3 * a)..(2 * R + a), g y) =
        ∫ y in a..(2 * R + a), g y :=
    integral_add_adjacent_intervals _ _ _
  have hadd2 :
      (∫ y in a..(2 * R - a), g y) +
        (∫ y in (2 * R - a)..(2 * R + a), g y) =
        ∫ y in a..(2 * R + a), g y :=
    integral_add_adjacent_intervals _ _ _
  linarith

/-- Specialization of the finite-cutoff identity to the normalized heat Gaussian. -/
theorem truncatedHeatBoundaryTrace_eq
    (t a R : ℝ) :
    truncatedBoundaryTrace (heatKernelGaussian t) a R =
      a * heatKernelGaussian t a -
        (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), heatKernelGaussian t y) := by
  exact truncatedBoundaryTrace_eq_boundary_minus_tail (heatKernelGaussian t) a R

end GppCausalHeatBoundaryAnomaly

#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_zero_a_add_two
#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_a_R_two_sub
#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_a_R_two_add
#print axioms GppCausalHeatBoundaryAnomaly.truncatedBoundaryTrace_eq_boundary_minus_tail
#print axioms GppCausalHeatBoundaryAnomaly.truncatedHeatBoundaryTrace_eq
