import GppVerify.QuantumGravity.SinhZetaBridge
import Mathlib.Tactic

/-!
# Odd-mode exponential sum for the chamber Levy kernel

This module formalizes the elementary summation step behind the odd-Gamma-mode
representation of the continuous chamber semigroup.  For `y > 0`, the odd rates
`(2n+1) * pi` satisfy

  sum_n 2 a exp (-(2n+1) pi y) = a / sinh(pi y).

Dividing by `y` gives the pointwise continuous Levy density

  a / (y sinh(pi y)).

This is only the exact odd-mode-to-hyperbolic-kernel summation.  It does not assert
existence of a Levy process, a Levy--Khintchine integral, or identification with the
explicit Gamma-square spatial density; those remain separate analytic steps.
-/

namespace GppOddModeLevyKernel

open Real

/-- The unscaled odd exponential series is exactly the reciprocal `sinh` kernel. -/
theorem tsum_two_exp_odd {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, 2 * Real.exp (-(2 * (n : ℝ) + 1) * t)) = 1 / Real.sinh t := by
  have h := GppZetaBridge.sinh_summand_eq (t := t) ht (1 : ℝ)
  simpa using h.symm

/-- Scaling the odd exponential modes by `a` preserves the closed `sinh` sum. -/
theorem tsum_scaled_two_exp_odd (a : ℝ) {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, 2 * a * Real.exp (-(2 * (n : ℝ) + 1) * t)) =
      a / Real.sinh t := by
  calc
    (∑' n : ℕ, 2 * a * Real.exp (-(2 * (n : ℝ) + 1) * t)) =
        a * (∑' n : ℕ, 2 * Real.exp (-(2 * (n : ℝ) + 1) * t)) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          ring
    _ = a * (1 / Real.sinh t) := by rw [tsum_two_exp_odd ht]
    _ = a / Real.sinh t := by ring

/-- At the chamber rates `(2n+1) * pi`, the odd-mode numerator sums to
`a / sinh(pi y)` for every `y > 0`. -/
theorem tsum_chamber_odd_rates (a : ℝ) {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ,
      2 * a * Real.exp (-((2 * (n : ℝ) + 1) * Real.pi) * y)) =
      a / Real.sinh (Real.pi * y) := by
  have ht : 0 < Real.pi * y := mul_pos Real.pi_pos hy
  simpa [mul_assoc] using tsum_scaled_two_exp_odd a ht

/-- Dividing the summed odd-mode numerator by `y` gives the pointwise continuous
chamber Levy density `a / (y * sinh(pi y))`. -/
theorem chamber_levy_density_from_odd_modes (a : ℝ) {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ,
      2 * a * Real.exp (-((2 * (n : ℝ) + 1) * Real.pi) * y)) / y =
      a / (y * Real.sinh (Real.pi * y)) := by
  rw [tsum_chamber_odd_rates a hy]
  field_simp

end GppOddModeLevyKernel

#print axioms GppOddModeLevyKernel.tsum_two_exp_odd
#print axioms GppOddModeLevyKernel.tsum_scaled_two_exp_odd
#print axioms GppOddModeLevyKernel.tsum_chamber_odd_rates
#print axioms GppOddModeLevyKernel.chamber_levy_density_from_odd_modes
