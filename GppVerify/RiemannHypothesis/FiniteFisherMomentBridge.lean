import Mathlib.Tactic

/-!
# Finite Fisher moment bridge

This module isolates the scalar algebra sitting between the finite-support
Vandermonde energy and the two-parameter Fisher determinant for sufficient
statistics `X` and `X^2`.

Once the ordered squared-Vandermonde energy has been expanded into raw moments,
the covariance determinant identity is pure polynomial algebra.  This file
formalizes exactly that algebraic bridge, leaving the finite-sum expansion as the
only remaining arbitrary-support step.
-/

namespace GppFiniteFisherMomentBridge

/-- Determinant of the covariance matrix of `X` and `X^2`, written in terms of
raw moments `m₁,...,m₄` for normalized mass. -/
def fisherDet (m1 m2 m3 m4 : ℝ) : ℝ :=
  (m2 - m1 ^ 2) * (m4 - m2 ^ 2) - (m3 - m1 * m2) ^ 2

/-- The cubic moment discriminant produced by expanding an ordered squared
Vandermonde energy.  The `m0` argument is the total mass. -/
def momentDiscriminant (m0 m1 m2 m3 m4 : ℝ) : ℝ :=
  6 * (m0 * m2 * m4 + 2 * m1 * m2 * m3 - m2 ^ 3 - m0 * m3 ^ 2 - m1 ^ 2 * m4)

/-- At normalized total mass `m₀ = 1`, the moment discriminant is exactly six
times the Fisher covariance determinant. -/
theorem momentDiscriminant_one_eq_six_fisherDet
    (m1 m2 m3 m4 : ℝ) :
    momentDiscriminant 1 m1 m2 m3 m4 = 6 * fisherDet m1 m2 m3 m4 := by
  unfold momentDiscriminant fisherDet
  ring

/-- Equivalent division-free form useful for composing with an ordered-energy
identity. -/
theorem six_fisherDet_eq_momentDiscriminant_one
    (m1 m2 m3 m4 : ℝ) :
    6 * fisherDet m1 m2 m3 m4 = momentDiscriminant 1 m1 m2 m3 m4 := by
  symm
  exact momentDiscriminant_one_eq_six_fisherDet m1 m2 m3 m4

end GppFiniteFisherMomentBridge

#print axioms GppFiniteFisherMomentBridge.momentDiscriminant_one_eq_six_fisherDet
#print axioms GppFiniteFisherMomentBridge.six_fisherDet_eq_momentDiscriminant_one
