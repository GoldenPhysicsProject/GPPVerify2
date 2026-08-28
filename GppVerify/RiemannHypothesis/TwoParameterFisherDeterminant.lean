import Mathlib.Tactic

/-!
# Two-parameter Fisher determinant algebra

For sufficient statistics `X` and `X^2`, the 2x2 covariance determinant is exactly
the determinant of the 3x3 moment Gram matrix of `(1,X,X^2)`.  This is the
algebraic core of the two-parameter prime-gas fluctuation geometry; positivity
and the Vandermonde/Cauchy-Binet expansion are separate measure-theoretic layers.
-/

namespace GppTwoParameterFisherDeterminant

/-- The covariance determinant of `(X,X^2)` equals the determinant of the moment
Gram matrix `E[(1,X,X^2)^T(1,X,X^2)]`, written in terms of moments `m₁,...,m₄`. -/
theorem covariance_det_eq_moment_gram_det
    (m1 m2 m3 m4 : ℝ) :
    (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 =
      (m2*m4 - m3^2) - m1*(m1*m4 - m2*m3) + m2*(m1*m3 - m2^2) := by
  ring

end GppTwoParameterFisherDeterminant

#print axioms GppTwoParameterFisherDeterminant.covariance_det_eq_moment_gram_det
