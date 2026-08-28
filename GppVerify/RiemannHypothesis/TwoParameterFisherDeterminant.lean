import Mathlib.Tactic

/-!
# Two-parameter Fisher determinant algebra

For sufficient statistics `X` and `X^2`, the 2x2 covariance determinant is exactly
the determinant of the 3x3 moment Gram matrix of `(1,X,X^2)`.  For an exactly
normalized three-point support it is moreover the positive weight product times
the squared Vandermonde.  These are algebraic cores of the two-parameter prime-gas
fluctuation geometry; the infinite Gibbs-family and measure-theoretic layers remain
separate.
-/

namespace GppTwoParameterFisherDeterminant

/-- The covariance determinant of `(X,X^2)` equals the determinant of the moment
Gram matrix `E[(1,X,X^2)^T(1,X,X^2)]`, written in terms of moments `m₁,...,m₄`. -/
theorem covariance_det_eq_moment_gram_det
    (m1 m2 m3 m4 : ℝ) :
    (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 =
      (m2*m4 - m3^2) - m1*(m1*m4 - m2*m3) + m2*(m1*m3 - m2^2) := by
  ring

/-- For a normalized three-point distribution, the covariance determinant of
`(X,X^2)` is exactly the weight product times the squared Vandermonde. -/
theorem three_point_covariance_det_eq_vandermonde
    (p q r x y z : ℝ) (hnorm : p + q + r = 1) :
    let m1 := p*x + q*y + r*z
    let m2 := p*x^2 + q*y^2 + r*z^2
    let m3 := p*x^3 + q*y^3 + r*z^3
    let m4 := p*x^4 + q*y^4 + r*z^4
    (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 =
      p*q*r*(x-y)^2*(x-z)^2*(y-z)^2 := by
  dsimp
  have hr : r = 1 - p - q := by linarith
  rw [hr]
  ring

/-- The three-point Fisher determinant is strictly positive for positive weights
and pairwise distinct support points. -/
theorem three_point_covariance_det_pos
    (p q r x y z : ℝ)
    (hnorm : p + q + r = 1)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    let m1 := p*x + q*y + r*z
    let m2 := p*x^2 + q*y^2 + r*z^2
    let m3 := p*x^3 + q*y^3 + r*z^3
    let m4 := p*x^4 + q*y^4 + r*z^4
    0 < (m2 - m1^2) * (m4 - m2^2) - (m3 - m1*m2)^2 := by
  dsimp
  rw [three_point_covariance_det_eq_vandermonde p q r x y z hnorm]
  have hxy2 : 0 < (x-y)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hxy)
  have hxz2 : 0 < (x-z)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hxz)
  have hyz2 : 0 < (y-z)^2 := by
    rw [pow_two]
    exact mul_self_pos.mpr (sub_ne_zero.mpr hyz)
  positivity

end GppTwoParameterFisherDeterminant

#print axioms GppTwoParameterFisherDeterminant.covariance_det_eq_moment_gram_det
#print axioms GppTwoParameterFisherDeterminant.three_point_covariance_det_eq_vandermonde
#print axioms GppTwoParameterFisherDeterminant.three_point_covariance_det_pos
