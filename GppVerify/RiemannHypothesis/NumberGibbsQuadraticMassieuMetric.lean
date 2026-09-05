import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuPositiveDefinite
import Mathlib.Tactic

/-!
# Strict positive-definite Massieu/Fisher metric

The confined two-parameter number-Gibbs family already has a strictly positive
leading covariance response and strictly positive covariance determinant.  This
file packages those certified Sylvester inequalities as strict positivity of the
full quadratic form on every nonzero tangent direction.
-/

namespace GppNumberGibbsQuadraticMassieuMetric

open GppNumberGibbsQuadraticMassieuHessian
open GppNumberGibbsQuadraticMassieuFisherIdentification
open GppNumberGibbsQuadraticMassieuPositiveDefinite

/-- The exact Massieu/Fisher covariance matrix is strictly positive definite on
the quadratically confined domain.  Equivalently, every nonzero tangent vector
has strictly positive fluctuation norm. -/
theorem massieuFisher_quadratic_form_pos
    (β : ℝ) {η : ℝ} (hη : 0 < η)
    (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < fisherBB β η * a ^ 2 +
        2 * fisherBE β η * a * b +
        fisherEE β η * b ^ 2 := by
  let A := fisherBB β η
  let B := fisherBE β η
  let C := fisherEE β η
  have hA : 0 < A := by
    simpa [A] using fisherBB_pos β hη
  have hdet : 0 < A * C - B ^ 2 := by
    simpa [A, B, C, massieuFisherDet] using massieuFisherDet_pos β hη
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by
      rcases hab with ha | hb'
      · exact ha
      · exact False.elim (hb' hb)
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    simp [A, B, C, hb]
    exact mul_pos hA ha2
  · have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    have hdetb : 0 < (A * C - B ^ 2) * b ^ 2 := mul_pos hdet hb2
    have hsquare : 0 ≤ (A * a + B * b) ^ 2 := sq_nonneg (A * a + B * b)
    have hmul :
        0 < A * (A * a ^ 2 + 2 * B * a * b + C * b ^ 2) := by
      nlinarith
    have hq : 0 < A * a ^ 2 + 2 * B * a * b + C * b ^ 2 := by
      nlinarith
    simpa [A, B, C] using hq

end GppNumberGibbsQuadraticMassieuMetric

#print axioms GppNumberGibbsQuadraticMassieuMetric.massieuFisher_quadratic_form_pos
