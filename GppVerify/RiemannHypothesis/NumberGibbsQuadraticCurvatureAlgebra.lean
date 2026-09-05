import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuMetric
import Mathlib.Tactic

/-!
# Algebraic curvature reduction for the quadratic number-Gibbs metric

This file isolates the exact centered-moment algebra discovered for the
quadratically confined two-parameter Gibbs family.  It deliberately proves only
the polynomial/rational identities and the resulting conditional curvature
bound.  The analytic identification of these symbols with countable Gibbs
centered moments, and the nonnegativity of the degree-three moment Gram
determinant, remain separate semantic obligations.
-/

namespace GppNumberGibbsQuadraticCurvatureAlgebra

/-- Determinant of the covariance metric of the sufficient statistics `X` and
`X^2`, expressed in centered moments. -/
def metricDet (m2 m3 m4 : ℝ) : ℝ :=
  m2 * m4 - m3 ^ 2 - m2 ^ 3

/-- Determinant of the centered degree-three moment Gram matrix, expanded as a
polynomial in centered moments `m₂,...,m₆`. -/
def centeredGramDet (m2 m3 m4 m5 m6 : ℝ) : ℝ :=
  -m2 ^ 3 * m6 + 2 * m2 ^ 2 * m3 * m5 + m2 ^ 2 * m4 ^ 2
    - 3 * m2 * m3 ^ 2 * m4 + m2 * m4 * m6 - m2 * m5 ^ 2
    + m3 ^ 4 - m3 ^ 2 * m6 + 2 * m3 * m4 * m5 - m4 ^ 3

/-- Determinant of the `3×3` Hessian-curvature numerator matrix after exact
elimination of the mean. -/
def curvatureNumeratorDet (m2 m3 m4 m5 m6 : ℝ) : ℝ :=
  -m2 ^ 6 + 2 * m2 ^ 4 * m4 - 2 * m2 ^ 3 * m3 ^ 2 - m2 ^ 3 * m6
    + 2 * m2 ^ 2 * m3 * m5 - m2 * m3 ^ 2 * m4 + m2 * m4 * m6
    - m2 * m5 ^ 2 - m3 ^ 2 * m6 + 2 * m3 * m4 * m5 - m4 ^ 3

/-- Exact polynomial elimination identity:
`det(C) = det(H) - det(g)^2`. -/
theorem curvatureNumeratorDet_eq_gram_sub_metric_sq
    (m2 m3 m4 m5 m6 : ℝ) :
    curvatureNumeratorDet m2 m3 m4 m5 m6 =
      centeredGramDet m2 m3 m4 m5 m6 - metricDet m2 m3 m4 ^ 2 := by
  unfold curvatureNumeratorDet centeredGramDet metricDet
  ring

/-- Scalar-curvature normal form used by the quadratic number-gas discovery
calculation. -/
noncomputable def scalarCurvature
    (m2 m3 m4 m5 m6 : ℝ) : ℝ :=
  (metricDet m2 m3 m4 ^ 2 - centeredGramDet m2 m3 m4 m5 m6) /
    (2 * metricDet m2 m3 m4 ^ 2)

/-- When the metric determinant is nonzero, the curvature is exactly one half
minus one half of the normalized centered Gram determinant. -/
theorem scalarCurvature_eq_half_sub
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : metricDet m2 m3 m4 ≠ 0) :
    scalarCurvature m2 m3 m4 m5 m6 =
      (1 : ℝ) / 2 *
        (1 - centeredGramDet m2 m3 m4 m5 m6 / metricDet m2 m3 m4 ^ 2) := by
  unfold scalarCurvature
  field_simp [hD]
  ring

/-- Algebraic curvature ceiling.  Once the centered degree-three moment Gram
determinant is known nonnegative, strict metric nondegeneracy implies `R ≤ 1/2`.
No sign-definiteness of `R` itself is asserted. -/
theorem scalarCurvature_le_half
    (m2 m3 m4 m5 m6 : ℝ)
    (hD : metricDet m2 m3 m4 ≠ 0)
    (hH : 0 ≤ centeredGramDet m2 m3 m4 m5 m6) :
    scalarCurvature m2 m3 m4 m5 m6 ≤ (1 : ℝ) / 2 := by
  rw [scalarCurvature_eq_half_sub m2 m3 m4 m5 m6 hD]
  have hDsq : 0 < metricDet m2 m3 m4 ^ 2 := sq_pos_of_ne_zero hD
  have hratio :
      0 ≤ centeredGramDet m2 m3 m4 m5 m6 / metricDet m2 m3 m4 ^ 2 :=
    div_nonneg hH hDsq.le
  linarith

end GppNumberGibbsQuadraticCurvatureAlgebra

#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.curvatureNumeratorDet_eq_gram_sub_metric_sq
#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.scalarCurvature_eq_half_sub
#print axioms GppNumberGibbsQuadraticCurvatureAlgebra.scalarCurvature_le_half
