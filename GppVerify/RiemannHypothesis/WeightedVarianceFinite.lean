import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite weighted variance positivity

This file isolates the algebraic positivity mechanism needed by the zeta Gibbs/Fisher
formalization.  For nonnegative real weights `w i` and observables `x i`, Cauchy--Schwarz
gives

  (sum w_i x_i)^2 <= (sum w_i) (sum w_i x_i^2).

Equivalently, the unnormalized weighted variance numerator is nonnegative.  The statement
is finite and purely algebraic; no analytic continuation or zeta-zero assertion is involved.
-/

namespace GppWeightedVarianceFinite

open scoped BigOperators

/-- Finite weighted Cauchy--Schwarz in the exact form needed for variance positivity. -/
theorem weighted_first_moment_sq_le
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro i hi
    exact hw i hi
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg (x i))
  · intro i hi
    ring_nf

/-- The finite unnormalized weighted variance numerator is nonnegative. -/
theorem weighted_variance_numerator_nonneg
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) -
      (∑ i ∈ s, w i * x i) ^ 2 := by
  have h := weighted_first_moment_sq_le s w x hw
  linarith

/-- If the total weight is positive, the normalized finite weighted variance is nonnegative. -/
theorem normalized_weighted_variance_nonneg
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ s, w i) :
    0 ≤ (∑ i ∈ s, w i * x i ^ 2) / (∑ i ∈ s, w i) -
      ((∑ i ∈ s, w i * x i) / (∑ i ∈ s, w i)) ^ 2 := by
  have hnum := weighted_variance_numerator_nonneg s w x hw
  have hW2 : 0 < (∑ i ∈ s, w i) ^ 2 := sq_pos_of_pos hW
  apply (div_nonneg_iff hW2).2
  constructor
  · field_simp
    nlinarith
  · exact le_of_lt hW2

end GppWeightedVarianceFinite

#print axioms GppWeightedVarianceFinite.weighted_first_moment_sq_le
#print axioms GppWeightedVarianceFinite.weighted_variance_numerator_nonneg
#print axioms GppWeightedVarianceFinite.normalized_weighted_variance_nonneg
