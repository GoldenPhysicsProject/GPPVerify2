import Mathlib

open scoped BigOperators

namespace GppPrimeHankel

/--
Finite weighted polynomial Gram positivity. This is the algebraic core of the
prime-side Hankel moment hierarchy: any nonnegative discrete weight produces a
nonnegative quadratic form after evaluating a polynomial on the support.
-/
theorem finite_weighted_polynomial_gram_nonneg
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (N : ℕ) (c : Fin (N + 1) → ℝ) :
    0 ≤ ∑ i ∈ s, w i * (∑ j : Fin (N + 1), c j * (x i) ^ (j : ℕ)) ^ 2 := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i hi) (sq_nonneg _)

/-- The same positivity statement when the finite support is encoded directly
as a finite type rather than an explicit `Finset`. -/
theorem finite_type_weighted_polynomial_gram_nonneg
    {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (N : ℕ) (c : Fin (N + 1) → ℝ) :
    0 ≤ ∑ i : ι, w i * (∑ j : Fin (N + 1), c j * (x i) ^ (j : ℕ)) ^ 2 := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (sq_nonneg _)

/-- Two distinct support points with positive weights force the `2 × 2`
Hankel determinant to be strictly positive.  Algebraically the determinant is
exactly `w₁ w₂ (x₁-x₂)^2`; this is the strict core used when the prime-gas
measure supplies, for example, the distinct support points `log 2` and `log 3`. -/
theorem two_support_hankel_det_pos
    (w₁ w₂ x₁ x₂ : ℝ)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hx : x₁ ≠ x₂) :
    0 < (w₁ + w₂) * (w₁ * x₁ ^ 2 + w₂ * x₂ ^ 2) -
      (w₁ * x₁ + w₂ * x₂) ^ 2 := by
  have hdiff : 0 < (x₁ - x₂) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  have hprod : 0 < w₁ * w₂ * (x₁ - x₂) ^ 2 := by positivity
  nlinarith [hprod]

/-- Exact determinant factorization behind `two_support_hankel_det_pos`. -/
theorem two_support_hankel_det_factor
    (w₁ w₂ x₁ x₂ : ℝ) :
    (w₁ + w₂) * (w₁ * x₁ ^ 2 + w₂ * x₂ ^ 2) -
      (w₁ * x₁ + w₂ * x₂) ^ 2 =
      w₁ * w₂ * (x₁ - x₂) ^ 2 := by
  ring

end GppPrimeHankel
