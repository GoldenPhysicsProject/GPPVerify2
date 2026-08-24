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
  apply Finset.sum_nonneg
  intro _ _
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

end GppPrimeHankel
