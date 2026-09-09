import Mathlib.Tactic

/-!
# Finite odd/even split for Weierstrass products

This module isolates the finite combinatorial factorization needed to pass from
the full `sinh` Weierstrass product to its odd subproduct.  It deliberately
proves only an exact finite identity; no infinite-product limit or logarithmic
differentiation is asserted here.
-/

namespace GppOddWeierstrassProductSplit

open scoped BigOperators

/-- Splitting a product over `0, ..., 2N-1` into its even and odd indices. -/
theorem prod_range_even_mul_odd (f : ℕ → ℝ) : ∀ N : ℕ,
    (∏ k in Finset.range N, f (2 * k)) *
        (∏ k in Finset.range N, f (2 * k + 1)) =
      ∏ j in Finset.range (2 * N), f j := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega]
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      rw [← ih]
      ring

end GppOddWeierstrassProductSplit

#print axioms GppOddWeierstrassProductSplit.prod_range_even_mul_odd
