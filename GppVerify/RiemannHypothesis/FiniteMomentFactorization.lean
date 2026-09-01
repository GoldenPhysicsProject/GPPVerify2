import Mathlib.Tactic

/-!
# Finite raw-moment factorization

A bookkeeping lemma for the arbitrary finite-support Fisher/Vandermonde identity.
It factors an ordered triple sum of separable monomials into the product of the
corresponding raw moments.
-/

open scoped BigOperators

namespace GppFiniteMomentFactorization

/-- Raw moment of order `r` for a finite weighted support. -/
def rawMoment {n : ℕ} (p x : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ i : Fin n, p i * x i ^ r

/-- Every separable ordered triple monomial factors into three raw moments. -/
theorem triple_monomial_factorization
    {n : ℕ} (p x : Fin n → ℝ) (a b c : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (p i * x i ^ a) * (p j * x j ^ b) * (p k * x k ^ c)) =
      rawMoment p x a * rawMoment p x b * rawMoment p x c := by
  unfold rawMoment
  -- Expand products of finite sums in their native ordered form.  Avoid
  -- commutative simp lemmas here: under Lean 4.19 they can canonicalize the
  -- two outer binders differently and leave a spurious `a`/`b` swap goal.
  simp [Finset.sum_mul, Finset.mul_sum, mul_assoc]

end GppFiniteMomentFactorization

#print axioms GppFiniteMomentFactorization.triple_monomial_factorization