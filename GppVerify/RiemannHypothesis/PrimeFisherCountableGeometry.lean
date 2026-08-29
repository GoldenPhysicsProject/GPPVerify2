import GppVerify.RiemannHypothesis.CountableFisherMomentLimit
import GppVerify.RiemannHypothesis.PrimeFisherMomentSummability
import Mathlib.Tactic

/-!
# Countable prime-gas Fisher geometry

This file specializes the general countable Fisher/Vandermonde positivity theorem to the
actual arithmetic Fisher weight

  w_beta(n) = Lambda(n) log(n) exp(-beta log n),

with observable `x(n) = log n`.  The all-order logarithmic summability theorem supplies
raw moments through order four for every `beta > 1`; pointwise nonnegativity of the
von-Mangoldt Fisher weight then gives a nonnegative mass-aware covariance numerator.

No normalization of finite truncations is used.  This is the correct countable statement
before dividing by the total Fisher mass to obtain a probability distribution.
-/

namespace GppPrimeFisherCountableGeometry

open GppCountableFisherMomentLimit
open GppPrimeFisherMomentSummability
open GppPrimeHankelFisherSpecialization
open GppFiniteFisherMomentBridge

/-- Every raw logarithmic moment of the arithmetic Fisher weight is summable on `beta > 1`,
expressed in the generic `infiniteMoment` interface used by the countable Fisher theorem. -/
theorem summable_prime_fisher_moment (r : ℕ) {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => fisherWeight β n * (Real.log n) ^ r) := by
  exact summable_fisherWeight_mul_log_pow r hβ

/-- **Countable arithmetic Fisher positivity.**  On the half-plane `beta > 1`, the
mass-aware covariance numerator for the sufficient statistics `log n` and `(log n)^2`
is nonnegative for the full countable von-Mangoldt Fisher measure. -/
theorem prime_fisherNumerator_infinite_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ fisherNumerator
      (infiniteMoment (fisherWeight β) Real.log 0)
      (infiniteMoment (fisherWeight β) Real.log 1)
      (infiniteMoment (fisherWeight β) Real.log 2)
      (infiniteMoment (fisherWeight β) Real.log 3)
      (infiniteMoment (fisherWeight β) Real.log 4) := by
  apply fisherNumerator_infinite_nonneg
  · intro n
    exact fisherWeight_nonneg β n
  · simpa using summable_fisherWeight_mul_log_pow 0 hβ
  · simpa using summable_fisherWeight_mul_log_pow 1 hβ
  · simpa using summable_fisherWeight_mul_log_pow 2 hβ
  · simpa using summable_fisherWeight_mul_log_pow 3 hβ
  · simpa using summable_fisherWeight_mul_log_pow 4 hβ

end GppPrimeFisherCountableGeometry

#print axioms GppPrimeFisherCountableGeometry.prime_fisherNumerator_infinite_nonneg
