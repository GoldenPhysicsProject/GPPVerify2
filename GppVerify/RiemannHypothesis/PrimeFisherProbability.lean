import GppVerify.RiemannHypothesis.PrimeFisherCountableGeometry
import Mathlib.Tactic

/-!
# Probability normalization of the countable prime-Fisher measure

The arithmetic Fisher weight

  w_beta(n) = Lambda(n) log(n) exp(-beta log n)

has already been proved summable and to have strictly positive total mass for
`beta > 1`.  This file performs the probability normalization explicitly.  The
result is the honest countable probability measure needed before defining
expectations, covariance, entropy, and fluctuation geometry directly for the
prime-power Fisher ensemble.

No finite truncation is used in the normalization.
-/

namespace GppPrimeFisherProbability

open GppCountableFisherMomentLimit
open GppPrimeFisherMomentSummability
open GppPrimeHankelFisherSpecialization
open GppPrimeFisherCountableGeometry

/-- Total mass of the arithmetic Fisher measure. -/
noncomputable def primeFisherMass (beta : ℝ) : ℝ :=
  infiniteMoment (fisherWeight beta) Real.log 0

/-- Probability-normalized arithmetic Fisher weight. -/
noncomputable def primeFisherProbability (beta : ℝ) (n : ℕ) : ℝ :=
  fisherWeight beta n / primeFisherMass beta

/-- The total Fisher mass is strictly positive on the thermodynamic half-line. -/
theorem primeFisherMass_pos {beta : ℝ} (hbeta : 1 < beta) :
    0 < primeFisherMass beta := by
  simpa [primeFisherMass] using prime_fisher_mass_pos hbeta

/-- Each normalized prime-Fisher weight is nonnegative. -/
theorem primeFisherProbability_nonneg {beta : ℝ} (hbeta : 1 < beta) (n : ℕ) :
    0 ≤ primeFisherProbability beta n := by
  exact div_nonneg (fisherWeight_nonneg beta n) (primeFisherMass_pos hbeta).le

/-- The unnormalized Fisher weights sum exactly to their mass definition. -/
theorem fisherWeight_tsum_eq_mass (beta : ℝ) :
    (∑' n : ℕ, fisherWeight beta n) = primeFisherMass beta := by
  simp [primeFisherMass, infiniteMoment]

/-- **Prime-Fisher probability normalization.** For every `beta > 1`, the
actual countable von-Mangoldt Fisher weights normalize to total mass one. -/
theorem primeFisherProbability_tsum_eq_one {beta : ℝ} (hbeta : 1 < beta) :
    (∑' n : ℕ, primeFisherProbability beta n) = 1 := by
  have hmass : primeFisherMass beta ≠ 0 := (primeFisherMass_pos hbeta).ne'
  rw [show (∑' n : ℕ, primeFisherProbability beta n) =
      (∑' n : ℕ, fisherWeight beta n) / primeFisherMass beta by
        simp only [primeFisherProbability, tsum_div_const]]
  rw [fisherWeight_tsum_eq_mass]
  exact div_self hmass

/-- The normalized arithmetic Fisher weights are summable on `beta > 1`. -/
theorem summable_primeFisherProbability {beta : ℝ} (hbeta : 1 < beta) :
    Summable (primeFisherProbability beta) := by
  have hs : Summable (fun n : ℕ => fisherWeight beta n) := by
    simpa using summable_fisherWeight_mul_log_pow 0 hbeta
  simpa only [primeFisherProbability] using hs.div_const (primeFisherMass beta)

end GppPrimeFisherProbability

#print axioms GppPrimeFisherProbability.primeFisherMass_pos
#print axioms GppPrimeFisherProbability.primeFisherProbability_nonneg
#print axioms GppPrimeFisherProbability.primeFisherProbability_tsum_eq_one
#print axioms GppPrimeFisherProbability.summable_primeFisherProbability
