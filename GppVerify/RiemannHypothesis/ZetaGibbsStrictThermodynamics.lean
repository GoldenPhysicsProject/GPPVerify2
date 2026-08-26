import GppVerify.RiemannHypothesis.ZetaGibbsFisherStrict
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-!
# Strict thermodynamic stability of the zeta Gibbs gas

The project already identifies the genuine Gibbs log-energy variance with the positive
von-Mangoldt Fisher series.  This file upgrades the existing weak inequalities to strict
ones by using the single `n = 2` arithmetic mode as a witness.
-/

namespace GppZetaGibbsStrictThermodynamics

open ArithmeticFunction
open GppZetaGibbsFisher
open GppZetaFisherStrictMonotonicity
open GppZetaGibbsFisherStrict

/-- The `n = 2` Fisher mode is strictly positive at every real inverse temperature. -/
theorem fisherSummand_two_pos (β : ℝ) : 0 < fisherSummand β 2 := by
  unfold fisherSummand
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- The full arithmetic Fisher series is strictly positive for every `β > 1`. -/
theorem fisher_tsum_pos {β : ℝ} (hβ : 1 < β) :
    0 < ∑' n : ℕ, fisherSummand β n := by
  exact (summable_fisherSummand hβ).tsum_pos
    (fisherSummand_nonneg β) 2 (fisherSummand_two_pos β)

/-- The genuine zeta-Gibbs Fisher metric / log-energy variance is strictly positive. -/
theorem logEnergyVariance_pos {β : ℝ} (hβ : 1 < β) :
    0 < logEnergyVariance β := by
  rw [logEnergyVariance_eq_fisher_tsum hβ]
  exact fisher_tsum_pos hβ

/-- Strict positive heat capacity on the honest Gibbs domain. -/
theorem heatCapacity_pos {β : ℝ} (hβ : 1 < β) :
    0 < heatCapacity β := by
  unfold heatCapacity
  have hβ0 : 0 < β := lt_trans (by norm_num) hβ
  exact mul_pos (sq_pos_of_pos hβ0) (logEnergyVariance_pos hβ)

/-- The entropy response is strictly negative with inverse temperature. -/
theorem entropyBetaDerivative_neg {β : ℝ} (hβ : 1 < β) :
    entropyBetaDerivative β < 0 := by
  unfold entropyBetaDerivative
  have hβ0 : 0 < β := lt_trans (by norm_num) hβ
  exact mul_neg_of_neg_of_pos (neg_neg.mpr hβ0) (logEnergyVariance_pos hβ)

end GppZetaGibbsStrictThermodynamics

#print axioms GppZetaGibbsStrictThermodynamics.fisher_tsum_pos
#print axioms GppZetaGibbsStrictThermodynamics.logEnergyVariance_pos
#print axioms GppZetaGibbsStrictThermodynamics.heatCapacity_pos
#print axioms GppZetaGibbsStrictThermodynamics.entropyBetaDerivative_neg
