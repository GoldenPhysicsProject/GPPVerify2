import GppVerify.RiemannHypothesis.CausalPrimeHeatSummability
import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerReindex
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

/-!
# Global causal prime heat reindexing

For every positive heat time the normalized von-Mangoldt heat series is absolutely summable.
Its support is contained in the prime powers, and Mathlib's canonical equivalence

  Nat.Primes × ℕ ≃ {n : ℕ // IsPrimePow n}

therefore reindexes the arithmetic heat series into prime/repetition coordinates.  The local
causal heat bridge then identifies every reindexed term with the weighted boundary anomaly
of the corresponding unilateral prime translation.

Thus the convergent arithmetic heat series has the exact causal representation

  sum_n H_t(n)
    = sum_(p,k) weight(p,k) * anomaly_t((k+1) log p).

This is still a scalar series identity.  It does not assert that the infinite sum of
operator commutators converges in trace norm; the manuscript requires a relative
prime--Archimedean trace for that operator-theoretic completion.
-/

namespace GppCausalPrimeHeatReindex

open Set
open GppCausalPrimeHeatBridge
open GppCausalPrimeHeatSummability
open GppCausalPrimeResolventFinite

/-- The normalized heat summand vanishes away from prime powers. -/
theorem normalizedPrimeHeatSummand_eq_zero_of_not_primePow
    (t : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) :
    normalizedPrimeHeatSummand t n = 0 := by
  unfold normalizedPrimeHeatSummand
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  simp

/-- Support of the normalized heat series is contained in the prime powers. -/
theorem support_normalizedPrimeHeatSummand_subset_primePowers (t : ℝ) :
    Function.support (normalizedPrimeHeatSummand t) ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpp
  exact hn (normalizedPrimeHeatSummand_eq_zero_of_not_primePow t hpp)

/-- Causal prime/repetition term in canonical `Primes × ℕ` coordinates. -/
noncomputable def causalPrimePairTerm (t : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  resolventWeight ((pk.1 : ℕ) : ℝ) pk.2 *
    scalarHeatAnomaly t (repetitionLength ((pk.1 : ℕ) : ℝ) pk.2)

/-- Exact canonical reindex of the normalized arithmetic heat series by prime powers. -/
theorem normalizedPrimeHeat_tsum_eq_primePower_pair_tsum (t : ℝ) :
    (∑' n : ℕ, normalizedPrimeHeatSummand t n) =
      ∑' pk : Nat.Primes × ℕ,
        normalizedPrimeHeatSummand t ((pk.1 : ℕ) ^ (pk.2 + 1)) := by
  let S : Set ℕ := {n : ℕ | IsPrimePow n}
  have hsupp : Function.support (normalizedPrimeHeatSummand t) ⊆ S :=
    support_normalizedPrimeHeatSummand_subset_primePowers t
  calc
    (∑' n : ℕ, normalizedPrimeHeatSummand t n) =
        ∑' n : S, normalizedPrimeHeatSummand t n :=
      (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' pk : Nat.Primes × ℕ,
        normalizedPrimeHeatSummand t ((pk.1 : ℕ) ^ (pk.2 + 1)) := by
      simpa [S] using
        (Nat.Primes.prodNatEquiv.tsum_eq
          (fun n : {n : ℕ // IsPrimePow n} => normalizedPrimeHeatSummand t n)).symm

/-- **Global scalar causal-prime identity.** The normalized von-Mangoldt heat `tsum` is
exactly the canonical prime/repetition sum of weighted causal boundary anomalies. -/
theorem normalizedPrimeHeat_tsum_eq_causalPrimePair_tsum (t : ℝ) :
    (∑' n : ℕ, normalizedPrimeHeatSummand t n) =
      ∑' pk : Nat.Primes × ℕ, causalPrimePairTerm t pk := by
  rw [normalizedPrimeHeat_tsum_eq_primePower_pair_tsum]
  apply tsum_congr
  intro pk
  unfold causalPrimePairTerm
  simpa [repetition] using
    (weighted_causal_anomaly_eq_normalizedPrimeHeatSummand pk.1 t pk.2).symm

/-- For positive heat time, the preceding global scalar identity has an absolutely summable
arithmetic left-hand side.  This packages convergence and causal reindexing together without
claiming trace-norm convergence of the operator series. -/
theorem convergent_normalizedPrimeHeat_eq_causalPrimePair_tsum
    {t : ℝ} (ht : 0 < t) :
    Summable (normalizedPrimeHeatSummand t) ∧
      (∑' n : ℕ, normalizedPrimeHeatSummand t n) =
        ∑' pk : Nat.Primes × ℕ, causalPrimePairTerm t pk := by
  exact ⟨summable_normalizedPrimeHeatSummand ht,
    normalizedPrimeHeat_tsum_eq_causalPrimePair_tsum t⟩

end GppCausalPrimeHeatReindex

#print axioms GppCausalPrimeHeatReindex.normalizedPrimeHeat_tsum_eq_primePower_pair_tsum
#print axioms GppCausalPrimeHeatReindex.normalizedPrimeHeat_tsum_eq_causalPrimePair_tsum
#print axioms GppCausalPrimeHeatReindex.convergent_normalizedPrimeHeat_eq_causalPrimePair_tsum
