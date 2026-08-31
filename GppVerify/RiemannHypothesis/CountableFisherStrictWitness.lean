import GppVerify.RiemannHypothesis.CountableFisherMomentLimit
import Mathlib.Tactic

/-!
# Countable Fisher strict witness bridge

This module packages the final topological step needed for strict countable
Fisher positivity.  Once a fixed positive lower witness is known for all
sufficiently large finite prefixes, convergence of the mass-aware Fisher
numerator transfers that witness unchanged to the countable limit.

This deliberately separates the finite algebraic witness construction from
the analytic moment-limit passage.
-/

namespace GppCountableFisherStrictWitness

open Filter
open GppCountableFisherMomentLimit

/-- Any eventual lower bound for the finite-prefix mass-aware Fisher numerator
survives the countable moment limit. -/
theorem fisherNumerator_infinite_ge_of_eventually_partial_ge
    (w x : ℕ → ℝ) (c : ℝ)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hge : ∀ᶠ N : ℕ in atTop,
      c ≤ fisherNumerator
        (partialMoment w x 0 N) (partialMoment w x 1 N)
        (partialMoment w x 2 N) (partialMoment w x 3 N)
        (partialMoment w x 4 N)) :
    c ≤ fisherNumerator
      (infiniteMoment w x 0) (infiniteMoment w x 1)
      (infiniteMoment w x 2) (infiniteMoment w x 3)
      (infiniteMoment w x 4) := by
  apply le_of_tendsto
    (fisherNumerator_partial_tendsto_infinite w x h0 h1 h2 h3 h4)
  exact hge

/-- A strictly positive eventual finite-prefix witness yields strict positivity
of the countable mass-aware Fisher numerator. -/
theorem fisherNumerator_infinite_pos_of_eventually_partial_ge
    (w x : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hge : ∀ᶠ N : ℕ in atTop,
      c ≤ fisherNumerator
        (partialMoment w x 0 N) (partialMoment w x 1 N)
        (partialMoment w x 2 N) (partialMoment w x 3 N)
        (partialMoment w x 4 N)) :
    0 < fisherNumerator
      (infiniteMoment w x 0) (infiniteMoment w x 1)
      (infiniteMoment w x 2) (infiniteMoment w x 3)
      (infiniteMoment w x 4) := by
  exact lt_of_lt_of_le hc
    (fisherNumerator_infinite_ge_of_eventually_partial_ge
      w x c h0 h1 h2 h3 h4 hge)

/-- At unit total mass, the same positive finite-prefix witness gives strict
positivity of the usual countable Fisher covariance determinant. -/
theorem fisherDet_infinite_pos_of_mass_one_and_eventually_partial_ge
    (w x : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c)
    (h0 : Summable (fun n : ℕ => w n * x n ^ 0))
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4))
    (hmass : infiniteMoment w x 0 = 1)
    (hge : ∀ᶠ N : ℕ in atTop,
      c ≤ fisherNumerator
        (partialMoment w x 0 N) (partialMoment w x 1 N)
        (partialMoment w x 2 N) (partialMoment w x 3 N)
        (partialMoment w x 4 N)) :
    0 < fisherDet
      (infiniteMoment w x 1) (infiniteMoment w x 2)
      (infiniteMoment w x 3) (infiniteMoment w x 4) := by
  have hpos := fisherNumerator_infinite_pos_of_eventually_partial_ge
    w x c hc h0 h1 h2 h3 h4 hge
  rw [hmass, GppFiniteFisherMomentBridge.fisherNumerator_one_eq_fisherDet] at hpos
  exact hpos

end GppCountableFisherStrictWitness

#print axioms GppCountableFisherStrictWitness.fisherNumerator_infinite_ge_of_eventually_partial_ge
#print axioms GppCountableFisherStrictWitness.fisherNumerator_infinite_pos_of_eventually_partial_ge
#print axioms GppCountableFisherStrictWitness.fisherDet_infinite_pos_of_mass_one_and_eventually_partial_ge
