import GppVerify.RiemannHypothesis.FiniteFisherVandermondeIdentity
import Mathlib.Tactic

/-!
# Quantitative finite Fisher witness

This module upgrades the finite three-point Vandermonde witness from strict
positivity to an explicit lower bound on the division-free Fisher numerator.
The bound is stable under adjoining further nonnegative support points and is
therefore suited to the existing countable strict-witness limit theorem.
-/

open scoped BigOperators

namespace GppFiniteFisherQuantitativeWitness

open GppFiniteVandermondeEnergy
open GppFiniteMomentFactorization
open GppFiniteFisherMomentBridge
open GppFiniteFisherVandermondeIdentity

/-- For nonnegative finite weights, every individual weight is bounded above
by the total mass `rawMoment p x 0`. -/
theorem weight_le_rawMoment_zero
    {n : ℕ} (p x : Fin n → ℝ)
    (hp : ∀ a, 0 ≤ p a) (i : Fin n) :
    p i ≤ rawMoment p x 0 := by
  unfold rawMoment
  simp only [pow_zero, mul_one]
  refine Finset.single_le_sum
    (s := Finset.univ) (f := p) ?_ (Finset.mem_univ i)
  intro a ha
  exact hp a

/-- **Quantitative Fisher witness.** A selected ordered three-point
Vandermonde contribution gives an explicit lower bound for six times the
mass-aware Fisher numerator. The right-hand side may include arbitrarily many
additional nonnegative states; the selected witness on the left is unchanged.
-/
theorem weighted_vandermonde_witness_le_six_fisherNumerator
    {n : ℕ} (p x : Fin n → ℝ)
    (hp : ∀ a, 0 ≤ p a) (i j k : Fin n) :
    p i *
        (p i * p j * p k *
          (((x i - x j) * (x i - x k) * (x j - x k)) ^ 2)) ≤
      6 * fisherNumerator
        (rawMoment p x 0) (rawMoment p x 1) (rawMoment p x 2)
        (rawMoment p x 3) (rawMoment p x 4) := by
  let W : ℝ :=
    p i * p j * p k *
      (((x i - x j) * (x i - x k) * (x j - x k)) ^ 2)
  have hm0 : 0 ≤ rawMoment p x 0 := rawMoment_zero_nonneg p x hp
  have hmass : p i ≤ rawMoment p x 0 := weight_le_rawMoment_zero p x hp i
  have hW : 0 ≤ W := by
    dsimp [W]
    exact weighted_vandermonde_sq_nonneg
      (p i) (p j) (p k) (x i) (x j) (x k) (hp i) (hp j) (hp k)
  have hE : W ≤ orderedVandermondeEnergy p x := by
    dsimp [W]
    exact weighted_vandermonde_sq_le_orderedVandermondeEnergy p x hp i j k
  have hprod :
      p i * W ≤ rawMoment p x 0 * orderedVandermondeEnergy p x := by
    exact mul_le_mul hmass hE hW hm0
  have hbridge := six_fisherNumerator_eq_mass_mul_momentDiscriminant
    (rawMoment p x 0) (rawMoment p x 1) (rawMoment p x 2)
    (rawMoment p x 3) (rawMoment p x 4)
  rw [← orderedVandermondeEnergy_eq_momentDiscriminant p x] at hbridge
  dsimp [W] at hprod ⊢
  nlinarith

/-- Dividing the previous identity by the positive constant six gives the
corresponding direct lower bound on the Fisher numerator. -/
theorem weighted_vandermonde_witness_div_six_le_fisherNumerator
    {n : ℕ} (p x : Fin n → ℝ)
    (hp : ∀ a, 0 ≤ p a) (i j k : Fin n) :
    (p i *
        (p i * p j * p k *
          (((x i - x j) * (x i - x k) * (x j - x k)) ^ 2))) / 6 ≤
      fisherNumerator
        (rawMoment p x 0) (rawMoment p x 1) (rawMoment p x 2)
        (rawMoment p x 3) (rawMoment p x 4) := by
  have h := weighted_vandermonde_witness_le_six_fisherNumerator p x hp i j k
  nlinarith

end GppFiniteFisherQuantitativeWitness

#print axioms GppFiniteFisherQuantitativeWitness.weight_le_rawMoment_zero
#print axioms GppFiniteFisherQuantitativeWitness.weighted_vandermonde_witness_le_six_fisherNumerator
#print axioms GppFiniteFisherQuantitativeWitness.weighted_vandermonde_witness_div_six_le_fisherNumerator

-- CI recheck marker after the pinned-Lean repair of `FiniteMomentFactorization`.