import GppVerify.RiemannHypothesis.PrimeHankelFiniteGramStrict
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Infinite lifting for strict prime-gas Gram positivity

A strictly positive finite truncation of a summable nonnegative series forces the
full infinite sum to be strictly positive.  This is the order-theoretic bridge
needed to pass from finite prime witnesses to the full von-Mangoldt moment form.
-/

namespace GppPrimeHankelInfiniteLift

open BigOperators

/-- A positive finite witness inside a summable nonnegative series forces the
whole `tsum` to be strictly positive. -/
theorem tsum_pos_of_finite_sum_pos
    {ι : Type*} (f : ι → ℝ) (S : Finset ι)
    (hf : Summable f)
    (hnonneg : ∀ i, 0 ≤ f i)
    (hS : 0 < ∑ i ∈ S, f i) :
    0 < ∑' i, f i := by
  exact lt_of_lt_of_le hS
    (sum_le_tsum S (fun i _ => hnonneg i) hf)

/-- Convenient form for weighted squares: positivity of one finite truncation
lifts to positivity of the full summable weighted-square series. -/
theorem weighted_sq_tsum_pos
    {ι : Type*} (w q : ι → ℝ) (S : Finset ι)
    (hsum : Summable (fun i => w i * (q i) ^ 2))
    (hw : ∀ i, 0 ≤ w i)
    (hS : 0 < ∑ i ∈ S, w i * (q i) ^ 2) :
    0 < ∑' i, w i * (q i) ^ 2 := by
  apply tsum_pos_of_finite_sum_pos (fun i => w i * (q i) ^ 2) S hsum
  · intro i
    exact mul_nonneg (hw i) (sq_nonneg (q i))
  · exact hS

end GppPrimeHankelInfiniteLift

#print axioms GppPrimeHankelInfiniteLift.tsum_pos_of_finite_sum_pos
#print axioms GppPrimeHankelInfiniteLift.weighted_sq_tsum_pos
