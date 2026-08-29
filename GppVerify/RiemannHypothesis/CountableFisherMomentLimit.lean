import GppVerify.RiemannHypothesis.FiniteFisherMomentBridge
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Countable Fisher moment limit

This module isolates the analytic passage from finite range moments to the
countable Fisher determinant.  If the first four weighted raw moments are
summable, their finite truncations converge to the corresponding `tsum`s, and
therefore the polynomial covariance determinant converges as well.

This is the limit layer needed to transfer the finite Fisher--Vandermonde
identity to countable Gibbs/prime-gas measures.
-/

namespace GppCountableFisherMomentLimit

open Filter
open scoped BigOperators Topology
open GppFiniteFisherMomentBridge

/-- Finite range raw moment. -/
def partialMoment (w x : ℕ → ℝ) (r N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, w n * x n ^ r

/-- Countable raw moment. -/
noncomputable def infiniteMoment (w x : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑' n : ℕ, w n * x n ^ r

/-- A summable weighted raw moment is the limit of its finite range truncations. -/
theorem partialMoment_tendsto_infiniteMoment
    (w x : ℕ → ℝ) (r : ℕ)
    (hs : Summable (fun n : ℕ => w n * x n ^ r)) :
    Tendsto (fun N : ℕ => partialMoment w x r N) atTop
      (𝓝 (infiniteMoment w x r)) := by
  simpa [partialMoment, infiniteMoment] using hs.hasSum.tendsto_sum_nat

/-- If moments through order four are summable, the Fisher covariance determinant
of the finite truncations converges to the determinant formed from the countable
raw moments. -/
theorem fisherDet_partial_tendsto_infinite
    (w x : ℕ → ℝ)
    (h1 : Summable (fun n : ℕ => w n * x n ^ 1))
    (h2 : Summable (fun n : ℕ => w n * x n ^ 2))
    (h3 : Summable (fun n : ℕ => w n * x n ^ 3))
    (h4 : Summable (fun n : ℕ => w n * x n ^ 4)) :
    Tendsto
      (fun N : ℕ => fisherDet
        (partialMoment w x 1 N) (partialMoment w x 2 N)
        (partialMoment w x 3 N) (partialMoment w x 4 N))
      atTop
      (𝓝 (fisherDet
        (infiniteMoment w x 1) (infiniteMoment w x 2)
        (infiniteMoment w x 3) (infiniteMoment w x 4))) := by
  have h1lim := partialMoment_tendsto_infiniteMoment w x 1 h1
  have h2lim := partialMoment_tendsto_infiniteMoment w x 2 h2
  have h3lim := partialMoment_tendsto_infiniteMoment w x 3 h3
  have h4lim := partialMoment_tendsto_infiniteMoment w x 4 h4
  unfold fisherDet
  exact
    ((h2lim.sub (h1lim.pow 2)).mul (h4lim.sub (h2lim.pow 2))).sub
      ((h3lim.sub (h1lim.mul h2lim)).pow 2)

end GppCountableFisherMomentLimit

#print axioms GppCountableFisherMomentLimit.partialMoment_tendsto_infiniteMoment
#print axioms GppCountableFisherMomentLimit.fisherDet_partial_tendsto_infinite
