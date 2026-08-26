import GppVerify.CelestialHolography.RegulatedBoxDilogSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# Endpoint constant for the real Spence identity

The local dilogarithm series satisfies

  Li₂(1) = sum_{m>=1} 1/m² = π²/6.

This isolates the exact constant needed after the previously formalized derivative
cancellation of the Spence combination.
-/

namespace GppRegulatedBoxSpenceConstant

open GppRegulatedBoxDilogSeries

/-- The shifted reciprocal-square series has the classical Basel sum. -/
theorem hasSum_shifted_recip_sq :
    HasSum
      (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6) := by
  have hz := hasSum_zeta_two
  have hsum := hz.summable
  have htail :
      (∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) =
        ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ 2) := by
    have hsplit := hsum.sum_add_tsum_nat_add 1
    simpa using hsplit
  rw [← hz.tsum_eq, ← htail]
  exact hsum.comp_injective (fun a b h => Nat.succ.inj h)

/-- Exact endpoint value of the project's local real dilogarithm series. -/
theorem li2Series_one :
    li2Series 1 = Real.pi ^ 2 / 6 := by
  unfold li2Series
  simpa using hasSum_shifted_recip_sq.tsum_eq

end GppRegulatedBoxSpenceConstant

#print axioms GppRegulatedBoxSpenceConstant.li2Series_one
