import GppVerify.CelestialHolography.ScalarBoxStructuredPhysicalMajorant
import GppVerify.CelestialHolography.ScalarBoxD0PrefactorVanishing
import GppVerify.CelestialHolography.ScalarBoxConvergenceAssembly
import GppVerify.CelestialHolography.ScalarBoxPrefactorRemainder
import Mathlib.Tactic

/-!
# Structured physical scalar-box convergence

This is the convergence assembly for the correct mixed-logarithm majorant.  Once the
moving core is eventually bounded by `structuredPhysicalCoreMajorant`, every remaining
term is already known to vanish and the physical `1/kappa` prefactor is controlled by
its exact quadratic defining relation.
-/

namespace GppScalarBoxStructuredPhysicalConvergence

open Filter Set
open scoped Topology
open GppScalarBoxStructuredPhysicalMajorant
open GppScalarBoxD0PrefactorVanishing
open GppScalarBoxConvergenceAssembly
open GppScalarBoxPrefactorRemainder

/-- Final convergence assembly for the correct structured scalar-box core bound. -/
theorem tendsto_corrected_scalarBox_core_zero_of_structured_bound
    {S U : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    {D κ : ℝ → ℝ}
    (hmS : ∀ᶠ m in 𝓝[>] 0, m ≤ S)
    (hκ : ∀ᶠ m in 𝓝[>] 0, 1 ≤ κ m)
    (hκsq : ∀ᶠ m in 𝓝[>] 0,
      (κ m) ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hcore : ∀ᶠ m in 𝓝[>] 0,
      |D m - scalarBoxD0 S U m| ≤ structuredPhysicalCoreMajorant S U m) :
    Tendsto
      (fun m : ℝ => D m / κ m - scalarBoxD0 S U m)
      (𝓝[>] 0) (𝓝 0) := by
  have hM := tendsto_structuredPhysicalCoreMajorant_nhdsGT_zero hS hU
  have hP := tendsto_delta_half_mul_abs_scalarBoxD0_nhdsGT_zero (S := S) hU
  have hbound : ∀ᶠ m in 𝓝[>] 0,
      |D m / κ m - scalarBoxD0 S U m| ≤
        structuredPhysicalCoreMajorant S U m +
          ((4 * m / U) / 2) * |scalarBoxD0 S U m| := by
    filter_upwards [self_mem_nhdsWithin, hmS, hκ, hκsq, hcore] with
      m hm hmS' hκ' hκsq' hcore'
    exact abs_prefactor_remainder_le_of_physical_core_bound
      hS hU hm.le hmS' hκ' hκsq' hcore'
  exact tendsto_corrected_remainder_zero_of_prefactor_bound hM hP hbound

end GppScalarBoxStructuredPhysicalConvergence

#print axioms GppScalarBoxStructuredPhysicalConvergence.tendsto_corrected_scalarBox_core_zero_of_structured_bound
