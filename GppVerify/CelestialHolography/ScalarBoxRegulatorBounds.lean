import GppVerify.CelestialHolography.ScalarBoxRegulatorAlgebra
import Mathlib.Tactic

/-!
# Uniform scalar-box regulator bounds

This file begins promotion of the explicit rational interval estimates derived in
`GPPDiscovery2/discovery/celestial_box/REGULATOR_UNIFORM_SCALE_BOUNDS.md`.
-/

namespace GppScalarBoxRegulatorBounds

/-- If `0 ≤ δ,η ≤ 1/4`, `κ ≥ 0`, and
`κ² = 1 + δ(1-η)`, then the rational bounds `1 ≤ κ ≤ 9/8` hold. -/
theorem kappa_mem_rational_interval
    (δ η κ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκ0 : 0 ≤ κ)
    (hsq : κ ^ 2 = 1 + δ * (1 - η)) :
    1 ≤ κ ∧ κ ≤ 9 / 8 := by
  have h1η : 0 ≤ 1 - η := by linarith
  have hlowerSq : 1 ≤ κ ^ 2 := by
    rw [hsq]
    have := mul_nonneg hδ0 h1η
    linarith
  have hδη : 0 ≤ δ * η := mul_nonneg hδ0 hη0
  have hupperSq : κ ^ 2 ≤ 5 / 4 := by
    rw [hsq]
    nlinarith
  constructor <;> nlinarith

end GppScalarBoxRegulatorBounds

#print axioms GppScalarBoxRegulatorBounds.kappa_mem_rational_interval
