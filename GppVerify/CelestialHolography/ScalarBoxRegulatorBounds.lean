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

/-- If `0 ≤ δ ≤ 1/4`, `R ≥ 0`, and `R² = 1/(1+δ)`, then
`8/9 ≤ R ≤ 1`. The constants are deliberately rational and slightly weaker
than the sharp square-root bounds. -/
theorem R_mem_rational_interval
    (δ R : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hR0 : 0 ≤ R)
    (hsq : R ^ 2 = 1 / (1 + δ)) :
    8 / 9 ≤ R ∧ R ≤ 1 := by
  have hden : 0 < 1 + δ := by linarith
  have hupperSq : R ^ 2 ≤ 1 := by
    rw [hsq]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hlowerSq : (8 / 9 : ℝ) ^ 2 ≤ R ^ 2 := by
    rw [hsq]
    apply (le_div_iff₀ hden).2
    nlinarith
  constructor <;> nlinarith

end GppScalarBoxRegulatorBounds

#print axioms GppScalarBoxRegulatorBounds.kappa_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.R_mem_rational_interval
