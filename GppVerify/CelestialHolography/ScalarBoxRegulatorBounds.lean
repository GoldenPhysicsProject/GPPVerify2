import GppVerify.CelestialHolography.ScalarBoxRegulatorAlgebra
import Mathlib.Tactic

/-!
# Uniform scalar-box regulator bounds

This file promotes the explicit rational interval estimates derived in
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
`8/9 ≤ R ≤ 1`. -/
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

/-- Under the exact product relation `(κR)² = 1 - δη/(1+δ)`,
`15/16 ≤ κR ≤ 1`. -/
theorem kappaR_mem_rational_interval
    (δ η x : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hx0 : 0 ≤ x)
    (hsq : x ^ 2 = 1 - δ * η / (1 + δ)) :
    15 / 16 ≤ x ∧ x ≤ 1 := by
  have hden : 0 < 1 + δ := by linarith
  have hδη0 : 0 ≤ δ * η := mul_nonneg hδ0 hη0
  have hδηle : δ * η ≤ 1 / 16 := by nlinarith
  have hfrac0 : 0 ≤ δ * η / (1 + δ) := div_nonneg hδη0 hden.le
  have hfracle : δ * η / (1 + δ) ≤ 1 / 16 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hupperSq : x ^ 2 ≤ 1 := by
    rw [hsq]
    linarith
  have hlowerSq : (15 / 16 : ℝ) ^ 2 ≤ x ^ 2 := by
    rw [hsq]
    nlinarith
  constructor <;> nlinarith

/-- `A = 4(1-η)/(1+κ)^2` lies in `[192/289,1]`. -/
theorem A_mem_rational_interval
    (η κ A : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hA : A = 4 * (1 - η) / (1 + κ) ^ 2) :
    192 / 289 ≤ A ∧ A ≤ 1 := by
  have hbase : 0 < 1 + κ := by linarith
  have hden : 0 < (1 + κ) ^ 2 := sq_pos_of_pos hbase
  rw [hA]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg (κ - 1), sq_nonneg (9 / 8 - κ)]
  · apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg (κ - 1)]

/-- If `0 ≤ r ≤ 1/8`, then `Q = 1/(1+r+r²/4)` lies in `[256/289,1]`. -/
theorem Q_mem_rational_interval
    (r Q : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 8)
    (hQ : Q = 1 / (1 + r + r ^ 2 / 4)) :
    256 / 289 ≤ Q ∧ Q ≤ 1 := by
  have hden : 0 < 1 + r + r ^ 2 / 4 := by nlinarith [sq_nonneg r]
  have hrsq : r ^ 2 ≤ 1 / 64 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
  rw [hQ]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith
  · apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg r]

/-- Pole-endpoint normalization bound. -/
theorem B_pos_and_le
    (δ η κ x R B : ℝ)
    (hδ0 : 0 ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hκlo : 1 ≤ κ) (hκhi : κ ≤ 9 / 8)
    (hxlo : 15 / 16 ≤ x)
    (hRlo : 8 / 9 ≤ R)
    (hB : B = 2 * (1 + κ) /
      ((1 + δ) * (1 + x) * (1 + R) * (1 - η))) :
    0 < B ∧ B ≤ 48 / 31 := by
  have h1δ : 0 < 1 + δ := by linarith
  have h1x : 0 < 1 + x := by linarith
  have h1R : 0 < 1 + R := by linarith
  have h1η : 0 < 1 - η := by linarith
  have hden : 0 < (1 + δ) * (1 + x) * (1 + R) * (1 - η) := by positivity
  rw [hB]
  constructor
  · exact div_pos (by nlinarith) hden
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hη)]

/-- The dilogarithm endpoint `η B` is uniformly inside the elementary `x<1/2`
regime: `0 ≤ ηB ≤ 12/31 < 1/2`. -/
theorem eta_mul_B_small
    (η B : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    0 ≤ η * B ∧ η * B ≤ 12 / 31 ∧ η * B < 1 / 2 := by
  have hprod0 : 0 ≤ η * B := mul_nonneg hη0 hB0
  have hprod : η * B ≤ 12 / 31 := by nlinarith
  constructor
  · exact hprod0
  · constructor
    · exact hprod
    · nlinarith

end GppScalarBoxRegulatorBounds

#print axioms GppScalarBoxRegulatorBounds.kappa_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.R_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.kappaR_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.A_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.Q_mem_rational_interval
#print axioms GppScalarBoxRegulatorBounds.B_pos_and_le
#print axioms GppScalarBoxRegulatorBounds.eta_mul_B_small
