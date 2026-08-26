import GppVerify.CelestialHolography.ScalarBoxRegulatorBounds
import GppVerify.CelestialHolography.ScalarBoxEndpointLinearization
import Mathlib.Tactic

/-!
# Exact pole-endpoint regulator scale

The moving pole argument in the regulated scalar box is

`q / a - 1`.

The discovery calculation introduces `η = m/S`, `δ = 4m/U`, and a bounded positive
factor `B`. This file proves the exact identity `q/a - 1 = η B`; no asymptotic
replacement is made.
-/

namespace GppScalarBoxPoleEndpointScale

open GppScalarBoxRegulatorAlgebra
open GppScalarBoxEndpointLinearization
open GppScalarBoxRegulatorBounds

/-- Exact identification of the pole endpoint with its natural regulator scale.

With `δ=4m/U`, `η=m/S`, and

`B = 2(1+κ)/[(1+δ)(1+κR)(1+R)(1-η)]`,

the Möbius endpoint obeys `q/a - 1 = η B`. -/
theorem q_div_a_sub_one_eq_eta_mul_B
    {S U m R κ q a δ η B : ℝ}
    (hS : 0 < S) (hU : 0 < U)
    (hm : 0 < m) (hmS : m < S)
    (hκlo : 1 ≤ κ)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hprodSq : (κ * R) ^ 2 =
      1 - 4 * m ^ 2 / (S * (U + 4 * m)))
    (hκsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U))
    (hδ : δ = 4 * m / U)
    (hη : η = m / S)
    (hB : B = 2 * (1 + κ) /
      ((1 + δ) * (1 + κ * R) * (1 + R) * (1 - η))) :
    q / a - 1 = η * B := by
  have hU4 : 0 < U + 4 * m := by linarith
  have hSU4 : 0 < S * (U + 4 * m) := mul_pos hS hU4
  have hκRplus : 1 + κ * R ≠ 0 := by
    intro hz
    have hκR : κ * R = -1 := by linarith
    rw [hκR] at hprodSq
    have hfrac : 0 < 4 * m ^ 2 / (S * (U + 4 * m)) := by positivity
    nlinarith
  have hRplus : 1 + R ≠ 0 := by
    intro hz
    have hR : R = -1 := by linarith
    rw [hR] at hprodSq
    have hfrac : 0 < 4 * m ^ 2 / (S * (U + 4 * m)) := by positivity
    have hκsqLower : 1 < κ ^ 2 := by
      rw [hκsq]
      have : 0 < 4 * m * (S - m) / (S * U) := by positivity
      linarith
    nlinarith
  have hκplus : 1 + κ ≠ 0 := by linarith
  have hqa := q_sub_a_exact_m_sq S U m R κ q a
    hSU4.ne' hκRplus hRplus hκplus hq ha hprodSq
  have haExact := a_exact_linear_m
    (mul_pos hS hU).ne' (by linarith : κ + 1 ≠ 0) ha hκsq
  have ha0 : a ≠ 0 := by
    rw [haExact]
    positivity
  rw [div_sub_one, ← sub_div, hqa, haExact, hδ, hη, hB]
  field_simp [hS.ne', hU.ne', hm.ne', sub_ne_zero.mpr hmS.ne']
  ring

/-- Once the exact pole-scale identity is known, the certified `B` interval immediately
places the physical pole argument inside the local dilogarithm disk. -/
theorem q_div_a_sub_one_small
    {q a η B : ℝ}
    (ha0 : a ≠ 0)
    (ht : q / a - 1 = η * B)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hB0 : 0 ≤ B) (hB : B ≤ 48 / 31) :
    0 ≤ q / a - 1 ∧
      q / a - 1 ≤ 12 / 31 ∧
      q / a - 1 < 1 / 2 := by
  have _ := ha0
  rw [ht]
  exact eta_mul_B_small η B hη0 hη hB0 hB

end GppScalarBoxPoleEndpointScale

#print axioms GppScalarBoxPoleEndpointScale.q_div_a_sub_one_eq_eta_mul_B
#print axioms GppScalarBoxPoleEndpointScale.q_div_a_sub_one_small
