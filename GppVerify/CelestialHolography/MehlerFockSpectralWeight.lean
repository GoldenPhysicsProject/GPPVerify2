import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Mehler-Fock / Wiener-Hopf spectral weight algebra

This file records the exact elementary hyperbolic-weight relation discovered in
`GPPDiscovery2`. The Gamma-function interpretation is deliberately left outside
the formal statement until the required Gamma-modulus API is formalized.
-/

namespace GppMehlerFockSpectral

open Real

/-- Wiener-Hopf spectral weight. -/
noncomputable def wienerHopfWeight (λ : ℝ) : ℝ :=
  Real.pi * λ / Real.sinh (Real.pi * λ)

/-- Mehler-Fock density in explicit sinh/cosh form. -/
noncomputable def mehlerFockWeight (λ : ℝ) : ℝ :=
  λ * Real.sinh (Real.pi * λ) / Real.cosh (Real.pi * λ)

/-- The collapsed product density obtained after multiplying the Wiener-Hopf
and Mehler-Fock factors. Discovery identifies this also with
`λ² |Γ(1/2 + iλ)|²`; only the elementary hyperbolic form is used here. -/
noncomputable def collapsedWeight (λ : ℝ) : ℝ :=
  Real.pi * λ ^ 2 / Real.cosh (Real.pi * λ)

/-- The product of the two weights collapses to the half-shifted hyperbolic factor. -/
theorem weight_product {λ : ℝ}
    (hs : Real.sinh (Real.pi * λ) ≠ 0)
    (hc : Real.cosh (Real.pi * λ) ≠ 0) :
    wienerHopfWeight λ * mehlerFockWeight λ = collapsedWeight λ := by
  unfold wienerHopfWeight mehlerFockWeight collapsedWeight
  field_simp [hs, hc]
  ring

/-- The collapsed spectral density is pointwise nonnegative. -/
theorem collapsedWeight_nonneg (λ : ℝ) :
    0 ≤ collapsedWeight λ := by
  unfold collapsedWeight
  exact div_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg λ)) (Real.cosh_pos _).le

/-- Away from the origin the collapsed density is strictly positive. -/
theorem collapsedWeight_pos {λ : ℝ} (hλ : λ ≠ 0) :
    0 < collapsedWeight λ := by
  unfold collapsedWeight
  exact div_pos (mul_pos Real.pi_pos (sq_pos_of_ne_zero hλ)) (Real.cosh_pos _)

/-- Both explicitly defined weights vanish at the origin under Lean's totalized division. -/
theorem mehlerFockWeight_zero : mehlerFockWeight 0 = 0 := by
  simp [mehlerFockWeight]

/-- The collapsed density also vanishes exactly at the origin in the forward direction. -/
theorem collapsedWeight_zero : collapsedWeight 0 = 0 := by
  simp [collapsedWeight]

end GppMehlerFockSpectral

#print axioms GppMehlerFockSpectral.weight_product
#print axioms GppMehlerFockSpectral.collapsedWeight_nonneg
#print axioms GppMehlerFockSpectral.collapsedWeight_pos
#print axioms GppMehlerFockSpectral.mehlerFockWeight_zero
#print axioms GppMehlerFockSpectral.collapsedWeight_zero
