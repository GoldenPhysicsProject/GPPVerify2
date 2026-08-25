import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Mehler-Fock / Wiener-Hopf spectral weight algebra

This file records the exact elementary hyperbolic-weight relation discovered in
`GPPDiscovery2`.  The Gamma-function interpretation is deliberately left outside
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

/-- The product of the two weights collapses to the half-shifted hyperbolic factor. -/
theorem weight_product {λ : ℝ}
    (hs : Real.sinh (Real.pi * λ) ≠ 0)
    (hc : Real.cosh (Real.pi * λ) ≠ 0) :
    wienerHopfWeight λ * mehlerFockWeight λ =
      Real.pi * λ ^ 2 / Real.cosh (Real.pi * λ) := by
  unfold wienerHopfWeight mehlerFockWeight
  field_simp [hs, hc]
  ring

/-- Both explicitly defined weights vanish at the origin under Lean's totalized division. -/
theorem mehlerFockWeight_zero : mehlerFockWeight 0 = 0 := by
  simp [mehlerFockWeight]

end GppMehlerFockSpectral

#print axioms GppMehlerFockSpectral.weight_product
#print axioms GppMehlerFockSpectral.mehlerFockWeight_zero
