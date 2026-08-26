import GppVerify.CelestialHolography.MehlerFockSpectralWeight
import GppVerify.QuantumGravity.GammaHalfModulusIdentity
import Mathlib.Tactic

/-!
# Gamma realization of the collapsed Mehler--Fock spectral weight

The elementary collapsed weight already formalized in the celestial module is

  P_coll(λ) = π λ² / cosh(π λ).

Euler reflection at the half shift gives exactly

  Γ(1/2+iλ) Γ(1/2-iλ) = π / cosh(π λ),

so the collapsed density is the corresponding Gamma product multiplied by λ².
This is a real-axis identity only; no half-plane outer-function or Wiener--Hopf
analyticity claim is made here.
-/

namespace GppMehlerFockGammaCollapsed

open Complex
open GppMehlerFockSpectral

/-- Exact Gamma-product realization of the collapsed spectral density. -/
theorem gamma_product_eq_collapsedWeight (λ : ℝ) :
    ((λ : ℂ) ^ 2) *
        (Complex.Gamma (((1 : ℂ) / 2) + (λ : ℂ) * I) *
          Complex.Gamma (((1 : ℂ) / 2) - (λ : ℂ) * I)) =
      ((collapsedWeight λ : ℝ) : ℂ) := by
  rw [GppGammaHalfModulus.gamma_half_add_mul_gamma_half_sub]
  unfold collapsedWeight
  push_cast
  ring

end GppMehlerFockGammaCollapsed

#print axioms GppMehlerFockGammaCollapsed.gamma_product_eq_collapsedWeight
