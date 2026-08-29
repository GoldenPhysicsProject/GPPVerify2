import GppVerify.CelestialHolography.MehlerFockSpectralWeight
import GppVerify.QuantumGravity.GammaHalfModulusIdentity
import Mathlib.Tactic

/-!
# Gamma realization of the collapsed Mehler--Fock spectral weight

The elementary collapsed weight already formalized in the celestial module is

  P_coll(lam) = pi lam^2 / cosh(pi lam).

Euler reflection at the half shift gives exactly

  Gamma(1/2+i lam) Gamma(1/2-i lam) = pi / cosh(pi lam),

so the collapsed density is the corresponding Gamma product multiplied by lam^2.
Combining this with the elementary Wiener--Hopf / Mehler--Fock product identity
closes the real-axis spectral-weight bridge. No half-plane outer-function or
Wiener--Hopf analyticity claim is made here.
-/

namespace GppMehlerFockGammaCollapsed

open Complex
open GppMehlerFockSpectral

/-- Exact Gamma-product realization of the collapsed spectral density. -/
theorem gamma_product_eq_collapsedWeight (lam : ℝ) :
    ((lam : ℂ) ^ 2) *
        (Complex.Gamma (((1 : ℂ) / 2) + (lam : ℂ) * I) *
          Complex.Gamma (((1 : ℂ) / 2) - (lam : ℂ) * I)) =
      ((collapsedWeight lam : ℝ) : ℂ) := by
  rw [GppGammaHalfModulus.gamma_half_add_mul_gamma_half_sub]
  unfold collapsedWeight
  push_cast
  ring

/-- **Closed real-axis Wiener--Hopf / Mehler--Fock / Gamma bridge.** Away from
the zero of the `sinh` denominator, the product of the two elementary spectral
weights is exactly `lam^2` times the half-shifted Gamma reflection product. -/
theorem wienerHopf_mul_mehlerFock_eq_gamma_product
    {lam : ℝ} (hs : Real.sinh (Real.pi * lam) ≠ 0) :
    (((wienerHopfWeight lam * mehlerFockWeight lam : ℝ) : ℂ)) =
      ((lam : ℂ) ^ 2) *
        (Complex.Gamma (((1 : ℂ) / 2) + (lam : ℂ) * I) *
          Complex.Gamma (((1 : ℂ) / 2) - (lam : ℂ) * I)) := by
  have hc : Real.cosh (Real.pi * lam) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  rw [weight_product hs hc]
  symm
  exact gamma_product_eq_collapsedWeight lam

end GppMehlerFockGammaCollapsed

#print axioms GppMehlerFockGammaCollapsed.gamma_product_eq_collapsedWeight
#print axioms GppMehlerFockGammaCollapsed.wienerHopf_mul_mehlerFock_eq_gamma_product
