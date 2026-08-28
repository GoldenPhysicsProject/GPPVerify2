import GppVerify.QuantumGravity.SpectralRhoMehlerFockBridge
import GppVerify.CelestialHolography.WienerHopfWeightExtension
import Mathlib.Tactic

/-!
# Normalized Gamma / Wiener--Hopf phase-space bridge

The scalar-cut paper identifies

  P(lambda) = pi*lambda/sinh(pi*lambda)

as the principal-series phase-space weight. The spectral Gamma family has base member

  rhoGamma 0 lambda = 2*lambda/sinh(pi*lambda)

away from the removable origin. Using the already-proved continuous extension of `P`,
this file closes the identity on all real lambda.
-/

namespace GppSpectralRhoWienerHopf

open GppSpectralRho
open GppSpectralRhoMehlerFock
open GppMehlerFockSpectral
open GppWienerHopfWeightExtension

/-- The base normalized Gamma chamber is exactly `2/pi` times the continuously extended
Wiener--Hopf / scalar-cut phase-space weight, including at the removable origin. -/
theorem rhoGamma_zero_eq_extendedWienerHopf (lam : ℝ) :
    rhoGamma 0 lam =
      (((2 / Real.pi) * extendedWienerHopfWeight lam : ℝ) : ℂ) := by
  by_cases hlam : lam = 0
  · subst lam
    rw [rhoGamma_zero_zero, extendedWienerHopfWeight_zero]
    norm_num
  · rw [rhoGamma_zero_eq_mehlerFock lam hlam]
    rw [extendedWienerHopfWeight_eq hlam]
    unfold wienerHopfWeight
    norm_cast
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hsinh : Real.sinh (Real.pi * lam) ≠ 0 := by
      exact Real.sinh_ne_zero.mpr (mul_ne_zero hpi hlam)
    field_simp [hpi, hsinh]
    ring

/-- Equivalently, the extended scalar-cut phase-space weight is `pi/2` times the base
Gamma chamber, as a complex-valued identity. -/
theorem extendedWienerHopf_eq_pi_half_rhoGamma (lam : ℝ) :
    ((extendedWienerHopfWeight lam : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * rhoGamma 0 lam := by
  rw [rhoGamma_zero_eq_extendedWienerHopf]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]
  ring

end GppSpectralRhoWienerHopf

#print axioms GppSpectralRhoWienerHopf.rhoGamma_zero_eq_extendedWienerHopf
#print axioms GppSpectralRhoWienerHopf.extendedWienerHopf_eq_pi_half_rhoGamma
