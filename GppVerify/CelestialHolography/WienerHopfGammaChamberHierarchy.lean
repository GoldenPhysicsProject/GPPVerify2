import GppVerify.CelestialHolography.WienerHopfGammaBridge
import GppVerify.QuantumGravity.SpectralRhoRecurrence
import Mathlib.Tactic

/-!
# Wiener--Hopf bridge through the full Gamma chamber hierarchy

The base bridge identifies the continuously extended Wiener--Hopf weight with the
normalized `k=0` Gamma/Mehler--Fock chamber.  The exact chamber recurrence then
propagates that identification to every `k` by a finite product of positive step
factors.

No convolution theorem is assumed here: this is the exact algebraic closure of
base normalization plus the already-proved Gamma recurrence.
-/

namespace GppWienerHopfGammaChamberHierarchy

open GppWienerHopfWeightExtension
open GppWienerHopfGammaBridge
open GppSpectralRho

/-- Every normalized Gamma chamber is the base chamber multiplied by the finite
product of recurrence factors encountered on the way from `0` to `k`. -/
theorem rhoGamma_eq_prod_stepFactor_mul_base (k : ℕ) (x : ℝ) :
    rhoGamma k x =
      (((∏ j in Finset.range k, rhoStepFactor j x : ℝ) : ℝ) : ℂ) * rhoGamma 0 x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_eq_add_one, rhoGamma_succ, ih, Finset.prod_range_succ]
      push_cast
      ring

/-- Taking real parts and inserting the global Wiener--Hopf/base-chamber bridge
gives an exact formula for the real spectral density in every chamber. -/
theorem rhoGamma_re_eq_prod_stepFactor_mul_wienerHopf (k : ℕ) (x : ℝ) :
    (rhoGamma k x).re =
      (∏ j in Finset.range k, rhoStepFactor j x) *
        ((2 / Real.pi) * extendedWienerHopfWeight x) := by
  rw [rhoGamma_eq_prod_stepFactor_mul_base]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [rhoGamma_zero_re_eq_two_over_pi_mul_extendedWienerHopfWeight]

/-- The full chamber multiplier relative to the Wiener--Hopf base is strictly
positive. -/
theorem prod_rhoStepFactor_pos (k : ℕ) (x : ℝ) :
    0 < ∏ j in Finset.range k, rhoStepFactor j x := by
  exact Finset.prod_pos fun j _ => rhoStepFactor_pos j x

end GppWienerHopfGammaChamberHierarchy

#print axioms GppWienerHopfGammaChamberHierarchy.rhoGamma_eq_prod_stepFactor_mul_base
#print axioms GppWienerHopfGammaChamberHierarchy.rhoGamma_re_eq_prod_stepFactor_mul_wienerHopf
#print axioms GppWienerHopfGammaChamberHierarchy.prod_rhoStepFactor_pos
