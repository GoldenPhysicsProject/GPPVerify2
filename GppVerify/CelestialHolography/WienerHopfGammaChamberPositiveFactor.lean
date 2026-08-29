import GppVerify.CelestialHolography.WienerHopfGammaChamberHierarchy
import GppVerify.CelestialHolography.WienerHopfGammaPositiveFactor
import Mathlib.Tactic

/-!
# Positive factorization through the full Gamma chamber hierarchy

The base Gamma / Mehler--Fock chamber already has a canonical positive square-root
factor, while the exact chamber recurrence expresses every higher chamber as the
base density multiplied by a finite product of strictly positive step factors.
This file combines those two results.

For every finite chamber `k` and every real spectral parameter `lam`, the real
Gamma density is therefore an exact square of a strictly positive real factor.
This remains an Archimedean spectral statement; no identification with the signed
completed arithmetic Weil form is made here.
-/

namespace GppWienerHopfGammaChamberPositiveFactor

open GppWienerHopfGammaChamberHierarchy
open GppWienerHopfGammaPositiveFactor
open GppSpectralRho

/-- Canonical positive square-root factor in the `k`th Gamma chamber. -/
noncomputable def gammaChamberFactor (k : ℕ) (lam : ℝ) : ℝ :=
  Real.sqrt (∏ j in Finset.range k, rhoStepFactor j lam) * gammaBaseFactor lam

/-- The full chamber factor is strictly positive for every real spectral parameter. -/
theorem gammaChamberFactor_pos (k : ℕ) (lam : ℝ) :
    0 < gammaChamberFactor k lam := by
  unfold gammaChamberFactor
  exact mul_pos
    (Real.sqrt_pos.2 (prod_rhoStepFactor_pos k lam))
    (gammaBaseFactor_pos lam)

/-- Every normalized Gamma / Mehler--Fock chamber has an exact positive square
factorization on the full real spectral axis, including the removable origin. -/
theorem gammaChamberFactor_sq (k : ℕ) (lam : ℝ) :
    gammaChamberFactor k lam ^ 2 = (rhoGamma k lam).re := by
  unfold gammaChamberFactor
  rw [mul_pow]
  rw [Real.sq_sqrt (prod_rhoStepFactor_pos k lam).le]
  rw [gammaBaseFactor_sq]
  rw [rhoGamma_eq_prod_stepFactor_mul_base]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- In particular no finite Gamma chamber factor vanishes anywhere on the real axis. -/
theorem gammaChamberFactor_ne_zero (k : ℕ) (lam : ℝ) :
    gammaChamberFactor k lam ≠ 0 :=
  ne_of_gt (gammaChamberFactor_pos k lam)

/-- Consequently the real part of every finite normalized Gamma chamber is
strictly positive on the entire real spectral axis. -/
theorem rhoGamma_re_pos (k : ℕ) (lam : ℝ) :
    0 < (rhoGamma k lam).re := by
  rw [← gammaChamberFactor_sq]
  exact sq_pos_of_pos (gammaChamberFactor_pos k lam)

end GppWienerHopfGammaChamberPositiveFactor

#print axioms GppWienerHopfGammaChamberPositiveFactor.gammaChamberFactor_pos
#print axioms GppWienerHopfGammaChamberPositiveFactor.gammaChamberFactor_sq
#print axioms GppWienerHopfGammaChamberPositiveFactor.rhoGamma_re_pos
