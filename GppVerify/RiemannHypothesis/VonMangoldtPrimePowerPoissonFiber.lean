import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerFubini
import GppVerify.RiemannHypothesis.PoissonGeometricFiber
import GppVerify.RiemannHypothesis.PrimePoissonRadialBridge
import Mathlib.Tactic

/-!
# Prime-power modes as radial Poisson modes

This file closes the termwise algebra between the canonical von-Mangoldt
prime-power coordinates and the one-sided Poisson geometric fiber.
-/

namespace GppVonMangoldtPrimePowerPoissonFiber

open Real
open GppVonMangoldtPrimePowerReindex
open GppPrimePoissonRadial

/-- The exponential damping on the `m`th prime-power mode is exactly the
`m`th ordinary power of the radial coordinate `p^{-a}`. -/
theorem exp_primePower_damping_eq_rpow_nat
    (p : Nat.Primes) (a : ℝ) (m : ℕ) :
    Real.exp (-(m : ℝ) * Real.log (p : ℕ) * a) =
      ((((p : ℕ) : ℝ) ^ (-a)) : ℝ) ^ m := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by
    exact_mod_cast p.prop.pos
  rw [rpow_neg_eq_exp hp0]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A single canonical prime-power von-Mangoldt cosine summand is exactly the
corresponding radial Poisson Fourier mode. -/
theorem cosineSummand_primePower_eq_radial_mode
    (p : Nat.Primes) (k : ℕ) (a t : ℝ) :
    cosineSummand a t ((p : ℕ) ^ (k + 1)) =
      Real.log (p : ℕ) *
        ((((p : ℕ) : ℝ) ^ (-a)) : ℝ) ^ (k + 1) *
        Real.cos (((k + 1 : ℕ) : ℝ) * (t * Real.log (p : ℕ))) := by
  rw [cosineSummand_primePower p k a t]
  rw [exp_primePower_damping_eq_rpow_nat p a (k + 1)]
  congr 2
  congr 1
  push_cast
  ring

end GppVonMangoldtPrimePowerPoissonFiber

#print axioms GppVonMangoldtPrimePowerPoissonFiber.exp_primePower_damping_eq_rpow_nat
#print axioms GppVonMangoldtPrimePowerPoissonFiber.cosineSummand_primePower_eq_radial_mode
