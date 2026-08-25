import GppVerify.QuantumGravity.SpectralGammaPairRecurrence
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Normalized Gamma-family recurrence for the Mehler--Fock spectral weights

For `k >= 0`, define the complex-valued Gamma family corresponding to `m = k+1` by

  rhoGamma k x = 2^(2k+1)/(pi (2k+1)!) * Gamma(k+1+ix) Gamma(k+1-ix).

The exact normalization ratio combines with the Gamma-pair recurrence to give

  rhoGamma (k+1) x
    = 2 ((k+1)^2+x^2)/((k+1)(2k+3)) * rhoGamma k x.

This is the Lean algebraic spine of the discovery-level convolution hierarchy.
No Fourier-transform or normalization integral is assumed here.
-/

namespace GppSpectralRho

open Complex
open GppSpectralGammaPair

/-- The normalized Gamma-family spectral weight, indexed by `m=k+1`. -/
noncomputable def rhoGamma (k : ℕ) (x : ℝ) : ℂ :=
  (((2 : ℝ) ^ (2 * k + 1) /
      (Real.pi * ((2 * k + 1).factorial : ℝ)) : ℝ) : ℂ) *
    gammaPair ((k : ℝ) + 1) x

/-- Exact one-step normalized recurrence for the Gamma-family spectral weights. -/
theorem rhoGamma_succ (k : ℕ) (x : ℝ) :
    rhoGamma (k + 1) x =
      (((2 * ((((k : ℝ) + 1) ^ 2) + x ^ 2)) /
          (((k : ℝ) + 1) * (2 * (k : ℝ) + 3)) : ℝ) : ℂ) *
        rhoGamma k x := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk23 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
  have hfact : (((2 * k + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hgamma := gammaPair_add_one (a := (k : ℝ) + 1) (by positivity) x
  have hindex : ((k + 1 : ℕ) : ℝ) + 1 = ((k : ℝ) + 1) + 1 := by norm_num
  have hfac : (2 * (k + 1) + 1).factorial =
      (2 * k + 3) * (2 * k + 2) * (2 * k + 1).factorial := by
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  unfold rhoGamma
  rw [hindex, hgamma, hfac]
  push_cast
  have hpow : (2 : ℝ) ^ (2 * (k + 1) + 1) = 4 * (2 : ℝ) ^ (2 * k + 1) := by
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
    norm_num
  rw [hpow]
  field_simp [hpi, hk1, hk23, hfact]
  ring

end GppSpectralRho

#print axioms GppSpectralRho.rhoGamma_succ
