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

The conjugate Gamma-pair symmetry also makes every normalized chamber weight exactly
even under `x -> -x`.
-/

namespace GppSpectralRho

open Complex
open GppSpectralGammaPair

/-- The normalized Gamma-family spectral weight, indexed by `m=k+1`. -/
noncomputable def rhoGamma (k : ℕ) (x : ℝ) : ℂ :=
  (((2 : ℝ) ^ (2 * k + 1) /
      (Real.pi * ((2 * k + 1).factorial : ℝ)) : ℝ) : ℂ) *
    gammaPair ((k : ℝ) + 1) x

/-- Every normalized Gamma/Mehler--Fock chamber weight is exactly even in the
principal-series spectral parameter. -/
theorem rhoGamma_neg (k : ℕ) (x : ℝ) :
    rhoGamma k (-x) = rhoGamma k x := by
  unfold rhoGamma
  rw [gammaPair_neg]

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

/-- Real one-step multiplier in the normalized chamber recurrence. -/
noncomputable def rhoStepFactor (k : ℕ) (x : ℝ) : ℝ :=
  2 * ((((k : ℝ) + 1) ^ 2) + x ^ 2) /
    (((k : ℝ) + 1) * (2 * (k : ℝ) + 3))

/-- The chamber multiplier is strictly positive for every real spectral parameter. -/
theorem rhoStepFactor_pos (k : ℕ) (x : ℝ) :
    0 < rhoStepFactor k x := by
  unfold rhoStepFactor
  positivity

/-- **Sharp chamber amplification threshold.** The normalized spectral weight grows
from chamber `k` to `k+1` exactly when `2 x^2 > k+1`.  Thus the recurrence suppresses
the central spectral region and amplifies the sufficiently large-|x| tail. -/
theorem rhoStepFactor_gt_one_iff (k : ℕ) (x : ℝ) :
    1 < rhoStepFactor k x ↔ ((k : ℝ) + 1) < 2 * x ^ 2 := by
  unfold rhoStepFactor
  have hden : 0 < ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by positivity
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- The threshold itself is the unique equality locus for the chamber multiplier. -/
theorem rhoStepFactor_eq_one_iff (k : ℕ) (x : ℝ) :
    rhoStepFactor k x = 1 ↔ 2 * x ^ 2 = ((k : ℝ) + 1) := by
  unfold rhoStepFactor
  have hden : 0 < ((k : ℝ) + 1) * (2 * (k : ℝ) + 3) := by positivity
  rw [div_eq_iff hden.ne']
  constructor <;> intro h <;> nlinarith

end GppSpectralRho

#print axioms GppSpectralRho.rhoGamma_neg
#print axioms GppSpectralRho.rhoGamma_succ
#print axioms GppSpectralRho.rhoStepFactor_pos
#print axioms GppSpectralRho.rhoStepFactor_gt_one_iff
#print axioms GppSpectralRho.rhoStepFactor_eq_one_iff
