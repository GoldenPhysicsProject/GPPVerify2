import GppVerify.RiemannHypothesis.CausalHeatBoundaryAnomaly
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Finite causal prime-resolvent anomaly

The local causal prime resolvent is built from unilateral translations at repetition lengths

  a_m = (m+1) log p,

with Euler-log coefficients

  p^{-(m+1)/2} / (m+1).

The scalar boundary anomaly contributes an extra factor `a_m`.  The repetition number
therefore cancels exactly, leaving the standard prime-orbit coefficient

  log p * p^{-(m+1)/2}.

This file records that finite algebraic layer and its finite-sum consequence.  It does not
construct the resolvent operator, prove trace-class summability, or pass to the infinite
prime/repetition sum.
-/

namespace GppCausalPrimeResolventFinite

open Finset
open GppCausalHeatBoundaryAnomaly

/-- Positive repetition number, indexed from zero to avoid a spurious `m=0` denominator. -/
def repetition (m : ℕ) : ℕ := m + 1

/-- Causal translation length of the `m`-th repetition of the prime orbit. -/
noncomputable def repetitionLength (p : ℝ) (m : ℕ) : ℝ :=
  (repetition m : ℝ) * Real.log p

/-- Euler-log resolvent coefficient attached to the `m`-th repetition. -/
noncomputable def resolventWeight (p : ℝ) (m : ℕ) : ℝ :=
  p ^ (-(repetition m : ℝ) / 2) / (repetition m : ℝ)

/-- The scalar heat-boundary anomaly at a translation length. -/
noncomputable def scalarHeatAnomaly (t a : ℝ) : ℝ :=
  a * heatKernelGaussian t a

/-- **Euler repetition cancellation.**  Multiplying the resolvent coefficient by the
boundary anomaly cancels the repetition denominator exactly. -/
theorem resolventWeight_mul_scalarHeatAnomaly
    (p t : ℝ) (m : ℕ) :
    resolventWeight p m * scalarHeatAnomaly t (repetitionLength p m) =
      Real.log p * p ^ (-(repetition m : ℝ) / 2) *
        heatKernelGaussian t (repetitionLength p m) := by
  have hm : (repetition m : ℝ) ≠ 0 := by
    positivity
  unfold resolventWeight scalarHeatAnomaly repetitionLength
  field_simp [hm]
  ring

/-- Closed Gaussian form of one weighted prime repetition anomaly. -/
theorem resolventWeight_mul_scalarHeatAnomaly_closed
    (p t : ℝ) (m : ℕ) :
    resolventWeight p m * scalarHeatAnomaly t (repetitionLength p m) =
      Real.log p * p ^ (-(repetition m : ℝ) / 2) *
        (Real.exp (-((repetition m : ℝ) * Real.log p) ^ 2 / (4 * t)) /
          Real.sqrt (4 * Real.pi * t)) := by
  rw [resolventWeight_mul_scalarHeatAnomaly]
  unfold heatKernelGaussian repetitionLength
  rfl

/-- Finite causal resolvent anomaly through repetition index `M-1`. -/
noncomputable def finiteResolventAnomaly (p t : ℝ) (M : ℕ) : ℝ :=
  ∑ m in range M,
    resolventWeight p m * scalarHeatAnomaly t (repetitionLength p m)

/-- Exact finite prime-orbit heat sum produced by the causal resolvent anomaly. -/
theorem finiteResolventAnomaly_eq_primeHeatSum
    (p t : ℝ) (M : ℕ) :
    finiteResolventAnomaly p t M =
      ∑ m in range M,
        Real.log p * p ^ (-(repetition m : ℝ) / 2) *
          heatKernelGaussian t (repetitionLength p m) := by
  unfold finiteResolventAnomaly
  apply Finset.sum_congr rfl
  intro m hm
  exact resolventWeight_mul_scalarHeatAnomaly p t m

end GppCausalPrimeResolventFinite

#print axioms GppCausalPrimeResolventFinite.resolventWeight_mul_scalarHeatAnomaly
#print axioms GppCausalPrimeResolventFinite.resolventWeight_mul_scalarHeatAnomaly_closed
#print axioms GppCausalPrimeResolventFinite.finiteResolventAnomaly_eq_primeHeatSum
