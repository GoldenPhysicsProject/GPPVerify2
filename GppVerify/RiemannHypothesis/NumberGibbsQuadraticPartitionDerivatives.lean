import GppVerify.RiemannHypothesis.NumberGibbsQuadraticGlobalEnvelope
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticTermDerivatives
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticThermodynamics
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# Countable differentiation of the quadratically confined partition function

Quadratic confinement supplies a single summable all-index envelope on a full
open neighborhood of every `β`, while each summand has an exact derivative.
This file closes the first countable-interchange step: differentiation of `Z`
with respect to inverse temperature at fixed positive confinement `η`.
-/

namespace GppNumberGibbsQuadraticPartitionDerivatives

open Set
open GppNumberGibbsTwoParameterStrict
open GppNumberGibbsQuadraticGlobalEnvelope
open GppNumberGibbsQuadraticTermDerivatives
open GppNumberGibbsQuadraticThermodynamics
open GppZetaGibbsSummability

/-- At every `η > 0`, the quadratically confined partition function is
termwise differentiable in `β`.  The derivative is the absolutely convergent
sum of the exact summand derivatives. -/
theorem hasDerivAt_Z_beta_raw
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun b : ℝ => Z b η)
      (∑' n : ℕ, numberGibbsWeight β η n * (-numberLogEnergy n)) β := by
  let B : ℝ := |β| + 1
  let U : Set ℝ := Set.Ioo (β - 1) (β + 1)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η))
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 1)
  have hz1 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n) :=
    summable_gibbsWeight_mul_logEnergy (by norm_num)
  have hd : Summable d := by
    have h := Summable.mul_left C hz1
    simpa [d] using h
  have hderiv : ∀ n b, b ∈ U →
      HasDerivAt
        (fun x : ℝ => numberGibbsWeight x η n)
        (numberGibbsWeight b η n * (-numberLogEnergy n)) b := by
    intro n b hb
    exact numberGibbsWeight_hasDerivAt_beta b η n
  have hbound : ∀ n b, b ∈ U →
      ‖numberGibbsWeight b η n * (-numberLogEnergy n)‖ ≤ d n := by
    intro n b hb
    have hβlower : -B ≤ b := by
      have hβabs : -|β| ≤ β := neg_abs_le β
      dsimp [U] at hb
      dsimp [B]
      linarith
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η b η 1 hη hβlower le_rfl n
    have hw0 : 0 ≤ numberGibbsWeight b η n := numberGibbsWeight_nonneg b η n
    have hL0 : 0 ≤ numberLogEnergy n := numberLogEnergy_nonneg n
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, pow_one, numberLogEnergy, logEnergy] using henv
  have hbase_mem : β ∈ U := by
    dsimp [U]
    constructor <;> linarith
  have hbase : Summable (fun n : ℕ => numberGibbsWeight β η n) :=
    summable_numberGibbsWeight β hη
  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  simpa [Z] using H

end GppNumberGibbsQuadraticPartitionDerivatives

#print axioms GppNumberGibbsQuadraticPartitionDerivatives.hasDerivAt_Z_beta_raw
