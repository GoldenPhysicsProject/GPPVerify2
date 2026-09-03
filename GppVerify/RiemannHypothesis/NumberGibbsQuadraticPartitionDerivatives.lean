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
termwise differentiable in `β`. The derivative is the absolutely convergent
sum of the exact summand derivatives. -/
theorem hasDerivAt_Z_beta_raw
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun b : ℝ => Z b η)
      (∑' n : ℕ, numberGibbsWeight β η n * (-numberLogEnergy n)) β := by
  let B : ℝ := |β| + 1
  let U : Set ℝ := Set.Ioo (β - 1) (β + 1)
  let C : ℝ := Real.exp ((B + 2) ^ 2 / (4 * η))
  let g : ℕ → ℝ → ℝ := fun n b => numberGibbsWeight b η n
  let g' : ℕ → ℝ → ℝ := fun n b =>
    numberGibbsWeight b η n * (-numberLogEnergy n)
  let d : ℕ → ℝ := fun n => C * (gibbsWeight 2 n * logEnergy n ^ 1)

  have hz1 : Summable (fun n : ℕ => gibbsWeight 2 n * logEnergy n ^ 1) := by
    simpa [pow_one] using
      (summable_gibbsWeight_mul_logEnergy (β := 2) (by norm_num : (1 : ℝ) < 2))
  have hd : Summable d := by
    simpa [d, C] using
      (summable_global_derivative_envelope B η 1 hz1)

  have hderiv : ∀ n b, b ∈ U → HasDerivAt (g n) (g' n b) b := by
    intro n b hb
    simpa [g, g'] using numberGibbsWeight_hasDerivAt_beta b η n

  have hbound : ∀ n b, b ∈ U → ‖g' n b‖ ≤ d n := by
    intro n b hb
    have hβlower : -B ≤ b := by
      calc
        -B = -(|β| + 1) := by rfl
        _ ≤ β - 1 := by linarith [neg_abs_le β]
        _ ≤ b := le_of_lt hb.1
    have henv := numberGibbs_moment_le_const_mul_gibbs_moment_two_uniform
      B η b η 1 hη hβlower le_rfl n
    have hw0 : 0 ≤ numberGibbsWeight b η n := numberGibbsWeight_nonneg b η n
    have hL0 : 0 ≤ numberLogEnergy n := by
      simpa [numberLogEnergy, logEnergy] using logEnergy_nonneg n
    dsimp [g']
    rw [abs_mul, abs_neg, abs_of_nonneg hw0, abs_of_nonneg hL0]
    simpa [d, C, pow_one, numberLogEnergy, logEnergy] using henv

  have hbase_mem : β ∈ U := by
    dsimp [U]
    constructor <;> linarith
  have hbase : Summable (fun n : ℕ => g n β) := by
    simpa [g] using summable_numberGibbsWeight β hη

  have H := hasDerivAt_tsum_of_isPreconnected
    hd isOpen_Ioo isPreconnected_Ioo hderiv hbound hbase_mem hbase hbase_mem
  simpa [Z, g, g'] using H

end GppNumberGibbsQuadraticPartitionDerivatives

#print axioms GppNumberGibbsQuadraticPartitionDerivatives.hasDerivAt_Z_beta_raw
