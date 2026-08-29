import GppVerify.RiemannHypothesis.PrimeResponseContraction
import GppVerify.CelestialHolography.ArithmeticCompletedDefectCriterion
import Mathlib.Tactic

/-!
# Prime-response scalar transfer operator

The normalized prime response `transfer a t` has absolute value at most one for
`a > 1`.  Here we lift that scalar multiplier to an actual contraction on real
amplitudes and feed it into the completed-defect criterion.  This is still only
a scalar model of the arithmetic transfer: identifying the true
Archimedean/prime amplitude spaces and the genuine Weil quadratic form remains
separate.
-/

namespace GppPrimeResponseTransferOperator

open GppPrimeResponseContraction
open GppArithmeticCompletedDefectCriterion

/-- Scalar transfer acting on a real amplitude. -/
noncomputable def transferOp (a t : ℝ) (y : ℝ) : ℝ :=
  transfer a t * y

/-- The normalized prime-response transfer is norm-contractive. -/
theorem norm_transferOp_le {a : ℝ} (ha : 1 < a) (t y : ℝ) :
    ‖transferOp a t y‖ ≤ ‖y‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold transferOp
  rw [abs_mul]
  have hc : |transfer a t| ≤ 1 := abs_transfer_le_one ha t
  have hy : 0 ≤ |y| := abs_nonneg y
  nlinarith

/-- Prime amplitude obtained by applying the scalar arithmetic transfer to an
ambient real amplitude. -/
noncomputable def primeAmplitude
    {X : Type*} (a t : ℝ) (Ainf : X → ℝ) (x : X) : ℝ :=
  transferOp a t (Ainf x)

/-- The scalar transfer model gives a nonnegative ambient-minus-prime defect. -/
theorem completedDefect_primeAmplitude_nonneg
    {X : Type*} {a : ℝ} (ha : 1 < a) (t : ℝ) (Ainf : X → ℝ) :
    ∀ x, 0 ≤ completedDefect Ainf (primeAmplitude a t Ainf) x := by
  apply completedDefect_nonneg_of_contraction_factorization
    Ainf (primeAmplitude a t Ainf) (transferOp a t)
  · intro x
    rfl
  · intro y
    exact norm_transferOp_le ha t y

end GppPrimeResponseTransferOperator

#print axioms GppPrimeResponseTransferOperator.norm_transferOp_le
#print axioms GppPrimeResponseTransferOperator.completedDefect_primeAmplitude_nonneg
