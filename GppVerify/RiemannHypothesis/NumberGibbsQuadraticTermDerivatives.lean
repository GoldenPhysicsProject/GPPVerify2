import GppVerify.RiemannHypothesis.NumberGibbsQuadraticConfinement
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Pointwise parameter derivatives for the quadratically confined number-Gibbs family

The uniform quadratic-confinement estimates already provide common summable
log-moment envelopes on compact parameter regions.  This file isolates the
other ingredient needed for termwise differentiation: the exact derivative of
each Gibbs summand with respect to each parameter.
-/

namespace GppNumberGibbsQuadraticTermDerivatives

open GppNumberGibbsTwoParameterStrict

/-- Differentiating one number-Gibbs summand in the inverse-temperature
parameter contributes one factor `-log(n+1)`. -/
theorem numberGibbsWeight_hasDerivAt_beta
    (β η : ℝ) (n : ℕ) :
    HasDerivAt
      (fun b : ℝ => numberGibbsWeight b η n)
      (numberGibbsWeight β η n * (-numberLogEnergy n)) β := by
  let L : ℝ := numberLogEnergy n
  have hinner : HasDerivAt
      (fun b : ℝ => -b * L - η * L ^ 2) (-L) β := by
    convert ((hasDerivAt_id β).neg.mul_const L).sub_const (η * L ^ 2) using 1 <;> ring
  have h := (Real.hasDerivAt_exp (-β * L - η * L ^ 2)).comp β hinner
  simpa [numberGibbsWeight, numberLogEnergy, L] using h

/-- Differentiating one number-Gibbs summand in the quadratic-confinement
parameter contributes one factor `-(log(n+1))^2`. -/
theorem numberGibbsWeight_hasDerivAt_eta
    (β η : ℝ) (n : ℕ) :
    HasDerivAt
      (fun e : ℝ => numberGibbsWeight β e n)
      (numberGibbsWeight β η n * (-(numberLogEnergy n) ^ 2)) η := by
  let L : ℝ := numberLogEnergy n
  have hinner : HasDerivAt
      (fun e : ℝ => -β * L - e * L ^ 2) (-(L ^ 2)) η := by
    convert (hasDerivAt_const η (-β * L)).sub
      ((hasDerivAt_id η).mul_const (L ^ 2)) using 1 <;> ring
  have h := (Real.hasDerivAt_exp (-β * L - η * L ^ 2)).comp η hinner
  simpa [numberGibbsWeight, numberLogEnergy, L] using h

end GppNumberGibbsQuadraticTermDerivatives

#print axioms GppNumberGibbsQuadraticTermDerivatives.numberGibbsWeight_hasDerivAt_beta
#print axioms GppNumberGibbsQuadraticTermDerivatives.numberGibbsWeight_hasDerivAt_eta