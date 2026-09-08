import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuHessian
import Mathlib.Tactic

/-!
# Entropy gradient and Fisher geometry for the quadratically confined number Gibbs gas

For

  S(β,η) = log Z + β⟨L⟩ + η⟨L²⟩,

the exact Massieu and moment derivative laws imply

  ∂β S = -(β gββ + η gβη),
  ∂η S = -(β gβη + η gηη).

Thus the entropy gradient is the negative Fisher/covariance matrix applied to the
natural-parameter vector.  Contracting with `(β,η)` gives the radial entropy-response
quadratic form.  Positivity/strictness can be supplied separately from covariance
positivity; the identities in this file are unconditional on the confined domain `η>0`.
-/

namespace GppNumberGibbsQuadraticEntropyGeometry

open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticMassieuDerivatives
open GppNumberGibbsQuadraticMassieuHessian

/-- The `β` entropy derivative is minus the first component of the Fisher matrix
applied to the natural-parameter vector `(β,η)`. -/
theorem hasDerivAt_entropy_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun b : ℝ => entropy b η)
      (-(β * fisherBB β η + η * fisherBE β η)) β := by
  have hlog := hasDerivAt_logZ_beta β hη
  have hU := hasDerivAt_internalEnergy_beta β hη
  have hQ := hasDerivAt_quadraticEnergy_beta β hη
  have hβU := (hasDerivAt_id β).mul hU
  have hηQ := (hasDerivAt_const (x := β) η).mul hQ
  have H := (hlog.add hβU).add hηQ
  convert H using 1 <;> simp [entropy] <;> ring

/-- The `η` entropy derivative is minus the second component of the Fisher matrix
applied to the natural-parameter vector `(β,η)`. -/
theorem hasDerivAt_entropy_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt
      (fun e : ℝ => entropy β e)
      (-(β * fisherBE β η + η * fisherEE β η)) η := by
  have hlog := hasDerivAt_logZ_eta β hη
  have hU := hasDerivAt_internalEnergy_eta β hη
  have hQ := hasDerivAt_quadraticEnergy_eta β hη
  have hβU := (hasDerivAt_const (x := η) β).mul hU
  have hηQ := (hasDerivAt_id η).mul hQ
  have H := (hlog.add hβU).add hηQ
  convert H using 1 <;> simp [entropy] <;> ring

/-- Algebraic radial contraction of the entropy-gradient components. -/
theorem radial_entropy_gradient_eq_neg_fisher_quadratic
    (β η : ℝ) :
    β * (-(β * fisherBB β η + η * fisherBE β η)) +
        η * (-(β * fisherBE β η + η * fisherEE β η)) =
      -(β ^ 2 * fisherBB β η +
        2 * β * η * fisherBE β η +
        η ^ 2 * fisherEE β η) := by
  ring

end GppNumberGibbsQuadraticEntropyGeometry

#print axioms GppNumberGibbsQuadraticEntropyGeometry.hasDerivAt_entropy_beta
#print axioms GppNumberGibbsQuadraticEntropyGeometry.hasDerivAt_entropy_eta
#print axioms GppNumberGibbsQuadraticEntropyGeometry.radial_entropy_gradient_eq_neg_fisher_quadratic
