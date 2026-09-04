import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMassieuDerivatives
import GppVerify.RiemannHypothesis.NumberGibbsQuadraticMomentDerivatives
import Mathlib.Tactic

/-!
# Hessian of the quadratically confined number-Gibbs Massieu potential

The first derivatives of `log Z` are the negative normalized first and second
log-energy moments.  The countable moment derivatives now promote the next
response layer to the exact covariance entries.  This file keeps the result
in one-variable `HasDerivAt` form in each coordinate, so no multivariable
calculus infrastructure is required.
-/

namespace GppNumberGibbsQuadraticMassieuHessian

open GppNumberGibbsQuadraticThermodynamics
open GppNumberGibbsQuadraticPartitionDerivatives
open GppNumberGibbsQuadraticMomentDerivatives
open GppNumberGibbsQuadraticMassieuDerivatives

/-- Variance entry of the normalized `(L,L^2)` covariance matrix. -/
noncomputable def fisherBB (β η : ℝ) : ℝ :=
  M2 β η / Z β η - (M1 β η / Z β η) ^ 2

/-- Mixed covariance entry of the normalized `(L,L^2)` covariance matrix. -/
noncomputable def fisherBE (β η : ℝ) : ℝ :=
  M3 β η / Z β η - (M1 β η * M2 β η) / Z β η ^ 2

/-- Variance entry for `L^2`. -/
noncomputable def fisherEE (β η : ℝ) : ℝ :=
  M4 β η / Z β η - (M2 β η / Z β η) ^ 2

/-- `∂β ⟨L⟩ = -Var(L)`. -/
theorem hasDerivAt_internalEnergy_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => internalEnergy b η) (-fisherBB β η) β := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have H := (hasDerivAt_M1_beta β hη).div (hasDerivAt_Z_beta β hη) hZne
  convert H using 1
  · simp [internalEnergy]
  · unfold fisherBB
    field_simp [hZne]

/-- `∂η ⟨L⟩ = -Cov(L,L²)`. -/
theorem hasDerivAt_internalEnergy_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => internalEnergy β e) (-fisherBE β η) η := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have H := (hasDerivAt_M1_eta β hη).div (hasDerivAt_Z_eta β hη) hZne
  convert H using 1
  · simp [internalEnergy]
  · unfold fisherBE
    field_simp [hZne]

/-- `∂β ⟨L²⟩ = -Cov(L,L²)`. -/
theorem hasDerivAt_quadraticEnergy_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => quadraticEnergy b η) (-fisherBE β η) β := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have H := (hasDerivAt_M2_beta β hη).div (hasDerivAt_Z_beta β hη) hZne
  convert H using 1
  · simp [quadraticEnergy]
  · unfold fisherBE
    field_simp [hZne]

/-- `∂η ⟨L²⟩ = -Var(L²)`. -/
theorem hasDerivAt_quadraticEnergy_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => quadraticEnergy β e) (-fisherEE β η) η := by
  have hZne : Z β η ≠ 0 := ne_of_gt (Z_pos β hη)
  have H := (hasDerivAt_M2_eta β hη).div (hasDerivAt_Z_eta β hη) hZne
  convert H using 1
  · simp [quadraticEnergy]
  · unfold fisherEE
    field_simp [hZne]

/-- The inverse-temperature second derivative of `log Z` is `Var(L)`. -/
theorem hasDerivAt_negInternalEnergy_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => -internalEnergy b η) (fisherBB β η) β := by
  simpa using (hasDerivAt_internalEnergy_beta β hη).neg

/-- The mixed Massieu response is `Cov(L,L²)`. -/
theorem hasDerivAt_negInternalEnergy_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => -internalEnergy β e) (fisherBE β η) η := by
  simpa using (hasDerivAt_internalEnergy_eta β hη).neg

/-- The other mixed Massieu response agrees with the same covariance entry. -/
theorem hasDerivAt_negQuadraticEnergy_beta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun b : ℝ => -quadraticEnergy b η) (fisherBE β η) β := by
  simpa using (hasDerivAt_quadraticEnergy_beta β hη).neg

/-- The confinement second derivative of `log Z` is `Var(L²)`. -/
theorem hasDerivAt_negQuadraticEnergy_eta
    (β : ℝ) {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun e : ℝ => -quadraticEnergy β e) (fisherEE β η) η := by
  simpa using (hasDerivAt_quadraticEnergy_eta β hη).neg

end GppNumberGibbsQuadraticMassieuHessian

#print axioms GppNumberGibbsQuadraticMassieuHessian.hasDerivAt_internalEnergy_beta
#print axioms GppNumberGibbsQuadraticMassieuHessian.hasDerivAt_internalEnergy_eta
#print axioms GppNumberGibbsQuadraticMassieuHessian.hasDerivAt_quadraticEnergy_beta
#print axioms GppNumberGibbsQuadraticMassieuHessian.hasDerivAt_quadraticEnergy_eta
#print axioms GppNumberGibbsQuadraticMassieuHessian.hasDerivAt_negInternalEnergy_beta
#print axioms GppNumberGibbsQuadraticMassieuHessian.hasDerivAt_negInternalEnergy_eta
#print axioms GppNumberGibbsQuadraticMassieuHessian.hasDerivAt_negQuadraticEnergy_beta
#print axioms GppNumberGibbsQuadraticMassieuHessian.hasDerivAt_negQuadraticEnergy_eta
