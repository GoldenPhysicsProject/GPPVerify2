import GppVerify.RiemannHypothesis.ZetaGibbsFisherStrict
import GppVerify.RiemannHypothesis.ZetaGibbsMomentBridge
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Real thermodynamic derivatives of the zeta Gibbs family

On the honest Gibbs half-line `β > 1`, define the real partition function as the
real part of zeta, the log-partition potential `A = log Z`, and the mean-energy
response as the real part of the negative zeta logarithmic derivative.  The
complex analytic calculus already formalized in the project then gives exactly

  A' = -U,   U' = -g,

where `g` is the genuine Gibbs log-energy variance.
-/

namespace GppZetaGibbsThermodynamicDerivatives

open Complex LSeries Set
open GppZetaGibbsSummability
open GppZetaGibbsMoments
open GppZetaGibbsMomentBridge
open GppZetaGibbsFisher
open GppZetaGibbsFisherStrict
open GppZetaThirdCumulantStrict
open GppVonMangoldtCumulantDerivativeBridge

/-- Real-axis zeta partition function. -/
noncomputable def zetaPartition (β : ℝ) : ℝ :=
  (riemannZeta (β : ℂ)).re

/-- Real zeta Gibbs log-partition potential. -/
noncomputable def zetaLogPartition (β : ℝ) : ℝ :=
  Real.log (zetaPartition β)

/-- Mean log-energy response, written as the real negative logarithmic derivative. -/
noncomputable def zetaMeanEnergy (β : ℝ) : ℝ :=
  (negZetaLogDeriv (β : ℂ)).re

/-- On `β>1`, zeta is the complex embedding of the positive Gibbs partition sum. -/
theorem riemannZeta_eq_ofReal_gibbsWeight_tsum
    {β : ℝ} (hβ : 1 < β) :
    riemannZeta (β : ℂ) = ((∑' n, gibbsWeight β n : ℝ) : ℂ) := by
  rw [riemannZeta_eq_LSeries_one (by simpa using hβ)]
  exact LSeries_one_eq_ofReal_gibbsWeight_tsum hβ

/-- The real-axis partition is strictly positive. -/
theorem zetaPartition_pos {β : ℝ} (hβ : 1 < β) :
    0 < zetaPartition β := by
  have hz := riemannZeta_eq_ofReal_gibbsWeight_tsum hβ
  have hp := gibbsWeight_tsum_pos hβ
  unfold zetaPartition
  rw [hz]
  simpa using hp

/-- Zeta itself is the complex embedding of `zetaPartition` on the honest real axis. -/
theorem riemannZeta_eq_ofReal_zetaPartition
    {β : ℝ} (hβ : 1 < β) :
    riemannZeta (β : ℂ) = (zetaPartition β : ℂ) := by
  have hz := riemannZeta_eq_ofReal_gibbsWeight_tsum hβ
  unfold zetaPartition
  rw [hz]
  simp

/-- The log-partition derivative is minus the mean log-energy response. -/
theorem hasDerivAt_zetaLogPartition
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt zetaLogPartition (-zetaMeanEnergy β) β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hsset : (β : ℂ) ∈ zetaHalfPlane := hs
  have h0c : HasDerivAt riemannZeta (deriv riemannZeta (β : ℂ)) (β : ℂ) :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane (β : ℂ) hsset).differentiableAt.hasDerivAt
  have h0r : HasDerivAt
      (fun x : ℝ => (riemannZeta (x : ℂ)).re)
      (deriv riemannZeta (β : ℂ)).re β :=
    h0c.real_of_complex
  have hpne : zetaPartition β ≠ 0 := (zetaPartition_pos hβ).ne'
  have hlog := h0r.log hpne
  have hz : riemannZeta (β : ℂ) = (zetaPartition β : ℂ) :=
    riemannZeta_eq_ofReal_zetaPartition hβ
  have hdivre :
      (deriv riemannZeta (β : ℂ) / riemannZeta (β : ℂ)).re =
        (deriv riemannZeta (β : ℂ)).re / zetaPartition β := by
    rw [hz]
    simp [div_eq_mul_inv]
  have hcoef :
      (deriv riemannZeta (β : ℂ)).re / zetaPartition β =
        -zetaMeanEnergy β := by
    unfold zetaMeanEnergy negZetaLogDeriv
    rw [map_neg, hdivre]
    ring
  simpa [zetaLogPartition, zetaPartition, hcoef] using hlog

/-- The mean-energy derivative is minus the genuine Gibbs Fisher metric. -/
theorem hasDerivAt_zetaMeanEnergy
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt zetaMeanEnergy (-logEnergyVariance β) β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hsset : (β : ℂ) ∈ zetaHalfPlane := hs
  have h0 : HasDerivAt riemannZeta (deriv riemannZeta (β : ℂ)) (β : ℂ) :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane (β : ℂ) hsset).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (deriv riemannZeta)
      (deriv (deriv riemannZeta) (β : ℂ)) (β : ℂ) :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv (β : ℂ) hsset).differentiableAt.hasDerivAt
  have hne : riemannZeta (β : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_right_half_plane hs
  have hdiff : DifferentiableAt ℂ negZetaLogDeriv (β : ℂ) :=
    ((h1.div h0 hne).neg).differentiableAt
  have hreal : HasDerivAt
      (fun x : ℝ => (negZetaLogDeriv (x : ℂ)).re)
      (deriv negZetaLogDeriv (β : ℂ)).re β :=
    hdiff.hasDerivAt.real_of_complex
  rw [deriv_negZetaLogDeriv_eq_neg_zetaVarianceResponse hβ] at hreal
  rw [zetaVarianceResponse_eq_ofReal_logEnergyVariance hβ] at hreal
  simpa [zetaMeanEnergy] using hreal

end GppZetaGibbsThermodynamicDerivatives

#print axioms GppZetaGibbsThermodynamicDerivatives.zetaPartition_pos
#print axioms GppZetaGibbsThermodynamicDerivatives.hasDerivAt_zetaLogPartition
#print axioms GppZetaGibbsThermodynamicDerivatives.hasDerivAt_zetaMeanEnergy
