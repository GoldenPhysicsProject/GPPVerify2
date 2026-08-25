import GppVerify.RiemannHypothesis.ZetaGibbsMomentBridge
import Mathlib.Tactic

/-!
# Fisher positivity of the zeta Gibbs family

For real `β > 1`, the logarithmic second response

  ζ''(β)/ζ(β) - (ζ'(β)/ζ(β))^2

is exactly the complex embedding of the Gibbs variance of the arithmetic energy
`log(n+1)`. Consequently the response is real and nonnegative on the honest Gibbs
domain. No positivity is asserted after analytic continuation into the critical strip.
-/

namespace GppZetaGibbsFisher

open Complex LSeries
open GppZetaGibbsSummability
open GppZetaGibbsMoments
open GppZetaGibbsMomentBridge

/-- Unnormalized partition sum. -/
noncomputable def Z (β : ℝ) : ℝ := ∑' n, gibbsWeight β n

/-- Unnormalized first log-energy moment. -/
noncomputable def M1 (β : ℝ) : ℝ := ∑' n, gibbsWeight β n * logEnergy n

/-- Unnormalized second log-energy moment. -/
noncomputable def M2 (β : ℝ) : ℝ := ∑' n, gibbsWeight β n * (logEnergy n) ^ 2

/-- Real Gibbs variance in quotient form. -/
noncomputable def logEnergyVariance (β : ℝ) : ℝ :=
  M2 β / Z β - (M1 β / Z β) ^ 2

/-- Complex logarithmic second response of zeta. -/
noncomputable def zetaVarianceResponse (β : ℝ) : ℂ :=
  iteratedDeriv 2 riemannZeta (β : ℂ) / riemannZeta (β : ℂ) -
    (deriv riemannZeta (β : ℂ) / riemannZeta (β : ℂ)) ^ 2

/-- The zeta logarithmic second response is exactly the embedded Gibbs variance. -/
theorem zetaVarianceResponse_eq_ofReal_logEnergyVariance {β : ℝ} (hβ : 1 < β) :
    zetaVarianceResponse β = (logEnergyVariance β : ℂ) := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  rw [zetaVarianceResponse, logEnergyVariance, M2, M1, Z]
  rw [iteratedDeriv_two_riemannZeta_eq_logSqMomentLSeries hs]
  rw [LSeries_logMul_logMul_one_eq_ofReal_secondMoment hβ]
  rw [deriv_riemannZeta_eq_neg_logMomentLSeries hs]
  rw [LSeries_logMul_one_eq_ofReal_firstMoment hβ]
  rw [riemannZeta_eq_LSeries_one hs]
  rw [LSeries_one_eq_ofReal_gibbsWeight_tsum hβ]
  norm_cast
  ring

/-- The Gibbs logarithmic-energy variance is nonnegative for every `β > 1`. -/
theorem logEnergyVariance_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ logEnergyVariance β := by
  exact gibbs_logEnergy_variance_nonneg hβ

/-- The complex zeta response lies on the real axis for `β > 1`. -/
theorem zetaVarianceResponse_im_eq_zero {β : ℝ} (hβ : 1 < β) :
    (zetaVarianceResponse β).im = 0 := by
  rw [zetaVarianceResponse_eq_ofReal_logEnergyVariance hβ]
  simp

/-- Fisher / susceptibility positivity of the zeta response on the honest Gibbs axis. -/
theorem zetaVarianceResponse_re_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ (zetaVarianceResponse β).re := by
  rw [zetaVarianceResponse_eq_ofReal_logEnergyVariance hβ]
  simpa using logEnergyVariance_nonneg hβ

/-- Dimensionless number-gas heat capacity. -/
noncomputable def heatCapacity (β : ℝ) : ℝ := β ^ 2 * logEnergyVariance β

/-- Thermodynamic stability: heat capacity is nonnegative for `β > 1`. -/
theorem heatCapacity_nonneg {β : ℝ} (hβ : 1 < β) :
    0 ≤ heatCapacity β := by
  unfold heatCapacity
  exact mul_nonneg (sq_nonneg β) (logEnergyVariance_nonneg hβ)

/-- Entropy derivative written in the exact Gibbs-response form. -/
noncomputable def entropyBetaDerivative (β : ℝ) : ℝ :=
  -β * logEnergyVariance β

/-- Entropy decreases with inverse temperature on the honest Gibbs domain. -/
theorem entropyBetaDerivative_nonpos {β : ℝ} (hβ : 1 < β) :
    entropyBetaDerivative β ≤ 0 := by
  unfold entropyBetaDerivative
  have hβ0 : 0 ≤ β := le_trans (by norm_num) hβ.le
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ0) (logEnergyVariance_nonneg hβ)

/-- Exact Fisher-geometry algebra: the square of the entropy response equals
heat capacity times the Fisher metric coefficient (the log-energy variance).
This is the coordinate-β version of `C = (dS/dτ)^2` once `dτ = sqrt(g) dβ`
is introduced. -/
theorem entropyBetaDerivative_sq_eq_heatCapacity_mul_variance (β : ℝ) :
    entropyBetaDerivative β ^ 2 = heatCapacity β * logEnergyVariance β := by
  unfold entropyBetaDerivative heatCapacity
  ring

/-- On the honest Gibbs domain the squared entropy response is nonnegative. -/
theorem entropyBetaDerivative_sq_nonneg (β : ℝ) :
    0 ≤ entropyBetaDerivative β ^ 2 := by
  exact sq_nonneg _

end GppZetaGibbsFisher

#print axioms GppZetaGibbsFisher.zetaVarianceResponse_eq_ofReal_logEnergyVariance
#print axioms GppZetaGibbsFisher.logEnergyVariance_nonneg
#print axioms GppZetaGibbsFisher.zetaVarianceResponse_re_nonneg
#print axioms GppZetaGibbsFisher.heatCapacity_nonneg
#print axioms GppZetaGibbsFisher.entropyBetaDerivative_nonpos
#print axioms GppZetaGibbsFisher.entropyBetaDerivative_sq_eq_heatCapacity_mul_variance
