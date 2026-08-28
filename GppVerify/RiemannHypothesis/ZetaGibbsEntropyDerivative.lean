import GppVerify.RiemannHypothesis.ZetaGibbsThermodynamicDerivatives
import GppVerify.RiemannHypothesis.ZetaGibbsStrictThermodynamics
import GppVerify.RiemannHypothesis.ZetaGibbsCumulantDerivative
import Mathlib.Tactic

/-!
# Differential entropy law for the zeta Gibbs family

The project already identifies the real-axis Massieu potential and mean log-energy by

  A'(β) = -U(β),    U'(β) = -g(β),

where `g` is the genuine Gibbs variance of `log(n+1)`.  This file packages the corresponding
entropy potential

  S(β) = A(β) + β U(β)

and proves the actual differential identity

  S'(β) = -β g(β).

The cumulant flow `g'(β) = -κ₃(β)` then gives the exact entropy-response curvature

  (S')'(β) = -g(β) + β κ₃(β).

Thus the previously formalized `entropyBetaDerivative` is not merely a response ansatz: it
is the derivative of an explicit entropy potential on the honest Gibbs half-line `β > 1`.
No analytic continuation of this thermodynamic interpretation is asserted, and no global
sign is asserted for the curvature because its two terms compete.
-/

namespace GppZetaGibbsEntropyDerivative

open GppZetaGibbsFisher
open GppZetaGibbsStrictThermodynamics
open GppZetaGibbsThermodynamicDerivatives
open GppZetaGibbsCumulantDerivative

/-- Entropy potential written directly in terms of the real zeta log-partition and mean
log-energy response. -/
noncomputable def zetaEntropy (β : ℝ) : ℝ :=
  zetaLogPartition β + β * zetaMeanEnergy β

/-- The entropy potential has derivative `-β` times the Gibbs Fisher variance. -/
theorem hasDerivAt_zetaEntropy
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt zetaEntropy (entropyBetaDerivative β) β := by
  have hA := hasDerivAt_zetaLogPartition hβ
  have hU := hasDerivAt_zetaMeanEnergy hβ
  have hS := hA.add ((hasDerivAt_id β).mul hU)
  have hcoef :
      -zetaMeanEnergy β +
          (1 * zetaMeanEnergy β + β * (-logEnergyVariance β)) =
        entropyBetaDerivative β := by
    unfold entropyBetaDerivative
    ring
  rw [← hcoef]
  simpa only [zetaEntropy] using hS

/-- Consequently the zeta Gibbs entropy is strictly decreasing with inverse temperature
throughout the honest Gibbs domain. -/
theorem deriv_zetaEntropy_neg
    {β : ℝ} (hβ : 1 < β) :
    deriv zetaEntropy β < 0 := by
  rw [(hasDerivAt_zetaEntropy hβ).deriv]
  exact entropyBetaDerivative_neg hβ

/-- The derivative of entropy is exactly minus heat capacity divided by inverse
temperature. -/
theorem deriv_zetaEntropy_eq_neg_heatCapacity_div_beta
    {β : ℝ} (hβ : 1 < β) :
    deriv zetaEntropy β = -heatCapacity β / β := by
  rw [(hasDerivAt_zetaEntropy hβ).deriv]
  exact entropyBetaDerivative_eq_neg_heatCapacity_div_beta (by linarith)

/-- The positive entropy-loss rate recovers heat capacity after multiplication by `β`. -/
theorem heatCapacity_eq_neg_beta_mul_deriv_zetaEntropy
    {β : ℝ} (hβ : 1 < β) :
    heatCapacity β = -β * deriv zetaEntropy β := by
  rw [(hasDerivAt_zetaEntropy hβ).deriv]
  exact heatCapacity_eq_neg_beta_mul_entropyBetaDerivative β

/-- **Exact entropy-response curvature law.**  Differentiating
`S'(β) = -β κ₂(β)` and using `κ₂'(β) = -κ₃(β)` gives

`(S')'(β) = -κ₂(β) + β κ₃(β)`.

No sign is asserted: variance and skewness compete. -/
theorem hasDerivAt_entropyBetaDerivative
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt entropyBetaDerivative
      (-logEnergyVariance β + β * logEnergyThirdCumulant β) β := by
  have hvar := hasDerivAt_logEnergyVariance hβ
  have hprod :
      HasDerivAt
        (fun y : ℝ => y * logEnergyVariance y)
        (logEnergyVariance β + β * (-logEnergyThirdCumulant β)) β := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id β).mul hvar
  have hneg := hprod.neg
  unfold entropyBetaDerivative
  convert hneg using 1 <;> ring

/-- Derivative form of the entropy-response curvature identity. -/
theorem deriv_entropyBetaDerivative
    {β : ℝ} (hβ : 1 < β) :
    deriv entropyBetaDerivative β =
      -logEnergyVariance β + β * logEnergyThirdCumulant β := by
  exact (hasDerivAt_entropyBetaDerivative hβ).deriv

end GppZetaGibbsEntropyDerivative

#print axioms GppZetaGibbsEntropyDerivative.hasDerivAt_zetaEntropy
#print axioms GppZetaGibbsEntropyDerivative.deriv_zetaEntropy_neg
#print axioms GppZetaGibbsEntropyDerivative.deriv_zetaEntropy_eq_neg_heatCapacity_div_beta
#print axioms GppZetaGibbsEntropyDerivative.heatCapacity_eq_neg_beta_mul_deriv_zetaEntropy
#print axioms GppZetaGibbsEntropyDerivative.hasDerivAt_entropyBetaDerivative
#print axioms GppZetaGibbsEntropyDerivative.deriv_entropyBetaDerivative