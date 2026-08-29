import GppVerify.RiemannHypothesis.ZetaGibbsLegendreDifferential
import GppVerify.RiemannHypothesis.ZetaGibbsStrictThermodynamics
import Mathlib.Tactic

/-!
# Free-energy curvature for the honest zeta Gibbs gas

On `β > 1`, the already formalized Legendre law is

  F'(β) = S(β) / β^2,

while the entropy law is

  S'(β) = -β κ₂(β).

Differentiating once more gives the exact curvature identity

  F''(β) = -κ₂(β)/β - 2 S(β)/β^3.

This is an exact fluctuation-geometric identity.  We deliberately assert no global
sign for `F''`: the variance term is negative, while a sign for the entropy potential
must be established separately rather than assumed from thermodynamic terminology.
-/

namespace GppZetaGibbsFreeEnergyCurvature

open GppZetaGibbsFisher
open GppZetaGibbsStrictThermodynamics
open GppZetaGibbsEntropyDerivative
open GppZetaGibbsLegendreDifferential

/-- The derivative appearing in the Legendre law. -/
noncomputable def freeEnergyBetaDerivative (β : ℝ) : ℝ :=
  zetaEntropy β / β ^ 2

/-- Exact second differential law for the zeta Gibbs Helmholtz free energy. -/
theorem hasDerivAt_freeEnergyBetaDerivative
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt freeEnergyBetaDerivative
      (-logEnergyVariance β / β - 2 * zetaEntropy β / β ^ 3) β := by
  have hβ0 : β ≠ 0 := by linarith
  have hS := hasDerivAt_zetaEntropy hβ
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * β) β := by
    simpa [id] using (hasDerivAt_id β).pow 2
  have hquot := hS.div hsq (pow_ne_zero 2 hβ0)
  have hcoef :
      (entropyBetaDerivative β * β ^ 2 - zetaEntropy β * (2 * β)) /
          (β ^ 2) ^ 2 =
        -logEnergyVariance β / β - 2 * zetaEntropy β / β ^ 3 := by
    unfold entropyBetaDerivative
    field_simp [hβ0]
    ring
  rw [← hcoef]
  simpa only [freeEnergyBetaDerivative] using hquot

/-- Ordinary derivative form of the free-energy curvature law. -/
theorem deriv_freeEnergyBetaDerivative
    {β : ℝ} (hβ : 1 < β) :
    deriv freeEnergyBetaDerivative β =
      -logEnergyVariance β / β - 2 * zetaEntropy β / β ^ 3 :=
  (hasDerivAt_freeEnergyBetaDerivative hβ).deriv

/-- Clearing the positive-temperature denominator exposes the exact fluctuation
balance behind the curvature: `β³ F'' = -β² κ₂ - 2S`.  This form is useful because
it separates the strictly positive Fisher contribution from the entropy term without
introducing any additional analytic assumptions. -/
theorem beta_cube_mul_deriv_freeEnergyBetaDerivative
    {β : ℝ} (hβ : 1 < β) :
    β ^ 3 * deriv freeEnergyBetaDerivative β =
      -(β ^ 2 * logEnergyVariance β) - 2 * zetaEntropy β := by
  have hβ0 : β ≠ 0 := by linarith
  rw [deriv_freeEnergyBetaDerivative hβ]
  field_simp [hβ0]
  ring

/-- If the Gibbs entropy potential is nonnegative at `β`, then the free-energy
curvature is strictly negative there.  Strictness comes from the already-proved
positive Fisher variance; entropy contributes only an additional nonpositive term.
The entropy sign is kept explicit rather than assumed from terminology. -/
theorem deriv_freeEnergyBetaDerivative_neg_of_entropy_nonneg
    {β : ℝ} (hβ : 1 < β) (hS : 0 ≤ zetaEntropy β) :
    deriv freeEnergyBetaDerivative β < 0 := by
  rw [deriv_freeEnergyBetaDerivative hβ]
  have hβpos : 0 < β := by linarith
  have hV : 0 < logEnergyVariance β := logEnergyVariance_pos hβ
  have hfirst : -logEnergyVariance β / β < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hV) hβpos
  have hβ3 : 0 < β ^ 3 := pow_pos hβpos 3
  have hsecond : 0 ≤ 2 * zetaEntropy β / β ^ 3 :=
    div_nonneg (mul_nonneg (by norm_num) hS) hβ3.le
  linarith

/-- The first derivative of the actual free energy is exactly the response whose
curvature was computed above. -/
theorem deriv_zetaFreeEnergy_eq_freeEnergyBetaDerivative
    {β : ℝ} (hβ : 1 < β) :
    deriv zetaFreeEnergy β = freeEnergyBetaDerivative β := by
  rw [deriv_zetaFreeEnergy hβ]
  rfl

end GppZetaGibbsFreeEnergyCurvature

#print axioms GppZetaGibbsFreeEnergyCurvature.hasDerivAt_freeEnergyBetaDerivative
#print axioms GppZetaGibbsFreeEnergyCurvature.deriv_freeEnergyBetaDerivative
#print axioms GppZetaGibbsFreeEnergyCurvature.beta_cube_mul_deriv_freeEnergyBetaDerivative
#print axioms GppZetaGibbsFreeEnergyCurvature.deriv_freeEnergyBetaDerivative_neg_of_entropy_nonneg
#print axioms GppZetaGibbsFreeEnergyCurvature.deriv_zetaFreeEnergy_eq_freeEnergyBetaDerivative
