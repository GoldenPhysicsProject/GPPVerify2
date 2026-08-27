import GppVerify.CelestialHolography.Mu4DimensionShiftAlgebra
import GppVerify.CelestialHolography.GammaResidueAtZero
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Raised-box residue assembly

For the dimension-shifted four-dimensional scalar box, the only remaining analytic input
needed for the finite `mu^4` rational term is the simplex moment

  simplexMoment(eps) -> 1/6.

A Feynman-parameter derivation factors the raised-dimensional integral as

  I8(eps) = Gamma(eps) * simplexMoment(eps).

`GammaResidueAtZero.lean` now proves the other formerly-open input

  eps * Gamma(eps) -> 1

on the punctured real neighborhood of zero.  This file keeps a generic assembly theorem
and then specializes it to the genuine real Gamma factor.  No Feynman-parameter
factorization or simplex dominated-convergence theorem is asserted here.
-/

namespace GppRaisedBoxResidueAssembly

open Filter Set
open GppMu4DimensionShift
open GppGammaResidueAtZero

/-- Product assembly for the scaled raised-box residue. -/
theorem tendsto_scaledRaisedBox_of_gamma_simplex
    {gammaFactor simplexMoment : ℝ → ℝ} {l : Filter ℝ}
    (hgamma : Tendsto (fun ε : ℝ => ε * gammaFactor ε) l (nhds 1))
    (hsimplex : Tendsto simplexMoment l (nhds (1 / 6 : ℝ))) :
    Tendsto
      (fun ε : ℝ => ε * (gammaFactor ε * simplexMoment ε))
      l (nhds (1 / 6 : ℝ)) := by
  have hmul := hgamma.mul hsimplex
  convert hmul using 1
  · funext ε
    ring
  · ring

/-- If the raised-dimensional box is pointwise represented by a Gamma factor times
its simplex moment, the same two analytic limits imply the exact scaled residue. -/
theorem tendsto_scaledRaisedBox_of_factorization
    {I gammaFactor simplexMoment : ℝ → ℝ} {l : Filter ℝ}
    (hI : ∀ ε, I ε = gammaFactor ε * simplexMoment ε)
    (hgamma : Tendsto (fun ε : ℝ => ε * gammaFactor ε) l (nhds 1))
    (hsimplex : Tendsto simplexMoment l (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => ε * I ε) l (nhds (1 / 6 : ℝ)) := by
  have h := tendsto_scaledRaisedBox_of_gamma_simplex hgamma hsimplex
  convert h using 1
  funext ε
  rw [hI ε]

/-- **Real-Gamma specialization.** Once the actual raised box is represented as
`Gamma(eps) * simplexMoment(eps)`, the Gamma-pole part is no longer a hypothesis:
only the simplex-volume limit remains. -/
theorem tendsto_scaledRaisedBox_realGamma_of_simplex
    {I simplexMoment : ℝ → ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε)
    (hsimplex : Tendsto simplexMoment
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => ε * I ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ)) := by
  exact tendsto_scaledRaisedBox_of_factorization hI
    tendsto_mul_realGamma_zero hsimplex

/-- **Complete algebraic route to the finite `mu^4` rational term.** Once the
Feynman-parameter factorization, Gamma residue, and simplex-volume limit are
available, the dimension-shifted product tends to `-1/6`. -/
theorem tendsto_mu4_rational_of_gamma_simplex
    {I gammaFactor simplexMoment : ℝ → ℝ} {l : Filter ℝ}
    (hε : Tendsto (fun ε : ℝ => ε) l (nhds 0))
    (hI : ∀ ε, I ε = gammaFactor ε * simplexMoment ε)
    (hgamma : Tendsto (fun ε : ℝ => ε * gammaFactor ε) l (nhds 1))
    (hsimplex : Tendsto simplexMoment l (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => shiftFactor ε * I ε) l (nhds (-(1 / 6 : ℝ))) := by
  apply tendsto_shiftFactor_mul_of_scaledResidue hε
  exact tendsto_scaledRaisedBox_of_factorization hI hgamma hsimplex

/-- **Real-Gamma `mu^4` closure.** On the punctured real regulator neighborhood,
the sole remaining analytic hypothesis is the simplex moment tending to `1/6`. -/
theorem tendsto_mu4_rational_realGamma_of_simplex
    {I simplexMoment : ℝ → ℝ}
    (hI : ∀ ε, I ε = Real.Gamma ε * simplexMoment ε)
    (hsimplex : Tendsto simplexMoment
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 6 : ℝ))) :
    Tendsto (fun ε : ℝ => shiftFactor ε * I ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-(1 / 6 : ℝ))) := by
  apply tendsto_shiftFactor_mul_of_scaledResidue
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  exact tendsto_scaledRaisedBox_realGamma_of_simplex hI hsimplex

end GppRaisedBoxResidueAssembly

#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_of_gamma_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_of_factorization
#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_realGamma_of_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_mu4_rational_of_gamma_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_mu4_rational_realGamma_of_simplex
