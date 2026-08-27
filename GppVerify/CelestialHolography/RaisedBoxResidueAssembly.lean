import GppVerify.CelestialHolography.Mu4DimensionShiftAlgebra
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Raised-box residue assembly

For the dimension-shifted four-dimensional scalar box, the only analytic input
needed for the finite `mu^4` rational term is the scaled residue

  eps * I8(eps) -> 1/6.

A Feynman-parameter derivation naturally factors the raised-dimensional integral as

  I8(eps) = Gamma(eps) * simplexMoment(eps),

with the two elementary limits

  eps * Gamma(eps) -> 1,
  simplexMoment(eps) -> 1/6.

This file formalizes that assembly and then feeds the resulting scaled residue into
the already-proved `mu^4` dimension-shift limit.  The two analytic limits themselves
remain separate targets; no Feynman-integral residue is assumed globally.
-/

namespace GppRaisedBoxResidueAssembly

open Filter
open GppMu4DimensionShift

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

end GppRaisedBoxResidueAssembly

#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_of_gamma_simplex
#print axioms GppRaisedBoxResidueAssembly.tendsto_scaledRaisedBox_of_factorization
#print axioms GppRaisedBoxResidueAssembly.tendsto_mu4_rational_of_gamma_simplex
