import GppVerify.RiemannHypothesis.ZetaGibbsEntropyDerivative
import Mathlib.Tactic

/-!
# Differential Legendre law for the zeta Gibbs free energy

On the honest Gibbs half-line `β > 1`, let

  A(β) = log Z(β),
  U(β) = -A'(β),
  S(β) = A(β) + β U(β),
  F(β) = -A(β) / β.

The already formalized derivative `A' = -U` then gives the exact differential
Legendre identity

  F'(β) = S(β) / β^2.

No analytic continuation of the thermodynamic interpretation is asserted.
-/

namespace GppZetaGibbsLegendreDifferential

open GppZetaGibbsThermodynamicDerivatives
open GppZetaGibbsEntropyDerivative

/-- Helmholtz free energy built from the real zeta log-partition potential. -/
noncomputable def zetaFreeEnergy (β : ℝ) : ℝ :=
  -zetaLogPartition β / β

/-- Exact differential Legendre relation `F' = S / β²` on the Gibbs half-line. -/
theorem hasDerivAt_zetaFreeEnergy
    {β : ℝ} (hβ : 1 < β) :
    HasDerivAt zetaFreeEnergy (zetaEntropy β / β ^ 2) β := by
  have hA := (hasDerivAt_zetaLogPartition hβ).neg
  have hβid : HasDerivAt (fun x : ℝ => x) 1 β := hasDerivAt_id β
  have hβ0 : β ≠ 0 := by linarith
  have hF := hA.div hβid hβ0
  convert hF using 1
  · unfold zetaFreeEnergy
    rfl
  · unfold zetaEntropy
    field_simp [hβ0]
    ring

/-- The ordinary derivative version of the same Legendre differential identity. -/
theorem deriv_zetaFreeEnergy
    {β : ℝ} (hβ : 1 < β) :
    deriv zetaFreeEnergy β = zetaEntropy β / β ^ 2 :=
  (hasDerivAt_zetaFreeEnergy hβ).deriv

end GppZetaGibbsLegendreDifferential

#print axioms GppZetaGibbsLegendreDifferential.hasDerivAt_zetaFreeEnergy
#print axioms GppZetaGibbsLegendreDifferential.deriv_zetaFreeEnergy
