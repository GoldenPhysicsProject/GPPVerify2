import GppVerify.CelestialHolography.RegulatedBoxDilogSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Derivative cancellation kernel for the real Spence identity

This file isolates the algebraic/calculus part of the real Spence argument from the
remaining hard analytic input: differentiating the project's `li2Series`.

Once the two local derivative identities for `li2Series` are supplied at `x` and
`1 - x`, the full Spence combination has derivative zero on `0 < x < 1`.
-/

namespace GppRegulatedBoxSpenceDerivativeKernel

open GppRegulatedBoxDilogSeries

/-- The real Spence combination built from the project's local dilogarithm series. -/
noncomputable def spenceCombination (x : ℝ) : ℝ :=
  li2Series x + li2Series (1 - x) + Real.log x * Real.log (1 - x)

/-- Exact derivative cancellation for the Spence combination, conditional only on
having established the local derivative formula for `li2Series` at `x` and `1-x`.
This theorem contains no dilogarithm functional equation assumption. -/
theorem spenceCombination_hasDerivAt_zero
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hLx : HasDerivAt li2Series (-Real.log (1 - x) / x) x)
    (hL1x : HasDerivAt li2Series (-Real.log x / (1 - x)) (1 - x)) :
    HasDerivAt spenceCombination 0 x := by
  have hxne : x ≠ 0 := ne_of_gt hx0
  have h1xne : 1 - x ≠ 0 := by linarith
  have hone_sub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x) using 1 <;> ring
  have hL1x_comp :
      HasDerivAt (fun y : ℝ => li2Series (1 - y))
        ((-Real.log x / (1 - x)) * (-1)) x := by
    exact hL1x.comp x hone_sub
  have hlogx : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hxne
  have hlog1x :
      HasDerivAt (fun y : ℝ => Real.log (1 - y))
        ((1 / (1 - x)) * (-1)) x := by
    simpa [one_div, Function.comp_def] using
      (Real.hasDerivAt_log h1xne).comp x hone_sub
  have hprod :
      HasDerivAt (fun y : ℝ => Real.log y * Real.log (1 - y))
        ((1 / x) * Real.log (1 - x) +
          Real.log x * ((1 / (1 - x)) * (-1))) x := by
    exact hlogx.mul hlog1x
  have hsum := hLx.add hL1x_comp |>.add hprod
  have hzero :
      -Real.log (1 - x) / x +
          -Real.log x / (1 - x) * (-1) +
          ((1 / x) * Real.log (1 - x) +
            Real.log x * ((1 / (1 - x)) * (-1))) = 0 := by
    field_simp [hxne, h1xne]
    ring
  rw [hzero] at hsum
  simpa [spenceCombination] using hsum

end GppRegulatedBoxSpenceDerivativeKernel

#print axioms GppRegulatedBoxSpenceDerivativeKernel.spenceCombination_hasDerivAt_zero
