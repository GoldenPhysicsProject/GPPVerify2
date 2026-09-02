import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.Tactic

/-!
# Raised-box strip integral bridge

The jointly measurable two-dimensional strip representation is useful for
product-measure/Fubini arguments, while the original raised-box moment is
written with the affine variable endpoint `0 ≤ x3 ≤ 1 - x1 - x2`.

This file lifts the certified pointwise section identity to equality of the
corresponding whole-line indicator integrals.  It is the direct bridge needed
before converting the product-integral measurability theorem into the middle
DCT formulation used by the nested simplex moment.
-/

namespace GppRaisedBoxStripIntegralBridge

open GppRaisedBoxConcreteMoment

/-- Integrating a fixed `x2` section of the measurable two-dimensional simplex
strip is exactly the same as integrating the corresponding closed-interval
indicator of the original affine innermost coordinate. -/
theorem stripInnerIntegral_eq_IccIndicatorIntegral
    (ε S T x1 x2 : ℝ) :
    (∫ x3 : ℝ,
      ((innerSimplexStrip x1).indicator
        (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3)) =
    ∫ x3 : ℝ,
      (Set.Icc (0 : ℝ) (1 - x1 - x2)).indicator
        (fun y : ℝ => integrand ε S T x1 x2 y) x3 := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x3
  exact stripIntegrand_section_eq_Icc_indicator ε S T x1 x2 x3

end GppRaisedBoxStripIntegralBridge

#print axioms GppRaisedBoxStripIntegralBridge.stripInnerIntegral_eq_IccIndicatorIntegral
