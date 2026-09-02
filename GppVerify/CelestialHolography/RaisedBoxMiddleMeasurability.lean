import GppVerify.CelestialHolography.RaisedBoxStripIntegralBridge
import Mathlib.Tactic

/-!
# Raised-box middle-coordinate measurability

The measurable product-strip representation gives strong measurability of the
innermost integral as a function of `x2`.  On the physical middle simplex range,
the strip integral is exactly the variable-endpoint interval integral.  This file
transfers the product-measure certificate to the interval-integral function used
by the second dominated-convergence step.
-/

namespace GppRaisedBoxMiddleMeasurability

open Filter Set MeasureTheory
open scoped Interval
open GppRaisedBoxConcreteMoment
open GppRaisedBoxStripIntegralBridge

/-- On the physical middle simplex interval, the variable-endpoint innermost
raised-box integral is a.e. strongly measurable in `x2`.  This is the exact
measurability hypothesis needed by the middle dominated-convergence theorem. -/
theorem intervalInnerIntegral_aestronglyMeasurable
    {ε S T x1 : ℝ} (hx1 : x1 ≤ 1) :
    AEStronglyMeasurable
      (fun x2 : ℝ =>
        ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3)
      (volume.restrict (Set.uIoc (0 : ℝ) (1 - x1))) := by
  have hstrip :=
    (stripInnerIntegral_stronglyMeasurable ε S T x1).aestronglyMeasurable.restrict
  apply hstrip.congr
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x2 hx2
  rw [Set.uIoc_of_le (by linarith : (0 : ℝ) ≤ 1 - x1)] at hx2
  exact stripInnerIntegral_eq_intervalIntegral ε S T x1 x2 ⟨hx2.1.le, hx2.2⟩

end GppRaisedBoxMiddleMeasurability

#print axioms GppRaisedBoxMiddleMeasurability.intervalInnerIntegral_aestronglyMeasurable
