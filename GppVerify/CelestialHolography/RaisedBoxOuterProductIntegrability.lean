import GppVerify.CelestialHolography.RaisedBoxOuterSectionIntegrability
import GppVerify.CelestialHolography.RaisedBoxMiddleMeasurability
import GppVerify.CelestialHolography.RaisedBoxOuterFiberBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Raised-box outer product integrability

The final Fubini bridge requires integrability of the fixed-`x1` two-dimensional
simplex section.  The nontrivial second conjunct of `integrable_prod_iff` is the
integrability in `x2` of the integral of the `x3`-section norm.

On the physical interval the certified norm-integral identity identifies that
quantity with the ordinary variable-endpoint inner integral.  The middle-DCT
majorant already bounds this inner integral by an `x2`-independent constant for
fixed strict `x1`, so no new singular estimate is required here.
-/

namespace GppRaisedBoxOuterProductIntegrability

open Filter Set MeasureTheory
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxMiddleMeasurability
open GppRaisedBoxOuterSectionIntegrability
open GppRaisedBoxOuterFiberBridge

/-- For fixed strict outer coordinate, the physical variable-endpoint inner
integral is interval-integrable in the middle coordinate.  This is exactly the
scalar quantity that the section norm integral reduces to by nonnegativity. -/
theorem intervalInnerIntegral_intervalIntegrable
    {δ ε S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    IntervalIntegrable
      (fun x2 : ℝ =>
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3)
      volume 0 (1 - x1) := by
  have hL : 0 ≤ 1 - x1 := by linarith
  let C : ℝ := 1 + (S * x1) ^ (-δ : ℝ) / (1 - δ)
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _x2 : ℝ => C) volume 0 (1 - x1)).mono_fun'
  · exact intervalInnerIntegral_aestronglyMeasurable hx1lt.le
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x2 hx2
    rw [Set.uIoc_of_le hL] at hx2
    exact intervalInnerIntegral_norm_le_middleConstant
      hδ0 hδ1 hε0 hεδ hS hT hx1 hx2.1.le (by linarith)

/-- Zero-extending the physical middle integral outside its compact affine
interval gives a globally integrable function.  This is the target shape of the
second `integrable_prod_iff` conjunct after applying the certified section
norm-integral identity. -/
theorem IccIndicator_intervalInnerIntegral_integrable
    {δ ε S T x1 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx1lt : x1 < 1) :
    Integrable
      ((Set.Icc (0 : ℝ) (1 - x1)).indicator
        (fun x2 : ℝ =>
          ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
            integrand ε S T x1 x2 x3)) := by
  have hL : 0 ≤ 1 - x1 := by linarith
  have hInterval := intervalInnerIntegral_intervalIntegrable
    hδ0 hδ1 hε0 hεδ hS hT hx1 hx1lt
  have hOn : IntegrableOn
      (fun x2 : ℝ =>
        ∫ x3 in (0 : ℝ)..(1 - x1 - x2),
          integrand ε S T x1 x2 x3)
      (Set.Icc (0 : ℝ) (1 - x1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mp hInterval
  exact hOn.integrable_indicator measurableSet_Icc

end GppRaisedBoxOuterProductIntegrability

#print axioms GppRaisedBoxOuterProductIntegrability.intervalInnerIntegral_intervalIntegrable
#print axioms GppRaisedBoxOuterProductIntegrability.IccIndicator_intervalInnerIntegral_integrable
