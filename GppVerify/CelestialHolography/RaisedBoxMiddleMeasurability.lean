import GppVerify.CelestialHolography.RaisedBoxStripIntegralBridge
import GppVerify.CelestialHolography.RaisedBoxInnerDCT
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSliceIntegral
import Mathlib.Tactic

/-!
# Raised-box middle-coordinate measurability

The measurable product-strip representation gives strong measurability of the
innermost integral as a function of `x2`.  On the physical middle simplex range,
the strip integral is exactly the variable-endpoint interval integral.  This file
transfers the product-measure certificate to the interval-integral function used
by the second dominated-convergence step.

It also packages the norm of that inner integral under the same one-channel
majorant used in the certified inner DCT.  This is the direct domination
interface needed by the middle dominated-convergence theorem.
-/

namespace GppRaisedBoxMiddleMeasurability

open Filter Set MeasureTheory
open scoped Interval
open GppRaisedBoxConcreteMoment
open GppRaisedBoxStripIntegralBridge
open GppRaisedBoxRealMajorantSlice
open GppRaisedBoxRealMajorantSliceIntegral

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
  have hstrip :
      AEStronglyMeasurable
        (fun x2 : ℝ =>
          ∫ x3 : ℝ,
            ((innerSimplexStrip x1).indicator
              (fun p : ℝ × ℝ => integrand ε S T x1 p.1 p.2)) (x2, x3))
        (volume.restrict (Set.uIoc (0 : ℝ) (1 - x1))) :=
    (stripInnerIntegral_stronglyMeasurable ε S T x1).aestronglyMeasurable.restrict
  apply hstrip.congr
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x2 hx2
  rw [Set.uIoc_of_le (by linarith : (0 : ℝ) ≤ 1 - x1)] at hx2
  exact stripInnerIntegral_eq_intervalIntegral ε S T x1 x2 ⟨hx2.1.le, hx2.2⟩

/-- The norm of the variable-endpoint inner integral is bounded by the integral
of the certified one-channel majorant.  Unlike the pointwise inner DCT, this
statement keeps `x2` free and is therefore the exact domination interface for
the next (middle-coordinate) dominated-convergence step. -/
theorem intervalInnerIntegral_norm_le_integratedMajorant
    {δ ε S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx12 : x1 + x2 ≤ 1) :
    ‖∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3‖ ≤
      ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
        (1 + (S * x1 * x3) ^ (-δ : ℝ)) := by
  have hL : 0 ≤ 1 - x1 - x2 := by linarith
  have hMajInt : IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ))
      volume 0 (1 - x1 - x2) := by
    exact intervalIntegrable_const.add
      (channel_inner_intervalIntegrable hδ1 hS.le hx1.le hL)
  apply intervalIntegral.norm_integral_le_of_norm_le hL
  · filter_upwards with x3
    intro hx3mem
    have hx3 : 0 < x3 := hx3mem.1
    have hxsum : x1 + x2 + x3 ≤ 1 := by linarith
    have hQ : 0 < Q S T x1 x2 x3 := by
      unfold Q
      positivity
    have hnonneg : 0 ≤ integrand ε S T x1 x2 x3 := by
      unfold integrand
      exact Real.rpow_nonneg hQ.le _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact integrand_le_one_channel_majorant
      hS hT hx1 hx2 hx3 hxsum hε0 hεδ hδ0
  · exact hMajInt

/-- Explicit form of the previous norm bound after evaluating the singular
endpoint integral.  This is the middle-DCT majorant before integrating in `x2`.
-/
theorem intervalInnerIntegral_norm_le_explicitMajorant
    {δ ε S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hεδ : ε ≤ δ)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 ≤ x2) (hx12 : x1 + x2 ≤ 1) :
    ‖∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3‖ ≤
      (1 - x1 - x2) +
        (S * x1) ^ (-δ : ℝ) *
          ((1 - x1 - x2) ^ (1 - δ : ℝ) / (1 - δ)) := by
  have hL : 0 ≤ 1 - x1 - x2 := by linarith
  calc
    ‖∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
        integrand ε S T x1 x2 x3‖ ≤
        ∫ x3 : ℝ in (0 : ℝ)..(1 - x1 - x2),
          (1 + (S * x1 * x3) ^ (-δ : ℝ)) :=
      intervalInnerIntegral_norm_le_integratedMajorant
        hδ0 hδ1 hε0 hεδ hS hT hx1 hx2 hx12
    _ = (1 - x1 - x2) +
        (S * x1) ^ (-δ : ℝ) *
          ((1 - x1 - x2) ^ (1 - δ : ℝ) / (1 - δ)) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        (channel_inner_intervalIntegrable hδ1 hS.le hx1.le hL)]
      rw [integral_channel_zero_to hδ1 hS.le hx1.le hL]
      simp

end GppRaisedBoxMiddleMeasurability

#print axioms GppRaisedBoxMiddleMeasurability.intervalInnerIntegral_aestronglyMeasurable
#print axioms GppRaisedBoxMiddleMeasurability.intervalInnerIntegral_norm_le_integratedMajorant
#print axioms GppRaisedBoxMiddleMeasurability.intervalInnerIntegral_norm_le_explicitMajorant
