import GppVerify.CelestialHolography.RaisedBoxInnerAE
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSlice
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# First dominated-convergence step for the raised scalar box

This file assembles the already-certified inner-slice ingredients into the
actual interval dominated-convergence statement.  The regulator approaches
zero through `Icc 0 δ`, matching the physical nonnegative regulator and the
one-channel majorant hypotheses.

The sole remaining local input is AE strong measurability of the concrete
`Real.rpow` integrand on the restricted interval.  Keeping that hypothesis
explicit isolates the exact next measure-theory obligation rather than hiding
it behind an axiom or a surrogate estimate.
-/

namespace GppRaisedBoxInnerDCT

open Filter Set MeasureTheory
open scoped Interval Topology
open GppRaisedBoxConcreteMoment
open GppRaisedBoxInnerAE
open GppRaisedBoxRealMajorantSlice

/-- For a fixed strict base point of the simplex, dominated convergence carries
regulator removal through the innermost `x3` integral.  The filter is the
right-hand compact regulator neighborhood `nhdsWithin 0 (Icc 0 δ)`, exactly
where `0 ≤ ε ≤ δ` and the certified majorant applies. -/
theorem inner_interval_tendsto_one
    {δ S T x1 x2 : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : 0 < S) (hT : 0 < T)
    (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hx12 : x1 + x2 < 1)
    (hMeas :
      ∀ᶠ ε : ℝ in 𝓝[Set.Icc 0 δ] 0,
        AEStronglyMeasurable
          (fun x3 : ℝ => integrand ε S T x1 x2 x3)
          (volume.restrict (Set.uIoc 0 (1 - x1 - x2)))) :
    Tendsto
      (fun ε : ℝ =>
        ∫ x3 : ℝ in 0..(1 - x1 - x2), integrand ε S T x1 x2 x3)
      (𝓝[Set.Icc 0 δ] 0)
      (nhds (∫ _x3 : ℝ in 0..(1 - x1 - x2), (1 : ℝ))) := by
  have hL : 0 < 1 - x1 - x2 := by linarith
  have hMajInt : IntervalIntegrable
      (fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ))
      volume 0 (1 - x1 - x2) := by
    exact intervalIntegrable_const.add
      (channel_inner_intervalIntegrable hδ1 hS.le hx1.le)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun x3 : ℝ => 1 + (S * x1 * x3) ^ (-δ : ℝ))
  · exact hMeas
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Filter.Eventually.of_forall ?_
    intro x3
    intro hx3mem
    rw [Set.uIoc_of_le hL.le] at hx3mem
    have hx3 : 0 < x3 := hx3mem.1
    have hxsum : x1 + x2 + x3 ≤ 1 := by linarith
    have hx4 : 0 ≤ x4 x1 x2 x3 := by
      unfold x4
      linarith
    have hQ : 0 < Q S T x1 x2 x3 := by
      unfold Q
      positivity
    have hnonneg : 0 ≤ integrand ε S T x1 x2 x3 := by
      unfold integrand
      exact Real.rpow_nonneg hQ.le _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact integrand_le_one_channel_majorant
      hS hT hx1 hx2.le hx3 hxsum hε.1 hε.2 hδ0
  · exact hMajInt
  · have hAE := integrand_tendsto_one_ae_inner hS hT hx1 hx2 hx12
    filter_upwards [hAE] with x3 hx3lim
    intro hx3mem
    rw [Set.uIoc_of_le hL.le] at hx3mem
    have hfull := hx3lim hx3mem
    apply hfull.mono_left
    exact inf_le_left

end GppRaisedBoxInnerDCT

#print axioms GppRaisedBoxInnerDCT.inner_interval_tendsto_one
