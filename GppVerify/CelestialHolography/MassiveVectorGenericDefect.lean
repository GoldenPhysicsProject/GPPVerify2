import GppVerify.CelestialHolography.MassiveCutPhysicalCoordinates
import Mathlib.Tactic

/-!
# Generic massive-vector state-sum defect algebra

The exact symbolic five-dimensional Yang--Mills audit found that the threshold
identity `C_V = 3 C_S` is not a generic cut identity.  In the rational kinematic
parameters `r,t`, its same-helicity defect is

  4 (r^2 - 1)^2 (1+t^2)^2 / (r^2+t^2)^2.

A subsequent exact generic sewing audit evaluated the real-adjoint-scalar
contribution and the `D_s=4` massive-vector-minus-scalar baseline.  The latter
collapses to the unexpectedly simple numerator `r^8+1`:

  C4_same = 4 (r^8+1) (1+t^2)^2 /
    ((1+r^2)^2 (r^2+t^2)^2).

In physical coordinates `beta=|p|/E`, `rho=mu/E`, `c=cos(theta)`, these become

  Cs = rho^4/(1-beta*c)^2,
  Cv-3Cs = 16 beta^2/(1-beta*c)^2,
  C4 = (2 rho^4 + 16 beta^2)/(1-beta*c)^2.

This file certifies the rational algebra and the chart-to-physical conversion.
The identification with explicit sewn Yang--Mills trees remains an executable
symbolic discovery result rather than being hidden inside a Lean assumption.
-/

namespace GppMassiveVectorGenericDefect

open GppMassiveCutPhysicalCoordinates

/-- Exact rational defect found by the generic symbolic state-sum audit. -/
def sameHelicityDefect (r t : ℝ) : ℝ :=
  4 * (r ^ 2 - 1) ^ 2 * (1 + t ^ 2) ^ 2 / (r ^ 2 + t ^ 2) ^ 2

/-- Exact same-helicity one-real-adjoint-scalar sewing from the generic audit. -/
def sameHelicityScalarSewing (r t : ℝ) : ℝ :=
  4 * r ^ 4 * (1 + t ^ 2) ^ 2 /
    ((r ^ 2 + 1) ^ 2 * (r ^ 2 + t ^ 2) ^ 2)

/-- Exact `D_s=4` same-helicity baseline obtained as massive-vector minus scalar. -/
def sameHelicityDs4Baseline (r t : ℝ) : ℝ :=
  4 * (r ^ 8 + 1) * (1 + t ^ 2) ^ 2 /
    ((r ^ 2 + 1) ^ 2 * (r ^ 2 + t ^ 2) ^ 2)

/-- The generic correction is manifestly nonnegative. -/
theorem sameHelicityDefect_nonneg (r t : ℝ) :
    0 ≤ sameHelicityDefect r t := by
  unfold sameHelicityDefect
  positivity

/-- The real-adjoint-scalar sewing is nonnegative everywhere in the rational chart. -/
theorem sameHelicityScalarSewing_nonneg (r t : ℝ) :
    0 ≤ sameHelicityScalarSewing r t := by
  unfold sameHelicityScalarSewing
  positivity

/-- The reconstructed `D_s=4` same-helicity baseline is nonnegative everywhere
in the rational chart. -/
theorem sameHelicityDs4Baseline_nonneg (r t : ℝ) :
    0 ≤ sameHelicityDs4Baseline r t := by
  unfold sameHelicityDs4Baseline
  positivity

/-- The old `3:1` relation is recovered exactly on the threshold slice `r=1`. -/
@[simp] theorem sameHelicityDefect_one (t : ℝ) :
    sameHelicityDefect 1 t = 0 := by
  simp [sameHelicityDefect]

/-- The opposite threshold orientation `r=-1` has the same vanishing defect. -/
@[simp] theorem sameHelicityDefect_neg_one (t : ℝ) :
    sameHelicityDefect (-1) t = 0 := by
  simp [sameHelicityDefect]

/-- **Generic `D_s=4` closure.** Away from the degenerate `r=0` parametrization,
the exact massive-vector-minus-scalar baseline is two scalar sewings plus the
previously certified vector-minus-three-scalar defect. -/
theorem ds4Baseline_eq_two_scalar_add_defect
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDs4Baseline r t =
      2 * sameHelicityScalarSewing r t + sameHelicityDefect r t := by
  unfold sameHelicityDs4Baseline sameHelicityScalarSewing sameHelicityDefect
  have h1 : r ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg r]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have h2 : r ^ 2 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  field_simp [h1, h2]
  ring

/-- The positive defect is a rigorous lower bound for the reconstructed
same-helicity `D_s=4` baseline away from the degenerate `r=0` chart point. -/
theorem sameHelicityDefect_le_ds4Baseline
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDefect r t ≤ sameHelicityDs4Baseline r t := by
  rw [ds4Baseline_eq_two_scalar_add_defect hr]
  have hs := sameHelicityScalarSewing_nonneg r t
  linarith

/-- Exact chart-to-physical conversion of the scalar `mu^4` sewing. -/
theorem sameHelicityScalarSewing_physical
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityScalarSewing r t =
      rhoCoord r ^ 4 / (1 - betaCoord r * cosThetaCoord t) ^ 2 := by
  unfold sameHelicityScalarSewing rhoCoord betaCoord cosThetaCoord
  have hR : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  have hT : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hRT : r ^ 2 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp [hR, hT, hRT]
  ring

/-- Exact physical form of the generic polarization defect. -/
theorem sameHelicityDefect_physical
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDefect r t =
      16 * betaCoord r ^ 2 /
        (1 - betaCoord r * cosThetaCoord t) ^ 2 := by
  unfold sameHelicityDefect betaCoord cosThetaCoord
  have hR : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  have hT : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hRT : r ^ 2 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp [hR, hT, hRT]
  ring

/-- **Physical generic `D_s=4` numerator.** The baseline separates exactly into
a `mu^4` scalar term and a velocity/polarization term. -/
theorem sameHelicityDs4Baseline_physical
    {r t : ℝ} (hr : r ≠ 0) :
    sameHelicityDs4Baseline r t =
      (2 * rhoCoord r ^ 4 + 16 * betaCoord r ^ 2) /
        (1 - betaCoord r * cosThetaCoord t) ^ 2 := by
  rw [ds4Baseline_eq_two_scalar_add_defect hr,
    sameHelicityScalarSewing_physical hr,
    sameHelicityDefect_physical hr]
  ring

/-- The exact generic baseline recovers the threshold state count `2`. -/
@[simp] theorem sameHelicityDs4Baseline_one :
    sameHelicityDs4Baseline 1 1 = 2 := by
  norm_num [sameHelicityDs4Baseline]

/-- If an explicit Yang--Mills sewing calculation identifies its vector/scalar
state-sum difference with the audited rational defect, then the vector sewing is
at least three scalar sewings.  The amplitude identification remains an explicit
input rather than being smuggled into the algebraic theorem. -/
theorem vector_ge_three_scalar_of_defect
    {Cv Cs r t : ℝ}
    (hdef : Cv - 3 * Cs = sameHelicityDefect r t) :
    3 * Cs ≤ Cv := by
  have h := sameHelicityDefect_nonneg r t
  linarith

/-- On the threshold slice, the same explicit identification reduces exactly to
`C_V = 3 C_S`. -/
theorem vector_eq_three_scalar_at_threshold
    {Cv Cs t : ℝ}
    (hdef : Cv - 3 * Cs = sameHelicityDefect 1 t) :
    Cv = 3 * Cs := by
  simpa using hdef

end GppMassiveVectorGenericDefect

#print axioms GppMassiveVectorGenericDefect.sameHelicityDefect_nonneg
#print axioms GppMassiveVectorGenericDefect.sameHelicityScalarSewing_nonneg
#print axioms GppMassiveVectorGenericDefect.sameHelicityDs4Baseline_nonneg
#print axioms GppMassiveVectorGenericDefect.ds4Baseline_eq_two_scalar_add_defect
#print axioms GppMassiveVectorGenericDefect.sameHelicityDefect_le_ds4Baseline
#print axioms GppMassiveVectorGenericDefect.sameHelicityScalarSewing_physical
#print axioms GppMassiveVectorGenericDefect.sameHelicityDefect_physical
#print axioms GppMassiveVectorGenericDefect.sameHelicityDs4Baseline_physical
#print axioms GppMassiveVectorGenericDefect.vector_ge_three_scalar_of_defect
#print axioms GppMassiveVectorGenericDefect.vector_eq_three_scalar_at_threshold
