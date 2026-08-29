import Mathlib.Tactic

/-!
# Rational chart to physical massive-cut coordinates

The generic massive-vector discovery calculation uses rational parameters `r,t`.
This file isolates their exact conversion to the physical velocity/mass variables
and scattering angle:

  beta = (1-r^2)/(1+r^2),
  rho  = 2r/(1+r^2),
  cosTheta = (1-t^2)/(1+t^2).

The identities below are pure kinematics.  They explain the repeated denominator
`1-beta*cosTheta` in the generic nonzero-mu Yang--Mills cut.
-/

namespace GppMassiveCutPhysicalCoordinates

/-- Velocity coordinate `|p|/E` in the rational massive-cut chart. -/
def betaCoord (r : ℝ) : ℝ := (1 - r ^ 2) / (1 + r ^ 2)

/-- Mass coordinate `mu/E` in the rational massive-cut chart. -/
def rhoCoord (r : ℝ) : ℝ := 2 * r / (1 + r ^ 2)

/-- Rational angular parametrization of `cos theta`. -/
def cosThetaCoord (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

/-- The velocity and mass coordinates lie exactly on the unit mass shell. -/
theorem beta_sq_add_rho_sq (r : ℝ) :
    betaCoord r ^ 2 + rhoCoord r ^ 2 = 1 := by
  unfold betaCoord rhoCoord
  have h : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  field_simp [h]
  ring

/-- Exact conversion of the rational cut denominator to physical variables. -/
theorem one_sub_beta_mul_cosTheta (r t : ℝ) :
    1 - betaCoord r * cosThetaCoord t =
      2 * (r ^ 2 + t ^ 2) / ((1 + r ^ 2) * (1 + t ^ 2)) := by
  unfold betaCoord cosThetaCoord
  have hr : 1 + r ^ 2 ≠ 0 := by nlinarith [sq_nonneg r]
  have ht : 1 + t ^ 2 ≠ 0 := by nlinarith [sq_nonneg t]
  field_simp [hr, ht]
  ring

/-- Threshold `r=1` is the massive rest slice: zero velocity and unit mass ratio. -/
@[simp] theorem betaCoord_one : betaCoord 1 = 0 := by
  norm_num [betaCoord]

@[simp] theorem rhoCoord_one : rhoCoord 1 = 1 := by
  norm_num [rhoCoord]

end GppMassiveCutPhysicalCoordinates

#print axioms GppMassiveCutPhysicalCoordinates.beta_sq_add_rho_sq
#print axioms GppMassiveCutPhysicalCoordinates.one_sub_beta_mul_cosTheta
