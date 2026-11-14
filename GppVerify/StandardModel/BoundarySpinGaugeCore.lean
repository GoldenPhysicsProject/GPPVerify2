import Mathlib.Tactic
import GppVerify.StandardModel.PatiSalamHypercharge

/-!
# Boundary Spin gauge core

Golden Physics Project, November 2026. Theorems in this file concern exact
finite-dimensional algebra. Geometric bundle connections and gauge dynamics
are specified separately and must not be inferred from these finite checks.

The Pluecker conjugate-dual map gives a real structure on Lambda^2 C^4.
Two off-block Grassmannian tangent matrices have nonzero vertical Lie bracket.
A quark-doublet normalization and a neutral right-triplet order parameter
uniquely determine the linear Pati-Salam hypercharge functional.
-/

namespace GppBoundarySpinGauge

open Complex

/-- The SU(4) Pluecker conjugate-dual operation on the ordered bivector
coordinates (12,13,14,23,24,34). Unlike the linear Hodge star, this
operation explicitly conjugates complex coefficients. -/
def pluckerConjugateDual (v : Fin 6 → ℂ) : Fin 6 → ℂ
  | 0 => star (v 5)
  | 1 => -(star (v 4))
  | 2 => star (v 3)
  | 3 => star (v 2)
  | 4 => -(star (v 1))
  | 5 => star (v 0)

/-- The conjugate Pluecker duality squares to the identity. -/
theorem plucker_conjugate_dual_involution (v : Fin 6 → ℂ) :
    pluckerConjugateDual (pluckerConjugateDual v) = v := by
  funext i
  fin_cases i <;> simp [pluckerConjugateDual]

/-- The Pluecker duality respects sums. -/
theorem plucker_conjugate_dual_add (v w : Fin 6 → ℂ) :
    pluckerConjugateDual (v + w) =
      pluckerConjugateDual v + pluckerConjugateDual w := by
  funext i
  fin_cases i <;> simp [pluckerConjugateDual, Pi.add_apply, star_add]

/-- The Pluecker duality conjugates scalars. -/
theorem plucker_conjugate_dual_smul (z : ℂ) (v : Fin 6 → ℂ) :
    pluckerConjugateDual (z • v) =
      (star z) • pluckerConjugateDual v := by
  funext i
  fin_cases i <;> simp [pluckerConjugateDual, Pi.smul_apply, star_mul, mul_comm]

/-- Base rank-two projector in the four-dimensional twistor carrier. -/
def baseProjector : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1,0,0,0;
     0,1,0,0;
     0,0,0,0;
     0,0,0,0]

/-- A Grassmannian tangent rotation between the first and third axes. -/
def tangentX : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 0,0,1,0;
      0,0,0,0;
     -1,0,0,0;
      0,0,0,0]

/-- A second independent Grassmannian tangent rotation. -/
def tangentY : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0,0,0;
     0, 0,1,0;
     0,-1,0,0;
     0, 0,0,0]

/-- The bracket of the two horizontal directions, in the first U(2) block. -/
def verticalCurvature : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0,-1,0,0;
     1, 0,0,0;
     0, 0,0,0;
     0, 0,0,0]

/-- The Grassmannian base projector is idempotent. -/
theorem base_projector_sq :
    baseProjector * baseProjector = baseProjector := by
  decide

/-- Horizontal bracket has an explicitly nonzero vertical component.
This is a local witness for curvature of the canonical reductive connection.
The global smooth curvature identity remains to be formalized. -/
theorem horizontal_bracket_vertical :
    tangentX * tangentY - tangentY * tangentX = verticalCurvature := by
  decide

/-- The curvature witness is not the zero matrix. -/
theorem vertical_curvature_nonzero : verticalCurvature ≠ 0 := by
  decide

/-- Vertical curvature commutes with the splitting projector. -/
theorem vertical_curvature_preserves_projector :
    baseProjector * verticalCurvature = verticalCurvature * baseProjector := by
  decide

/-- Horizontal tangent does not commute with the splitting projector. -/
theorem horizontal_tangent_changes_projector :
    baseProjector * tangentX ≠ tangentX * baseProjector := by
  decide

/-- Linear U(1) generator on X=3(B-L), r=2T3R. -/
def linearHypercharge (a b : ℚ) (X r : ℤ) : ℚ :=
  a * (X : ℚ) + b * (r : ℚ)

/-- The left-quark charge and a hypercharge-neutral (X,r)=(6,-2)
right-triplet order parameter uniquely determine Y=X/6+r/2.
These physical normalization conditions are hypotheses. -/
theorem hypercharge_coefficients_unique (a b : ℚ)
    (hquark : linearHypercharge a b 1 0 = 1 / 6)
    (hneut : linearHypercharge a b 6 (-2) = 0) :
    a = 1 / 6 ∧ b = 1 / 2 := by
  norm_num [linearHypercharge] at hquark hneut
  constructor <;> linarith

/-- The selected generator agrees with the existing Pati-Salam table. -/
theorem selected_hypercharge_agrees (X r : ℤ) :
    linearHypercharge (1 / 6) (1 / 2) X r =
      GppPatiSalamHypercharge.hypercharge X r := by
  simp only [linearHypercharge, GppPatiSalamHypercharge.hypercharge]
  ring

/-- The selected right-triplet component has zero surviving hypercharge. -/
theorem selected_order_parameter_neutral :
    linearHypercharge (1 / 6) (1 / 2) 6 (-2) = 0 := by
  norm_num [linearHypercharge]

/-- Spin(10) chiral family dimension in its Pati-Salam branching. -/
theorem chiral_family_slot_count : (4 : ℕ) * 2 + 4 * 2 = 16 := by
  norm_num

/-- Six left-handed multiplet hypercharges, including charge-conjugated
right-handed particles: Q, L, u^c, d^c, e^c and nu^c. -/
theorem left_handed_hypercharges :
    linearHypercharge (1 / 6) (1 / 2) 1 0 = 1 / 6 ∧
    linearHypercharge (1 / 6) (1 / 2) (-3) 0 = -(1 / 2 : ℚ) ∧
    linearHypercharge (1 / 6) (1 / 2) (-1) (-1) = -(2 / 3 : ℚ) ∧
    linearHypercharge (1 / 6) (1 / 2) (-1) 1 = (1 / 3 : ℚ) ∧
    linearHypercharge (1 / 6) (1 / 2) 3 1 = (1 : ℚ) ∧
    linearHypercharge (1 / 6) (1 / 2) 3 (-1) = 0 := by
  norm_num [linearHypercharge]

/-- The local cubic U(1)_Y anomaly of a full left-handed family vanishes. -/
theorem full_family_cubic_hypercharge_anomaly :
    6 * ((1 : ℚ) / 6)^3 +
    3 * (-(2 : ℚ) / 3)^3 +
    3 * ((1 : ℚ) / 3)^3 +
    2 * (-(1 : ℚ) / 2)^3 +
    1^3 + 0^3 = 0 := by
  norm_num

/-- The two mixed nonabelian/U(1) anomalies vanish in one generation. -/
theorem family_mixed_anomalies :
    3 * ((1 : ℚ) / 6) - 1 / 2 = 0 ∧
    2 * ((1 : ℚ) / 6) - 2 / 3 + 1 / 3 = 0 := by
  norm_num

end GppBoundarySpinGauge

#print axioms GppBoundarySpinGauge.plucker_conjugate_dual_involution
#print axioms GppBoundarySpinGauge.horizontal_bracket_vertical
#print axioms GppBoundarySpinGauge.hypercharge_coefficients_unique
#print axioms GppBoundarySpinGauge.full_family_cubic_hypercharge_anomaly
