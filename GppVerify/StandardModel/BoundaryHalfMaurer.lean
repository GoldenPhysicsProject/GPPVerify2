import Mathlib.Tactic

/-!
# Curvature witness for the half-Maurer connection on the U(2) boundary

The Shilov boundary of the 2x2 matrix ball is U(2). Its graph map into
Gr(2,4) has an orthonormal tautological frame V(U)=(I,U)/sqrt(2).
The induced connection is A=V†dV=(1/2)U†dU. With
theta=U^-1 dU and dtheta=-theta∧theta, its curvature is
F=dA+A∧A=-(1/4) theta∧theta.

This file kernel-stages the local matrix curvature witness. Differential
forms, the graph bundle, and the Yang-Mills field equations are NOT yet
formalized here; those are separate proof obligations.
-/

namespace GppBoundaryHalfMaurer

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Two noncommuting traceless anti-Hermitian directions in su(2). -/
def generatorX : Mat2 :=
  !![Complex.I, 0;
     0, -Complex.I]

def generatorY : Mat2 :=
  !![0, 1;
     -1, 0]

def matrixCommutator (X Y : Mat2) : Mat2 :=
  X * Y - Y * X

/-- The curvature coefficient of A=cθ from dθ=-θ∧θ. -/
def curvatureCoefficient (c : ℚ) : ℚ := c^2 - c

theorem half_connection_coefficient :
    curvatureCoefficient (1 / 2) = -(1 / 4 : ℚ) := by
  norm_num [curvatureCoefficient]

/-- The two chosen tangent Lie algebra generators do not commute. -/
theorem generators_do_not_commute :
    matrixCommutator generatorX generatorY ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  norm_num [matrixCommutator, generatorX, generatorY,
    Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Local curvature of the canonical Grassmannian graph connection. -/
def halfMaurerCurvatureAtIdentity : Mat2 :=
  (-(1 / 4 : ℂ)) • matrixCommutator generatorX generatorY

theorem half_maurer_curvature_explicit :
    halfMaurerCurvatureAtIdentity =
      !![0, -(Complex.I / 2);
         -(Complex.I / 2), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfMaurerCurvatureAtIdentity, matrixCommutator,
      generatorX, generatorY, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply]

theorem half_maurer_curvature_nonzero :
    halfMaurerCurvatureAtIdentity ≠ 0 := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  rw [half_maurer_curvature_explicit] at h01
  norm_num at h01

end GppBoundaryHalfMaurer

#print axioms GppBoundaryHalfMaurer.half_connection_coefficient
#print axioms GppBoundaryHalfMaurer.generators_do_not_commute
#print axioms GppBoundaryHalfMaurer.half_maurer_curvature_explicit
#print axioms GppBoundaryHalfMaurer.half_maurer_curvature_nonzero
