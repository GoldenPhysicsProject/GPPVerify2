import Mathlib.Tactic

/-!
# Moving quaternionic real planes on the U(2) Shilov boundary

Let rho(Z) = epsilon * conj(Z) * epsilon^-1, where
epsilon = [[0,1],[-1,0]]. At determinant phase d in U(1), define
kappa_d(Z) = d * rho(Z). If d * conj(d) = 1, kappa_d is an
antilinear involution on M_2(C), so its fixed vectors form a real
four-plane. At d=1 it is the usual quaternionic copy of H.

A fixed quaternionic plane is not invariant under the entire
K = S(U(2) x U(2)) Grassmannian isotropy action. The correct
object over the U(2) boundary is the *moving* real plane
Fix(kappa_(det U)), not Fix(rho) everywhere.

This module formalizes finite 2x2 algebra and the exact
equivariance statement under explicit rho-behavior assumptions.
The geometric determinant-bundle assertion, topology, smooth
connection and full SU(2,2) conformal-equivariance are NOT claimed.
-/

namespace GppMovingQuaternionicBoundary

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Quaternionic conjugate-dual on complex 2x2 matrices. -/
def rho (Z : Mat2) : Mat2 :=
  !![star (Z 1 1), -(star (Z 1 0));
     -(star (Z 0 1)), star (Z 0 0)]

/-- It is an antilinear involution. -/
theorem rho_involutive (Z : Mat2) : rho (rho Z) = Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho]

theorem rho_add (Z W : Mat2) :
    rho (Z + W) = rho Z + rho W := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, Matrix.add_apply, star_add]

theorem rho_smul (z : ℂ) (Z : Mat2) :
    rho (z • Z) = (star z) • rho Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, Matrix.smul_apply, star_mul, mul_comm]

/-- Conjugation by the real symplectic epsilon matrix is multiplicative. -/
theorem rho_mul (Z W : Mat2) :
    rho (Z * W) = rho Z * rho W := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul] <;> ring

/-- Usual 2x2 realization of a quaternion q=a+b*j. -/
def quaternionMatrix (a b : ℂ) : Mat2 :=
  !![a, b;
     -(star b), star a]

/-- The classical quaternionic plane is the fixed set at d=1. -/
theorem quaternionMatrix_fixed (a b : ℂ) :
    rho (quaternionMatrix a b) = quaternionMatrix a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho, quaternionMatrix]

/-- A concrete four-by-four-real obstruction: a determinant-preserving
U(2)xU(2) action sends identity to this matrix, which is outside H. -/
def turnedIdentity : Mat2 :=
  !![-1, 0; 0, 1]

theorem turned_identity_not_quaternionic :
    rho turnedIdentity ≠ turnedIdentity := by
  intro h
  have h00 := congrArg (fun Z : Mat2 => Z 0 0) h
  norm_num [rho, turnedIdentity] at h00

/-- The determinant phase restores the correct reality condition. -/
def twistedRho (d : ℂ) (Z : Mat2) : Mat2 := d • rho Z

theorem twistedRho_involutive (d : ℂ)
    (hunit : d * star d = 1) (Z : Mat2) :
    twistedRho d (twistedRho d Z) = Z := by
  simp [twistedRho, rho_smul, rho_involutive, smul_smul, hunit]

theorem quaternionMatrix_twisted_at_one (a b : ℂ) :
    twistedRho 1 (quaternionMatrix a b) = quaternionMatrix a b := by
  simpa [twistedRho] using quaternionMatrix_fixed a b

/-- The transformed identity is fixed by the *new* real structure at
determinant phase d=-1. This is the moving-slice rescue. -/
theorem turned_identity_twisted_fixed :
    twistedRho (-1) turnedIdentity = turnedIdentity := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twistedRho, rho, turnedIdentity, Matrix.smul_apply]

/-- Exact matrix-algebra statement of equivariance.
In the geometric application, B and C=A^-1 are unitary, and
mu=(det B)^-1, lambda=det A, d'=(det B)/(det A)*d.
This theorem keeps those determinant identities as explicit inputs. -/
theorem twistedRho_equivariant
    (d d' mu lambda : ℂ) (B C Z : Mat2)
    (hB : rho B = mu • B)
    (hC : rho C = lambda • C)
    (hd : d' * mu * lambda = d) :
    twistedRho d' (B * Z * C) =
      B * twistedRho d Z * C := by
  calc
    twistedRho d' (B * Z * C) =
        (d' * mu * lambda) • (B * rho Z * C) := by
      simp [twistedRho, rho_mul, hB, hC,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_assoc, mul_left_comm, mul_comm]
    _ = B * twistedRho d Z * C := by
      rw [hd]
      simp [twistedRho, Matrix.smul_mul, Matrix.mul_smul]

end GppMovingQuaternionicBoundary

#print axioms GppMovingQuaternionicBoundary.rho_involutive
#print axioms GppMovingQuaternionicBoundary.quaternionMatrix_fixed
#print axioms GppMovingQuaternionicBoundary.turned_identity_not_quaternionic
#print axioms GppMovingQuaternionicBoundary.twistedRho_involutive
#print axioms GppMovingQuaternionicBoundary.twistedRho_equivariant
