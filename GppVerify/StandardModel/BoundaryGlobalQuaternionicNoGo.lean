import GppVerify.StandardModel.MovingQuaternionicBoundary
import Mathlib.Tactic

/-!
# Global quaternionic boundary frame and diagonal-connection reduction

For unitary 2x2 U, rho(U) = (det U)^-1 U. The relation is an
elementary adjugate identity: rho(U)=adj(U†) and U†=U^-1.

This module proves the resulting real-form and gauge-action statements
under the displayed 2x2 unitary identity as an EXPLICIT hypothesis.
Formalizing the adjugate identity from Matrix.IsUnitary is the next step.
The section h=1 is parallel, and the induced Hom connection reduces
to the adjoint SU(2), not SU(2)_L x SU(2)_R independent fields.
-/

namespace GppBoundaryGlobalQuaternionic

open GppMovingQuaternionicBoundary

/-- Every vector U h in the real fixed plane is obtained from a
rho-fixed quaternionic h, provided rho(U)=d^-1 U. -/
theorem global_frame_maps_quaternions_to_moving_plane
    (d e : ℂ) (U h : Mat2)
    (hde : d * e = 1)
    (hU : rho U = e • U)
    (hh : rho h = h) :
    twistedRho d (U * h) = U * h := by
  calc
    twistedRho d (U * h) = d • ((e • U) * h) := by
      simp [twistedRho, rho_mul, hU, hh]
    _ = (d * e) • (U * h) := by
      rw [Matrix.smul_mul, smul_smul]
    _ = U * h := by rw [hde]; simp

/-- Conversely, multiplication by U^-1 takes the moving fixed plane
back to ordinary quaternions, provided rho(U^-1)=d U^-1. -/
theorem global_frame_inverse_maps_moving_to_quaternions
    (d e : ℂ) (Uinv Z : Mat2)
    (hde : d * e = 1)
    (hUinv : rho Uinv = d • Uinv)
    (hfixed : twistedRho d Z = Z) :
    rho (Uinv * Z) = Uinv * Z := by
  have hZ : rho Z = e • Z := by
    have hz := congrArg (fun W : Mat2 => e • W) hfixed
    simpa [twistedRho, smul_smul, mul_comm, hde] using hz
  calc
    rho (Uinv * Z) = (d • Uinv) * (e • Z) := by
      rw [rho_mul, hUinv, hZ]
    _ = (d * e) • (Uinv * Z) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = Uinv * Z := by rw [hde]; simp

/-- A global frame h=U^-1 Z transforms by conjugation with only
the right-hand boundary factor A; the left B factor cancels.
This is the algebraic reason the boundary isotropy is diagonal. -/
theorem global_frame_gauge_action
    {R : Type*} [Ring R]
    (A Ainv B Binv Uinv Z : R)
    (hinvB : Binv * B = 1) :
    (A * Uinv * Binv) * (B * Z * Ainv) =
      A * (Uinv * Z) * Ainv := by
  calc
    (A * Uinv * Binv) * (B * Z * Ainv) =
      A * Uinv * (Binv * B) * Z * Ainv := by noncomm_ring
    _ = A * (Uinv * Z) * Ainv := by rw [hinvB]; noncomm_ring

/-- A parallel unit link eliminates the relative left/right part.
This is the exact polynomial connection identity for h=1. -/
theorem scalar_direction_parallel
    {R : Type*} [Ring R] (theta : R) :
    theta * (1 : R) - 1 * theta = 0 := by
  simp

/-- Connection in the global frame h=U^-1 Z.
With d(Uh)=dU h+U dh and A_Q=-(1/2)dU U^-1,
A_E=(1/2)U^-1 dU, the equation is:
  2 D(Uh) = U(2 dh+[U^-1 dU,h]).
It holds in any associative ring; it is not a dimension count. -/
theorem graph_connection_global_frame
    {R : Type*} [Ring R]
    (U Uinv dU h dh : R)
    (hinvL : Uinv * U = 1)
    (hinvR : U * Uinv = 1) :
    (2 : R) * (dU * h + U * dh) -
      (dU * Uinv) * (U * h) -
      (U * h) * (Uinv * dU) =
        U * ((2 : R) * dh + (Uinv * dU) * h - h * (Uinv * dU)) := by
  have h1 : (dU * Uinv) * (U * h) = dU * h := by
    calc
      (dU * Uinv) * (U * h) = dU * (Uinv * U) * h := by
        simp only [mul_assoc]
      _ = dU * h := by rw [hinvL]; simp
  have h2 : (U * h) * (Uinv * dU) = U * (h * (Uinv * dU)) := by
    simp only [mul_assoc]
  have h3 : U * ((Uinv * dU) * h) = dU * h := by
    calc
      U * ((Uinv * dU) * h) = (U * Uinv) * (dU * h) := by
        simp only [mul_assoc]
      _ = dU * h := by rw [hinvR]; simp
  calc
    (2 : R) * (dU * h + U * dh) -
      (dU * Uinv) * (U * h) -
      (U * h) * (Uinv * dU) =
        (2 : R) * (dU * h + U * dh) -
          dU * h - U * (h * (Uinv * dU)) := by rw [h1, h2]
    _ = U * ((2 : R) * dh +
           (Uinv * dU) * h - h * (Uinv * dU)) := by
      rw [← h3]
      noncomm_ring

end GppBoundaryGlobalQuaternionic

#print axioms GppBoundaryGlobalQuaternionic.global_frame_gauge_action
#print axioms GppBoundaryGlobalQuaternionic.graph_connection_global_frame
