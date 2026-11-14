import Mathlib.Tactic

/-!
# Canonical graph connection has a parallel unitary link: a gauge no-go

For U in U(2), the tautological and orthocomplement connections of the
graph embedding into Gr(2,4) are
  A_E = (1/2) U^-1 dU,
  A_Q = -(1/2) dU U^-1.
The induced connection on Hom(E,Q) is
  D Z = dZ + A_Q Z - Z A_E.

Substituting Z=U gives D U=0 identically. This module proves the exact
underlying *noncommutative* algebra over an arbitrary ring, clearing
the factor 1/2 by multiplication by two.

In a real rank-four quaternionic bundle, the parallel unit section U
reduces holonomy from a candidate SO(4) to the SO(3) stabilizer of U.
Thus the canonical boundary connection by itself cannot generate two
independent, dynamically variable SU(2) weak gauge fields.
-/

namespace GppBoundaryGraphParallelNoGo

variable {R : Type*} [Ring R]

/-- The two projected logarithmic-derivative terms reconstruct 2*dU.
Valid in every associative ring, without commutativity. -/
theorem graph_section_twice_covariant_zero
    (U Uinv dU : R)
    (hleft : U * Uinv = 1)
    (hright : Uinv * U = 1) :
    (2 : R) * dU - (dU * Uinv) * U -
      U * (Uinv * dU) = 0 := by
  calc
    (2 : R) * dU - (dU * Uinv) * U -
      U * (Uinv * dU) =
        (2 : R) * dU - dU - dU := by
          rw [mul_assoc, hright, ← mul_assoc, hleft]
          simp
    _ = 0 := by noncomm_ring

/-- Two-sided cancellation is the exact obstruction to treating the
induced left and right connections as independent gauge variables. -/
theorem two_log_derivatives_equal
    (U Uinv dU : R)
    (hleft : U * Uinv = 1)
    (hright : Uinv * U = 1) :
    (dU * Uinv) * U = dU ∧
      U * (Uinv * dU) = dU := by
  constructor
  · rw [mul_assoc, hright, mul_one]
  · rw [← mul_assoc, hleft, one_mul]

end GppBoundaryGraphParallelNoGo

#print axioms GppBoundaryGraphParallelNoGo.graph_section_twice_covariant_zero
#print axioms GppBoundaryGraphParallelNoGo.two_log_derivatives_equal
