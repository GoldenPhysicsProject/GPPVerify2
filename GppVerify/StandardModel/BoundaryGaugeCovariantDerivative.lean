import Mathlib.Tactic

/-!
# Connection one-forms: noncommutative curvature and gauge covariance

The base ring may be any associative, noncommutative ring, including the
complex matrix algebra of a physical gauge representation. The derivation
rules and commutativity of coordinate derivatives are explicit hypotheses.

Theorems prove the local algebra of a gauge connection and its first-order
gauge transformation. They do not assume a dynamical Yang-Mills action or
derive a gauge group from a boundary. The parent boundary bundle and its
reduction are separate geometric obligations.
-/

namespace GppBoundaryGaugeCovariant

variable {R : Type*} [Ring R]

/-- A covariant derivative on a module represented by the left regular
action of an associative ring. -/
def covD (δ : R → R) (A ψ : R) : R :=
  δ ψ + A * ψ

/-- Two covariant derivatives commute up to the curvature
F_xy = δx Ay - δy Ax + [Ax,Ay].
No commutativity of the coefficient ring is assumed. -/
theorem covariant_commutator_is_curvature
    (δx δy : R → R) (Ax Ay ψ : R)
    (hx_add : ∀ u v : R, δx (u + v) = δx u + δx v)
    (hy_add : ∀ u v : R, δy (u + v) = δy u + δy v)
    (hx_mul : ∀ u v : R, δx (u * v) = δx u * v + u * δx v)
    (hy_mul : ∀ u v : R, δy (u * v) = δy u * v + u * δy v)
    (hcomm : δx (δy ψ) = δy (δx ψ)) :
    covD δx Ax (covD δy Ay ψ) -
      covD δy Ay (covD δx Ax ψ) =
        (δx Ay - δy Ax + Ax * Ay - Ay * Ax) * ψ := by
  unfold covD
  rw [hx_add, hy_add]
  rw [hx_mul, hy_mul]
  rw [hcomm]
  noncomm_ring

/-- The inverse differential identity follows by multiplying the
derivative-of-inverse relation by the inverse on the right. -/
theorem inverse_differential_cancel
    (g h dg dh : R) (gh : g * h = 1)
    (hderiv : dh * g + h * dg = 0) :
    dh + h * dg * h = 0 := by
  calc
    dh + h * dg * h = (dh * g + h * dg) * h := by
      rw [add_mul]
      rw [mul_assoc, gh]
      simp
    _ = 0 := by simp [hderiv]

/-- Exact first-jet gauge covariance.
Writing h=g^{-1}, A' = h A g + h dg and ψ'=h ψ, the transformed
covariant derivative is h times the original one.
The left two terms are d(h ψ) by the Leibniz rule. -/
theorem gauge_covariance_first_jet
    (g h A dg dh ψ dψ : R)
    (gh : g * h = 1)
    (hderiv : dh * g + h * dg = 0) :
    dh * ψ + h * dψ + (h * A * g + h * dg) * (h * ψ) =
      h * (dψ + A * ψ) := by
  have hcancel : dh + h * dg * h = 0 :=
    inverse_differential_cancel g h dg dh gh hderiv
  calc
    dh * ψ + h * dψ + (h * A * g + h * dg) * (h * ψ)
        = dh * ψ + h * dψ + h * A * (g * h) * ψ + h * dg * h * ψ := by
          noncomm_ring
    _ = (dh + h * dg * h) * ψ + h * (dψ + A * ψ) := by
          rw [gh]
          noncomm_ring
    _ = h * (dψ + A * ψ) := by simp [hcancel]

end GppBoundaryGaugeCovariant

#print axioms GppBoundaryGaugeCovariant.covariant_commutator_is_curvature
#print axioms GppBoundaryGaugeCovariant.gauge_covariance_first_jet
