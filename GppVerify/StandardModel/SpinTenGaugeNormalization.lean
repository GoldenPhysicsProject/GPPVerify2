import Mathlib.Tactic

/-!
# Unification-scale weak angle from the same five-mode flag

For W=C^3+C^2 and its primitive hypercharge cocharacter
H6=diag(-2,-2,-2,3,3), the Standard Model hypercharge
operator is Y=H6/6. The weak-isospin Cartan generator on
the C^2 summand is T3=diag(0,0,0,1/2,-1/2).

Tr(Y^2)=5/6, Tr(T3^2)=1/2. If the SU(5) parent gauge
kinetic term uses one normalized coupling at a common
unification scale, sin²(thetaW)=3/8 at that scale.

This is the conventional tree-level GUT boundary condition,
NOT a prediction of the low-energy measured mixing angle and
NOT a dynamical derivation of coupling unification.
-/

namespace GppSpinTenGaugeNormalization

def Y : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.diagonal (fun i => if i.val < 3 then -(1 / 3) else 1 / 2)

def T3 : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.diagonal (fun i =>
    if i.val = 3 then 1 / 2 else if i.val = 4 then -(1 / 2) else 0)

theorem hypercharge_trace_zero : Matrix.trace Y = 0 := by
  decide

theorem weak_isospin_trace_zero : Matrix.trace T3 = 0 := by
  decide

theorem hypercharge_trace_sq :
    Matrix.trace (Y * Y) = (5 / 6 : ℚ) := by
  decide

theorem weak_isospin_trace_sq :
    Matrix.trace (T3 * T3) = (1 / 2 : ℚ) := by
  decide

theorem hypercharge_to_weak_trace_ratio :
    Matrix.trace (Y * Y) / Matrix.trace (T3 * T3) = (5 / 3 : ℚ) := by
  rw [hypercharge_trace_sq, weak_isospin_trace_sq]
  norm_num

theorem gut_weak_angle_three_eighths :
    Matrix.trace (T3 * T3) /
      (Matrix.trace (T3 * T3) + Matrix.trace (Y * Y)) = (3 / 8 : ℚ) := by
  rw [hypercharge_trace_sq, weak_isospin_trace_sq]
  norm_num

end GppSpinTenGaugeNormalization

#print axioms GppSpinTenGaugeNormalization.hypercharge_trace_sq
#print axioms GppSpinTenGaugeNormalization.gut_weak_angle_three_eighths
