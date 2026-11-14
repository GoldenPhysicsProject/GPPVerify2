import GppVerify.StandardModel.MovingQuaternionicBoundary
import Mathlib.Tactic

/-!
# Quaternionic compatibility of the boundary induced connection

The U(2) Shilov boundary embeds into Gr(2,4) by graph:
  U |-> Graph(U) in C^2 + C^2.

Unitary frames V=(I,U)/sqrt(2) and W=(-U^dagger,I)/sqrt(2)
of the tautological 2-plane and its orthogonal complement yield
the canonical U(2) connection matrices
  A_E = (1/2) U^-1 dU,
  A_Q = -(1/2) dU U^-1.

On a determinant-phase patch U=e^(it)q, q in SU(2), a vector in
the moving quaternionic plane is Z=e^(it)h, h in H.
The induced Hom connection becomes
  D h = d h - (1/2)(d q q^-1) h - (1/2) h(q^-1 d q).
Both Maurer forms lie in Im H, hence the connection preserves H.

This module formalizes the finite quaternionic preservation statement.
The derivative/form identities and local frame construction are stated
in the linked research note; they are not proved in Lean here.
-/

namespace GppBoundaryQuaternionicConnection

open GppMovingQuaternionicBoundary

/-- The real form rho(Z)=Z is closed under subtraction. -/
theorem rho_neg (Z : Mat2) : rho (-Z) = -rho Z := by
  simpa using rho_smul (-1 : ℂ) Z

theorem rho_sub (Z W : Mat2) :
    rho (Z - W) = rho Z - rho W := by
  simp only [sub_eq_add_neg, rho_add, rho_neg]

/-- Local Hom-connection coefficient for U=e^(it)q. The central
U(1) phase cancels and only SU(2) left/right actions survive. -/
def quaternionicCovariantStep
    (dh alpha theta h : Mat2) : Mat2 :=
  dh - (1 / 2 : ℂ) • (alpha * h + h * theta)

/-- Exact real-form compatibility of the induced left/right
connection. It requires only rho-fixed quaternionic coefficients,
so it applies to any local Maurer data in su(2) subset H. -/
theorem quaternionic_connection_preserves_real_form
    (dh alpha theta h : Mat2)
    (hdh : rho dh = dh)
    (ha : rho alpha = alpha)
    (ht : rho theta = theta)
    (hh : rho h = h) :
    rho (quaternionicCovariantStep dh alpha theta h) =
      quaternionicCovariantStep dh alpha theta h := by
  simp [quaternionicCovariantStep, rho_sub, rho_smul,
    rho_add, rho_mul, hdh, ha, ht, hh]

end GppBoundaryQuaternionicConnection

#print axioms GppBoundaryQuaternionicConnection.quaternionic_connection_preserves_real_form
