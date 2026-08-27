import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Abstract Gibbs cumulant differential algebra

For an exponential-family moment hierarchy with

  Z'  = -M1,
  M1' = -M2,
  M2' = -M3,
  M3' = -M4,

the normalized third cumulant differentiates to minus the normalized fourth
cumulant.  This file isolates the quotient-rule algebra independently of zeta,
so the arithmetic Gibbs specialization only has to prove the raw-moment derivative
hierarchy and nonvanishing of the partition function.
-/

namespace GppGibbsCumulantDifferentialAlgebra

/-- Third cumulant written in terms of unnormalized moments. -/
noncomputable def kappa3Expr
    (Z M1 M2 M3 : ℝ → ℝ) (β : ℝ) : ℝ :=
  M3 β / Z β -
    3 * (M2 β / Z β) * (M1 β / Z β) +
    2 * (M1 β / Z β) ^ 3

/-- Fourth cumulant written in terms of unnormalized moments. -/
noncomputable def kappa4Expr
    (Z M1 M2 M3 M4 : ℝ → ℝ) (β : ℝ) : ℝ :=
  M4 β / Z β -
    4 * (M3 β / Z β) * (M1 β / Z β) -
    3 * (M2 β / Z β) ^ 2 +
    12 * (M2 β / Z β) * (M1 β / Z β) ^ 2 -
    6 * (M1 β / Z β) ^ 4

/-- **Universal exponential-family cumulant law**:
if the unnormalized moments satisfy the canonical derivative ladder, then
`kappa3' = -kappa4`. -/
theorem hasDerivAt_kappa3Expr
    {Z M1 M2 M3 M4 : ℝ → ℝ} {β : ℝ}
    (hZ : HasDerivAt Z (-M1 β) β)
    (h1 : HasDerivAt M1 (-M2 β) β)
    (h2 : HasDerivAt M2 (-M3 β) β)
    (h3 : HasDerivAt M3 (-M4 β) β)
    (hZne : Z β ≠ 0) :
    HasDerivAt (kappa3Expr Z M1 M2 M3)
      (-(kappa4Expr Z M1 M2 M3 M4 β)) β := by
  have hM3Z := h3.div hZ hZne
  have hM2Z := h2.div hZ hZne
  have hM1Z := h1.div hZ hZne
  have hprod := hM2Z.mul hM1Z
  have hcubic := hM1Z.pow 3
  have hsum := hM3Z.sub (hprod.const_mul 3) |>.add (hcubic.const_mul 2)
  convert hsum using 1
  · funext x
    simp [kappa3Expr]
    ring
  · simp [kappa4Expr]
    field_simp [hZne]
    ring

end GppGibbsCumulantDifferentialAlgebra

#print axioms GppGibbsCumulantDifferentialAlgebra.hasDerivAt_kappa3Expr
