import GppVerify.RiemannHypothesis.ScaleShadowHalfDensity
import Mathlib.Tactic

/-!
# Conformal shadow and the principal-series line

For a scalar conformal weight `Delta` in real boundary dimension `d`, the shadow
involution is

  Delta |-> d - Delta.

Because `d` is real, this shadow equals Hermitian conjugation exactly on the
principal-series axis `Re Delta = d/2`.  The one-dimensional specialization is the
arithmetic reflection `s |-> 1-s`, whose principal line is `Re s = 1/2`.  Under the
project dictionary `Delta = 2s`, the same statement becomes the two-dimensional
celestial shadow `Delta |-> 2-Delta` with principal line `Re Delta = 1`.

These are representation-theoretic identities only; no zeta-zero statement is used.
-/

namespace GppConformalShadowPrincipalSeries

open Complex
open GppScaleShadow

/-- Scalar conformal shadow in real boundary dimension `d`. -/
noncomputable def conformalShadow (d : ℝ) (Delta : ℂ) : ℂ := (d : ℂ) - Delta

/-- Conformal shadow is an involution. -/
theorem conformalShadow_involutive (d : ℝ) (Delta : ℂ) :
    conformalShadow d (conformalShadow d Delta) = Delta := by
  unfold conformalShadow
  ring

/-- The principal-series axis is exactly the locus where scalar shadow equals
Hermitian conjugation. -/
theorem conformalShadow_eq_conj_iff (d : ℝ) (Delta : ℂ) :
    conformalShadow d Delta = (starRingEnd ℂ) Delta ↔ Delta.re = d / 2 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    simp [conformalShadow] at hr
    linarith
  · intro h
    apply Complex.ext
    · simp [conformalShadow]
      linarith
    · simp [conformalShadow]

/-- In one boundary dimension, the conformal shadow is literally the arithmetic
reflection `s |-> 1-s`. -/
theorem one_dimensional_shadow_eq_arithmetic (s : ℂ) :
    conformalShadow 1 s = 1 - s := by
  simp [conformalShadow]

/-- Consequently, the one-dimensional shadow is Hermitian conjugation exactly on the
Riemann critical line. -/
theorem one_dimensional_shadow_eq_conj_iff (s : ℂ) :
    conformalShadow 1 s = (starRingEnd ℂ) s ↔ s.re = 1 / 2 := by
  simpa using conformalShadow_eq_conj_iff 1 s

/-- Under `Delta = 2s`, arithmetic shadow is exactly the two-dimensional celestial
shadow. -/
theorem doubled_arithmetic_shadow_eq_two_dimensional (s : ℂ) :
    celestialDelta (1 - s) = conformalShadow 2 (celestialDelta s) := by
  rw [celestialDelta_shadow]
  simp [conformalShadow]

/-- Under `Delta = 2s`, the Riemann critical line is exactly the `d=2` celestial
principal-series line `Re Delta = 1`. -/
theorem critical_line_iff_two_dimensional_principal (s : ℂ) :
    s.re = 1 / 2 ↔ (celestialDelta s).re = 2 / 2 := by
  rw [show (2 : ℝ) / 2 = 1 by norm_num]
  exact (celestialDelta_re_eq_one_iff s).symm

end GppConformalShadowPrincipalSeries

#print axioms GppConformalShadowPrincipalSeries.conformalShadow_involutive
#print axioms GppConformalShadowPrincipalSeries.conformalShadow_eq_conj_iff
#print axioms GppConformalShadowPrincipalSeries.one_dimensional_shadow_eq_arithmetic
#print axioms GppConformalShadowPrincipalSeries.one_dimensional_shadow_eq_conj_iff
#print axioms GppConformalShadowPrincipalSeries.doubled_arithmetic_shadow_eq_two_dimensional
#print axioms GppConformalShadowPrincipalSeries.critical_line_iff_two_dimensional_principal
