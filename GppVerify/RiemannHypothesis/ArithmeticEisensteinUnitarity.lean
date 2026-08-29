import GppVerify.QuantumGravity.GlobalEisensteinCoefficient
import GppVerify.RiemannHypothesis.CompletedZetaReality
import GppVerify.CelestialHolography.CompletedZetaSpectralAxis
import Mathlib.Tactic

/-!
# Arithmetic Eisenstein scattering is unitary on the principal axis

The spherical global Eisenstein coefficient already formalized in
`GlobalEisensteinCoefficient` is

  phi(Delta) = Lambda(2-Delta) / Lambda(Delta),

where `Lambda` is Mathlib's completed Riemann zeta function.  On the celestial /
arithmetic principal axis `Re Delta = 1`, the shadow argument is exactly complex
conjugation:

  2-Delta = conj Delta.

Completed-zeta reality therefore turns the automorphic scattering coefficient into

  phi(Delta) = conj(Lambda(Delta)) / Lambda(Delta).

Consequently it has norm one wherever the denominator is nonzero.  This is a
genuine automorphic principal-series scattering/unitarity statement, not merely an
analogy with CFT.  It does not constrain zeros off the principal axis and is not an
RH proof.
-/

namespace GppArithmeticEisensteinUnitarity

open Complex
open GppEisenstein

/-- On the principal axis, celestial shadow is exactly Hermitian conjugation of the
spectral parameter. -/
theorem two_sub_eq_conj_of_re_one {Delta : ℂ} (hDelta : Delta.re = 1) :
    2 - Delta = conj Delta := by
  apply Complex.ext
  · simp [hDelta]
  · simp

/-- The global Eisenstein scattering coefficient is a pure completed-zeta phase on
the principal axis. -/
theorem eisensteinCoeff_eq_conj_div_of_re_one
    {Delta : ℂ} (hDelta : Delta.re = 1) :
    eisensteinCoeff Delta =
      conj (completedRiemannZeta Delta) / completedRiemannZeta Delta := by
  have hpos : 0 < Delta.re := by rw [hDelta]; norm_num
  rw [eisensteinCoeff_eq_shadow_ratio,
    two_sub_eq_conj_of_re_one hDelta,
    GppCompletedZetaReality.completedRiemannZeta_conj hpos]

/-- **Principal-series scattering unitarity.**  Away from a zero of the completed
zeta denominator, the global spherical Eisenstein coefficient has unit norm on
`Re Delta = 1`. -/
theorem norm_eisensteinCoeff_eq_one_of_re_one
    {Delta : ℂ} (hDelta : Delta.re = 1)
    (hLambda : completedRiemannZeta Delta ≠ 0) :
    ‖eisensteinCoeff Delta‖ = 1 := by
  rw [eisensteinCoeff_eq_conj_div_of_re_one hDelta, norm_div]
  rw [map_ne_zero_iff (starRingEnd ℂ), norm_ne_zero_iff.mpr hLambda]
  simp

/-- Parameterized version on `Delta(tau)=1+2 i tau`, the exact image of
`s=1/2+i tau` under `Delta=2s`. -/
theorem norm_eisensteinCoeff_principalDelta
    (tau : ℝ)
    (hLambda : completedRiemannZeta
      (GppCompletedZetaSpectralAxis.principalDelta tau) ≠ 0) :
    ‖eisensteinCoeff (GppCompletedZetaSpectralAxis.principalDelta tau)‖ = 1 := by
  exact norm_eisensteinCoeff_eq_one_of_re_one
    (GppCompletedZetaSpectralAxis.principalDelta_re tau) hLambda

/-- On the principal axis, the reflected scattering coefficient is the inverse of
the original one, matching the Weyl/shadow group law. -/
theorem reflected_eisensteinCoeff_eq_inv
    {Delta : ℂ} (hDelta : Delta.re = 1)
    (hLambda : completedRiemannZeta Delta ≠ 0) :
    eisensteinCoeff (2 - Delta) = (eisensteinCoeff Delta)⁻¹ := by
  have hshadow : completedRiemannZeta (2 - Delta) ≠ 0 := by
    rw [two_sub_eq_conj_of_re_one hDelta]
    have hpos : 0 < Delta.re := by rw [hDelta]; norm_num
    rw [GppCompletedZetaReality.completedRiemannZeta_conj hpos]
    exact map_ne_zero (starRingEnd ℂ) hLambda
  have href := eisensteinCoeff_reflection hLambda hshadow
  exact (eq_inv_iff_mul_eq_one₀ (by
    intro hzero
    rw [hzero, mul_zero] at href
    norm_num at href)).2 href

end GppArithmeticEisensteinUnitarity

#print axioms GppArithmeticEisensteinUnitarity.eisensteinCoeff_eq_conj_div_of_re_one
#print axioms GppArithmeticEisensteinUnitarity.norm_eisensteinCoeff_eq_one_of_re_one
#print axioms GppArithmeticEisensteinUnitarity.norm_eisensteinCoeff_principalDelta
#print axioms GppArithmeticEisensteinUnitarity.reflected_eisensteinCoeff_eq_inv
