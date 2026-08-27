import GppVerify.RiemannHypothesis.CompletedZetaCriticalResponse
import GppVerify.CelestialHolography.PositiveRealPrincipalSeries
import Mathlib.Tactic

namespace GppCompletedZetaPrincipalSeriesResponse

open Complex
open GppPositiveReal

noncomputable def celestialCompletedResponse (Δ : ℂ) : ℂ :=
  deriv GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) /
    GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2)

theorem half_argument_re_eq_half {Δ : ℂ} (hΔ : Δ.re = 1) :
    (Δ / 2).re = 1 / 2 := by
  simp [Complex.div_re, hΔ]
  norm_num

theorem celestialCompletedResponse_re_eq_zero
    {Δ : ℂ} (hΔ : Δ.re = 1)
    (hΛ : GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) ≠ 0) :
    (celestialCompletedResponse Δ).re = 0 := by
  unfold celestialCompletedResponse
  exact GppCompletedZetaCriticalResponse.completedRiemannZeta_logDeriv_re_eq_zero_of_re_half
    (half_argument_re_eq_half hΔ) hΛ

/-- Under the exact dictionary `Δ = 2s`, the globally reflected logarithmic response
of completed zeta becomes an odd response under the scalar celestial shadow
`Δ ↦ 2 - Δ`.  The exclusions `Δ ≠ 0,2` are precisely the two completed-zeta poles,
and `hΛ` records the domain of the logarithmic derivative. -/
theorem celestialCompletedResponse_shadow_odd
    {Δ : ℂ} (hΔ0 : Δ ≠ 0) (hΔ2 : Δ ≠ 2)
    (hΛ : GppCompletedZetaDerivative.completedRiemannZeta (Δ / 2) ≠ 0) :
    celestialCompletedResponse Δ =
      -celestialCompletedResponse (celestialShadow Δ) := by
  have hs0 : Δ / 2 ≠ 0 := by
    exact div_ne_zero hΔ0 (by norm_num)
  have hs1 : Δ / 2 ≠ 1 := by
    intro hs
    apply hΔ2
    calc
      Δ = 2 * (Δ / 2) := by ring
      _ = 2 := by rw [hs]; ring
  have hreflect :=
    GppCompletedZetaDerivative.completedRiemannZeta_logDeriv_reflection hs0 hs1 hΛ
  have harg : 1 - Δ / 2 = celestialShadow Δ / 2 := by
    simp [celestialShadow]
    ring
  unfold celestialCompletedResponse
  rw [harg] at hreflect
  exact hreflect

end GppCompletedZetaPrincipalSeriesResponse

#print axioms GppCompletedZetaPrincipalSeriesResponse.half_argument_re_eq_half
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedResponse_re_eq_zero
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedResponse_shadow_odd
