import GppVerify.RiemannHypothesis.CompletedZetaCriticalResponse
import Mathlib.Tactic

namespace GppCompletedZetaPrincipalSeriesResponse

open Complex

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

end GppCompletedZetaPrincipalSeriesResponse

#print axioms GppCompletedZetaPrincipalSeriesResponse.half_argument_re_eq_half
#print axioms GppCompletedZetaPrincipalSeriesResponse.celestialCompletedResponse_re_eq_zero
