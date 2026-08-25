import Mathlib.NumberTheory.LSeries.Dirichlet
import GppVerify.RiemannHypothesis.CompletedLogDerivativeBridge
import Mathlib.Tactic

/-!
# Global von Mangoldt bridge

On the half-plane of absolute convergence, Mathlib proves that the L-series of the
von Mangoldt function is the genuine negative logarithmic derivative of the Riemann
zeta function.
-/

namespace GppGlobalVonMangoldt

open Complex LSeries Nat
open ArithmeticFunction
open scoped LSeries.notation ArithmeticFunction

/-- The complex-valued sequence obtained from the real von Mangoldt arithmetic function. -/
noncomputable def vonMangoldtComplex (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)

/-- **Global prime-power logarithmic derivative in the absolute-convergence half-plane.** -/
theorem vonMangoldtLSeries_eq_neg_zeta_logDeriv {s : ℂ} (hs : 1 < s.re) :
    L vonMangoldtComplex s = - deriv riemannZeta s / riemannZeta s := by
  simpa [vonMangoldtComplex] using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)

/-- The Riemann zeta denominator occurring above is nonzero on `Re s > 1`. -/
theorem riemannZeta_ne_zero_right_half_plane {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_ne_zero_of_one_lt_re hs

/-- Equivalent sign convention. -/
theorem neg_zeta_logDeriv_eq_vonMangoldtLSeries {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s) = L vonMangoldtComplex s := by
  have h := vonMangoldtLSeries_eq_neg_zeta_logDeriv hs
  rw [neg_div] at h
  exact h.symm

/-- The global logarithmic derivative is the explicit countable `tsum` of
von-Mangoldt L-series terms on `Re s > 1`.  This exposes the infinite-series
object needed for later prime-power regrouping and real-part/cosine extraction. -/
theorem neg_zeta_logDeriv_eq_tsum_vonMangoldt_terms {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s) =
      ∑' n : ℕ, LSeries.term vonMangoldtComplex s n := by
  rw [neg_zeta_logDeriv_eq_vonMangoldtLSeries hs]
  rfl

/-- The same global response written as the literal Dirichlet `tsum`
`∑' n, Λ(n) / n^s`.  This is the exact countable series whose real part on
`s = a + it` is the von-Mangoldt cosine series. -/
theorem neg_zeta_logDeriv_eq_tsum_vonMangoldt_div {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s / riemannZeta s) =
      ∑' n : ℕ, vonMangoldtComplex n / (n : ℂ) ^ s := by
  rw [neg_zeta_logDeriv_eq_vonMangoldtLSeries hs]
  exact LSeries_def₀ (by simp [vonMangoldtComplex]) s

end GppGlobalVonMangoldt

#print axioms GppGlobalVonMangoldt.vonMangoldtLSeries_eq_neg_zeta_logDeriv
#print axioms GppGlobalVonMangoldt.riemannZeta_ne_zero_right_half_plane
#print axioms GppGlobalVonMangoldt.neg_zeta_logDeriv_eq_vonMangoldtLSeries
#print axioms GppGlobalVonMangoldt.neg_zeta_logDeriv_eq_tsum_vonMangoldt_terms
#print axioms GppGlobalVonMangoldt.neg_zeta_logDeriv_eq_tsum_vonMangoldt_div
