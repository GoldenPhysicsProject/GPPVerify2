import GppVerify.RiemannHypothesis.ZetaThirdCumulantStrict
import GppVerify.RiemannHypothesis.ZetaGibbsFourthCumulant
import GppVerify.RiemannHypothesis.VonMangoldtQuarticPositivity
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-!
# Strict positivity of the fourth zeta-Gibbs cumulant

On `Re s > 1`, put `q_j = zeta^(j) / zeta`.  The third logarithmic response is

  -q_3 + 3 q_2 q_1 - 2 q_1^3.

Differentiating it gives the negative fourth logarithmic response

  -(q_4 - 4 q_3 q_1 - 3 q_2^2 + 12 q_2 q_1^2 - 6 q_1^4).

The all-order von Mangoldt derivative bridge identifies the same derivative with
minus the three-logarithm-weighted von Mangoldt L-series.  Hence the latter is
exactly the genuine fourth Gibbs cumulant on the real axis.  Its strict arithmetic
positivity then proves `kappa_4 > 0` for every `beta > 1`.
-/

namespace GppZetaGibbsFourthCumulantStrict

open Complex LSeries Set
open GppGlobalVonMangoldt
open GppZetaGibbsMoments
open GppZetaGibbsFisher
open GppZetaGibbsFourthCumulant
open GppZetaThirdCumulantStrict
open GppVonMangoldtCumulantDerivativeBridge
open GppVonMangoldtQuarticPositivity

noncomputable def q1 (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s
noncomputable def q2 (s : ℂ) : ℂ := deriv (deriv riemannZeta) s / riemannZeta s
noncomputable def q3 (s : ℂ) : ℂ := deriv (deriv (deriv riemannZeta)) s / riemannZeta s
noncomputable def q4 (s : ℂ) : ℂ :=
  deriv (deriv (deriv (deriv riemannZeta))) s / riemannZeta s

noncomputable def thirdResponseGeneral (s : ℂ) : ℂ :=
  -q3 s + 3 * q2 s * q1 s - 2 * (q1 s) ^ 3

noncomputable def fourthResponseGeneral (s : ℂ) : ℂ :=
  q4 s - 4 * q3 s * q1 s - 3 * (q2 s) ^ 2 +
    12 * q2 s * (q1 s) ^ 2 - 6 * (q1 s) ^ 4

/-- The existing third-response computation, repackaged as a complex function on
the whole honest half-plane. -/
theorem iteratedDeriv_two_negZetaLogDeriv_eq_thirdResponseGeneral
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 2 negZetaLogDeriv s = thirdResponseGeneral s := by
  have hsset : s ∈ zetaHalfPlane := hs
  have heq :=
    (deriv_negZetaLogDeriv_eqOn_firstResponse.iteratedDeriv_of_isOpen
      isOpen_zetaHalfPlane 1) hsset
  have hiter :
      iteratedDeriv 2 negZetaLogDeriv s = deriv firstResponse s := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ']
    simpa [iteratedDeriv_one] using heq
  rw [hiter, deriv_firstResponse_eq_thirdLogResponse hs]
  simp [thirdResponseGeneral, q1, q2, q3]

/-- The second-derivative identity holds pointwise on the open half-plane. -/
theorem iteratedDeriv_two_negZetaLogDeriv_eqOn_thirdResponseGeneral :
    zetaHalfPlane.EqOn (iteratedDeriv 2 negZetaLogDeriv) thirdResponseGeneral := by
  intro s hs
  exact iteratedDeriv_two_negZetaLogDeriv_eq_thirdResponseGeneral hs

/-- Differentiating the third logarithmic response gives minus the fourth response. -/
theorem deriv_thirdResponseGeneral_eq_neg_fourthResponseGeneral
    {s : ℂ} (hs : 1 < s.re) :
    deriv thirdResponseGeneral s = -fourthResponseGeneral s := by
  have hsset : s ∈ zetaHalfPlane := hs
  have h0 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane s hsset).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (deriv riemannZeta) (deriv (deriv riemannZeta) s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv s hsset).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (deriv (deriv riemannZeta))
      (deriv (deriv (deriv riemannZeta)) s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv.deriv s hsset).differentiableAt.hasDerivAt
  have h3 : HasDerivAt (deriv (deriv (deriv riemannZeta)))
      (deriv (deriv (deriv (deriv riemannZeta))) s) s :=
    (analyticOnNhd_riemannZeta_zetaHalfPlane.deriv.deriv.deriv s hsset).differentiableAt.hasDerivAt
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_right_half_plane hs
  have hq1 : HasDerivAt q1
      ((deriv (deriv riemannZeta) s * riemannZeta s -
        deriv riemannZeta s * deriv riemannZeta s) / riemannZeta s ^ 2) s := by
    simpa [q1] using h1.div h0 hne
  have hq2 : HasDerivAt q2
      ((deriv (deriv (deriv riemannZeta)) s * riemannZeta s -
        deriv (deriv riemannZeta) s * deriv riemannZeta s) / riemannZeta s ^ 2) s := by
    simpa [q2] using h2.div h0 hne
  have hq3 : HasDerivAt q3
      ((deriv (deriv (deriv (deriv riemannZeta))) s * riemannZeta s -
        deriv (deriv (deriv riemannZeta)) s * deriv riemannZeta s) /
        riemannZeta s ^ 2) s := by
    simpa [q3] using h3.div h0 hne
  have hthird : HasDerivAt thirdResponseGeneral
      (-((deriv (deriv (deriv (deriv riemannZeta))) s * riemannZeta s -
          deriv (deriv (deriv riemannZeta)) s * deriv riemannZeta s) /
          riemannZeta s ^ 2) +
        3 * (((deriv (deriv (deriv riemannZeta)) s * riemannZeta s -
              deriv (deriv riemannZeta) s * deriv riemannZeta s) /
              riemannZeta s ^ 2) * q1 s +
            q2 s * ((deriv (deriv riemannZeta) s * riemannZeta s -
              deriv riemannZeta s * deriv riemannZeta s) /
              riemannZeta s ^ 2)) -
        6 * (q1 s) ^ 2 *
          ((deriv (deriv riemannZeta) s * riemannZeta s -
            deriv riemannZeta s * deriv riemannZeta s) / riemannZeta s ^ 2)) s := by
    have hA := hq3.neg
    have hB := HasDerivAt.const_mul (3 : ℂ) (hq2.mul hq1)
    have hC := HasDerivAt.const_mul (2 : ℂ) (hq1.pow 3)
    convert (hA.add hB).sub hC using 1 <;>
      simp [thirdResponseGeneral] <;> ring
  rw [hthird.deriv]
  unfold fourthResponseGeneral q1 q2 q3 q4
  field_simp [hne]
  ring

/-- The third derivative of `-zeta'/zeta` is minus the fourth logarithmic response. -/
theorem iteratedDeriv_three_negZetaLogDeriv_eq_neg_fourthResponseGeneral
    {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 3 negZetaLogDeriv s = -fourthResponseGeneral s := by
  have hsset : s ∈ zetaHalfPlane := hs
  have heq :=
    (iteratedDeriv_two_negZetaLogDeriv_eqOn_thirdResponseGeneral.iteratedDeriv_of_isOpen
      isOpen_zetaHalfPlane 1) hsset
  have hiter :
      iteratedDeriv 3 negZetaLogDeriv s = deriv thirdResponseGeneral s := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ']
    simpa [iteratedDeriv_one] using heq
  rw [hiter, deriv_thirdResponseGeneral_eq_neg_fourthResponseGeneral hs]

/-- On the real axis the generalized fourth response is the existing Gibbs response. -/
theorem fourthResponseGeneral_eq_zetaFourthCumulantResponse
    {β : ℝ} :
    fourthResponseGeneral (β : ℂ) = zetaFourthCumulantResponse β := by
  unfold fourthResponseGeneral q1 q2 q3 q4 zetaFourthCumulantResponse
  simp [iteratedDeriv_succ', iteratedDeriv_one]

/-- The three-logarithm-weighted von Mangoldt L-series is exactly the genuine
fourth zeta logarithmic response on `beta > 1`. -/
theorem logMul_three_vonMangoldt_eq_zetaFourthCumulantResponse
    {β : ℝ} (hβ : 1 < β) :
    LSeries
      (LSeries.logMul (LSeries.logMul (LSeries.logMul vonMangoldtComplex)))
      (β : ℂ) = zetaFourthCumulantResponse β := by
  have hs : 1 < ((β : ℂ).re) := by simpa using hβ
  have hvm := iteratedDeriv_three_negZetaLogDeriv_eq_neg_logMul_three hs
  have hz := iteratedDeriv_three_negZetaLogDeriv_eq_neg_fourthResponseGeneral hs
  rw [fourthResponseGeneral_eq_zetaFourthCumulantResponse] at hz
  linarith

/-- The genuine fourth zeta-Gibbs cumulant is strictly positive. -/
theorem logEnergyFourthCumulant_pos
    {β : ℝ} (hβ : 1 < β) :
    0 < logEnergyFourthCumulant β := by
  have hpos := logMul_three_vonMangoldt_re_pos hβ
  rw [logMul_three_vonMangoldt_eq_zetaFourthCumulantResponse hβ] at hpos
  rw [zetaFourthCumulantResponse_eq_ofReal_logEnergyFourthCumulant hβ] at hpos
  simpa using hpos

end GppZetaGibbsFourthCumulantStrict

#print axioms GppZetaGibbsFourthCumulantStrict.deriv_thirdResponseGeneral_eq_neg_fourthResponseGeneral
#print axioms GppZetaGibbsFourthCumulantStrict.logMul_three_vonMangoldt_eq_zetaFourthCumulantResponse
#print axioms GppZetaGibbsFourthCumulantStrict.logEnergyFourthCumulant_pos
