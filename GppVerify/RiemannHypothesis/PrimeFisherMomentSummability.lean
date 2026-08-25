import GppVerify.RiemannHypothesis.PrimeHankelFisherSpecialization
import GppVerify.RiemannHypothesis.VonMangoldtCumulantSummability
import GppVerify.RiemannHypothesis.VonMangoldtCosineBridge
import Mathlib.Tactic

/-!
# All logarithmic Fisher moments are summable

For `β > 1`, the repaired all-order `logMul` convergence theorem implies absolute
summability of every arithmetic Fisher log-moment

  Λ(n) log(n) exp(-β log n) (log n)^r.

This is the monomial analytic input needed before finite polynomial-square packaging in
the all-order prime-gas Hankel theorem.
-/

namespace GppPrimeFisherMomentSummability

open Complex LSeries ArithmeticFunction
open GppGlobalVonMangoldt
open GppVonMangoldtCumulantSummability
open GppVonMangoldtCosine
open GppPrimeHankelFisherSpecialization
open scoped LSeries.notation ArithmeticFunction

/-- Iterating `logMul` multiplies a coefficient by the corresponding power of the
complex logarithm. -/
theorem iterated_logMul_apply (m n : ℕ) :
    ((LSeries.logMul^[m]) vonMangoldtComplex) n =
      (Complex.log n) ^ m * vonMangoldtComplex n := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp [Function.iterate_succ', Function.comp_def, ih, pow_succ]
      ring

/-- On the real spectral axis the natural-number complex power is itself real. -/
theorem natCast_neg_cpow_im_real
    (n : ℕ) (hn : n ≠ 0) (β : ℝ) :
    (((n : ℂ) ^ (-(β : ℂ))).im) = 0 := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  rw [Complex.exp_im]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
    Complex.natCast_log.symm
  rw [hlog]
  simp

/-- Real part of the negative complex power on the real axis, obtained from the
already-certified von-Mangoldt cosine bridge at frequency zero. -/
theorem natCast_neg_cpow_re_real
    (n : ℕ) (hn : n ≠ 0) (β : ℝ) :
    (((n : ℂ) ^ (-(β : ℂ))).re) = Real.exp (-Real.log n * β) := by
  have h := natCast_neg_cpow_re n hn β 0
  simpa using h

/-- The real part of the `(r+1)`-fold logarithm-weighted von Mangoldt L-series term
is exactly the `r`th Fisher log-moment summand. -/
theorem iterated_logMul_term_re_eq_fisher_moment
    (r n : ℕ) (β : ℝ) :
    (LSeries.term ((LSeries.logMul^[r + 1]) vonMangoldtComplex) (β : ℂ) n).re =
      fisherWeight β n * (Real.log n) ^ r := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fisherWeight, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, iterated_logMul_apply]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]
    rw [Complex.mul_re]
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
      Complex.natCast_log.symm
    rw [hlog]
    simp [vonMangoldtComplex,
      natCast_neg_cpow_re_real n hn β,
      natCast_neg_cpow_im_real n hn β,
      fisherWeight]
    ring

/-- Every finite logarithmic moment of the actual prime-gas Fisher weight is summable
on the honest half-plane `β > 1`. -/
theorem summable_fisherWeight_mul_log_pow
    (r : ℕ) {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => fisherWeight β n * (Real.log n) ^ r) := by
  have hs := summable_iterated_logMul_vonMangoldt (r + 1) hβ
  change Summable
    (fun n : ℕ =>
      LSeries.term ((LSeries.logMul^[r + 1]) vonMangoldtComplex) (β : ℂ) n) at hs
  have hre : Summable
      (fun n : ℕ =>
        (LSeries.term ((LSeries.logMul^[r + 1]) vonMangoldtComplex)
          (β : ℂ) n).re) :=
    Complex.reCLM.summable hs
  exact hre.congr (fun n => iterated_logMul_term_re_eq_fisher_moment r n β)

end GppPrimeFisherMomentSummability

#print axioms GppPrimeFisherMomentSummability.iterated_logMul_apply
#print axioms GppPrimeFisherMomentSummability.summable_fisherWeight_mul_log_pow
