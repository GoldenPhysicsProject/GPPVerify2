import GppVerify.RiemannHypothesis.GlobalVonMangoldtBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-!
# Von Mangoldt cosine bridge

This file simplifies the real part of each absolutely-convergent von-Mangoldt
L-series term on `s = a + i t` to the expected exponential-decay cosine kernel.
-/

namespace GppVonMangoldtCosine

open Complex LSeries
open ArithmeticFunction
open GppGlobalVonMangoldt

/-- Real part of the negative complex power of a positive integer base. -/
theorem natCast_neg_cpow_re
    (n : ℕ) (hn : n ≠ 0) (a t : ℝ) :
    (((n : ℂ) ^ (-((a : ℂ) + (t : ℂ) * Complex.I))).re) =
      Real.exp (-Real.log n * a) * Real.cos (Real.log n * t) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
    Complex.natCast_log.symm
  rw [hlog]
  rw [Complex.exp_re]
  have hre :
      (((Real.log n : ℂ) * -((a : ℂ) + (t : ℂ) * Complex.I)).re) =
        -Real.log n * a := by
    change Real.log n * (-a) - 0 * (-t) = -Real.log n * a
    ring
  have him :
      (((Real.log n : ℂ) * -((a : ℂ) + (t : ℂ) * Complex.I)).im) =
        -Real.log n * t := by
    change Real.log n * (-t) + 0 * (-a) = -Real.log n * t
    ring
  rw [hre, him]
  have hcos : Real.cos (-Real.log n * t) = Real.cos (Real.log n * t) := by
    rw [show -Real.log n * t = -(Real.log n * t) by ring, Real.cos_neg]
  rw [hcos]
  ring_nf

/-- Each nonzero-index von-Mangoldt term has the expected cosine real part. -/
theorem vonMangoldt_term_re_eq_exp_cos
    (n : ℕ) (hn : n ≠ 0) (a t : ℝ) :
    (LSeries.term vonMangoldtComplex
      ((a : ℂ) + (t : ℂ) * Complex.I) n).re =
      ArithmeticFunction.vonMangoldt n *
        Real.exp (-Real.log n * a) * Real.cos (Real.log n * t) := by
  rw [LSeries.term_of_ne_zero hn]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  change
    (((ArithmeticFunction.vonMangoldt n : ℂ) *
      ((n : ℂ) ^ (-((a : ℂ) + (t : ℂ) * Complex.I)))).re) =
      ArithmeticFunction.vonMangoldt n *
        Real.exp (-Real.log n * a) * Real.cos (Real.log n * t)
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [natCast_neg_cpow_re n hn a t]
  ring

/-- The zero-index term vanishes. -/
theorem vonMangoldt_term_zero_re (a t : ℝ) :
    (LSeries.term vonMangoldtComplex
      ((a : ℂ) + (t : ℂ) * Complex.I) 0).re = 0 := by
  simp

/-- Global von-Mangoldt cosine series on the half-plane of absolute convergence. -/
theorem neg_zeta_logDeriv_re_eq_vonMangoldt_cosine_tsum
    {a t : ℝ} (ha : 1 < a) :
    (-(deriv riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I) /
      riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I))).re =
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n *
        Real.exp (-Real.log n * a) * Real.cos (Real.log n * t) := by
  have hs : 1 < (((a : ℂ) + (t : ℂ) * Complex.I).re) := by
    simpa using ha
  rw [neg_zeta_logDeriv_re_eq_tsum_re_terms hs]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact vonMangoldt_term_re_eq_exp_cos n hn a t

end GppVonMangoldtCosine

#print axioms GppVonMangoldtCosine.natCast_neg_cpow_re
#print axioms GppVonMangoldtCosine.vonMangoldt_term_re_eq_exp_cos
#print axioms GppVonMangoldtCosine.neg_zeta_logDeriv_re_eq_vonMangoldt_cosine_tsum
