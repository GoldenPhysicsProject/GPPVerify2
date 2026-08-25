import GppVerify.RiemannHypothesis.GlobalVonMangoldtBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
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
  rw [Complex.exp_re]
  simp [Complex.natCast_log, Real.cos_neg]
  ring

/-- Each nonzero-index von-Mangoldt term has the expected cosine real part. -/
theorem vonMangoldt_term_re_eq_exp_cos
    (n : ℕ) (hn : n ≠ 0) (a t : ℝ) :
    (LSeries.term vonMangoldtComplex
      ((a : ℂ) + (t : ℂ) * Complex.I) n).re =
      ArithmeticFunction.vonMangoldt n *
        Real.exp (-Real.log n * a) * Real.cos (Real.log n * t) := by
  rw [LSeries.term_of_ne_zero hn]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [Complex.mul_re]
  simp [vonMangoldtComplex, natCast_neg_cpow_re n hn a t]
  ring

/-- The zero-index term vanishes, matching the zero von-Mangoldt coefficient. -/
theorem vonMangoldt_term_zero_re (a t : ℝ) :
    (LSeries.term vonMangoldtComplex
      ((a : ℂ) + (t : ℂ) * Complex.I) 0).re = 0 := by
  simp

end GppVonMangoldtCosine

#print axioms GppVonMangoldtCosine.natCast_neg_cpow_re
#print axioms GppVonMangoldtCosine.vonMangoldt_term_re_eq_exp_cos
