import GppVerify.RiemannHypothesis.ZetaGibbsMoments
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Bridge from L-series logarithmic insertions to real Gibbs moments

For real `β > 1`, the constant-one L-series and its first two logarithmic coefficient
insertions are exactly the complex embeddings of the unnormalized real Gibbs partition
sum, first log-energy moment, and second log-energy moment. This closes the indexing
and coercion interface between the L-series derivative formalism and the real weighted
variance theorem.
-/

namespace GppZetaGibbsMomentBridge

open Complex LSeries
open GppZetaGibbsSummability

open scoped Topology

/-- The constant-one L-series on the real axis is the embedded real Gibbs partition sum. -/
theorem LSeries_one_eq_ofReal_gibbsWeight_tsum {β : ℝ} (hβ : 1 < β) :
    LSeries (fun _ : ℕ => (1 : ℂ)) (β : ℂ) =
      ((∑' n, gibbsWeight β n : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  have hs : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) (β : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (constant_abscissa_le_one.trans_lt (by exact_mod_cast hβ))
  change Summable (fun n => LSeries.term (fun _ : ℕ => (1 : ℂ)) (β : ℂ) n) at hs
  rw [hs.tsum_eq_zero_add]
  have hzero : LSeries.term (fun _ : ℕ => (1 : ℂ)) (β : ℂ) 0 = 0 := by
    simp [LSeries.term]
  rw [hzero, zero_add]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), gibbsWeight,
    Complex.ofReal_cpow (Nat.cast_nonneg (n + 1))]

/-- One logarithmic L-series insertion is the embedded first Gibbs log-energy moment. -/
theorem LSeries_logMul_one_eq_ofReal_firstMoment {β : ℝ} (hβ : 1 < β) :
    LSeries (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ) =
      ((∑' n, gibbsWeight β n * logEnergy n : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  have hs : LSeriesSummable (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa using constant_abscissa_le_one.trans_lt (by exact_mod_cast hβ))
  change Summable
    (fun n => LSeries.term (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ) n) at hs
  rw [hs.tsum_eq_zero_add]
  have hzero : LSeries.term (LSeries.logMul (fun _ : ℕ => (1 : ℂ))) (β : ℂ) 0 = 0 := by
    simp [LSeries.term]
  rw [hzero, zero_add]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), LSeries.logMul,
    gibbsWeight, logEnergy, Complex.natCast_log,
    Complex.ofReal_cpow (Nat.cast_nonneg (n + 1)), mul_comm, div_eq_mul_inv]

/-- Two logarithmic L-series insertions give the embedded second Gibbs log-energy moment. -/
theorem LSeries_logMul_logMul_one_eq_ofReal_secondMoment {β : ℝ} (hβ : 1 < β) :
    LSeries (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) (β : ℂ) =
      ((∑' n, gibbsWeight β n * (logEnergy n) ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold LSeries
  have hs : LSeriesSummable
      (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) (β : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa using constant_abscissa_le_one.trans_lt (by exact_mod_cast hβ))
  change Summable
    (fun n => LSeries.term
      (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) (β : ℂ) n) at hs
  rw [hs.tsum_eq_zero_add]
  have hzero : LSeries.term
      (LSeries.logMul (LSeries.logMul (fun _ : ℕ => (1 : ℂ)))) (β : ℂ) 0 = 0 := by
    simp [LSeries.term]
  rw [hzero, zero_add]
  apply tsum_congr
  intro n
  simp [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), LSeries.logMul,
    gibbsWeight, logEnergy, Complex.natCast_log,
    Complex.ofReal_cpow (Nat.cast_nonneg (n + 1)), pow_two, mul_comm, mul_left_comm,
    mul_assoc, div_eq_mul_inv]

end GppZetaGibbsMomentBridge

#print axioms GppZetaGibbsMomentBridge.LSeries_one_eq_ofReal_gibbsWeight_tsum
#print axioms GppZetaGibbsMomentBridge.LSeries_logMul_one_eq_ofReal_firstMoment
#print axioms GppZetaGibbsMomentBridge.LSeries_logMul_logMul_one_eq_ofReal_secondMoment
