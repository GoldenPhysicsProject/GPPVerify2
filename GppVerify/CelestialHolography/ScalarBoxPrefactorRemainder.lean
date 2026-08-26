import GppVerify.CelestialHolography.ScalarBoxStructuredRemainder
import Mathlib.Tactic

/-!
# Scalar-box prefactor remainder

The regulated scalar box carries an additional factor `1/κ`.  On the physical
small-regulator chamber the already established estimate `0 ≤ κ-1 ≤ δ/2` makes this
prefactor correction quantitatively harmless.  This file isolates that algebra from
the special-function remainder.
-/

namespace GppScalarBoxPrefactorRemainder

/-- If `1 ≤ κ` and `κ-1 ≤ δ/2`, then the inverse prefactor differs from one by at
most `δ/2`. -/
theorem abs_inv_kappa_sub_one_le
    {κ δ : ℝ}
    (hκ : 1 ≤ κ)
    (hκdiff : κ - 1 ≤ δ / 2) :
    |1 / κ - 1| ≤ δ / 2 := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hdiff0 : 0 ≤ κ - 1 := by linarith
  have hinvle : 1 / κ ≤ 1 := by
    apply (div_le_iff₀ hκpos).2
    simpa using hκ
  have habs : |1 / κ - 1| = (κ - 1) / κ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hinvle)]
    field_simp [hκpos.ne']
    ring
  rw [habs]
  exact (div_le_self hdiff0 hκ).trans hκdiff

/-- Exact decomposition of the prefactor-corrected remainder. -/
theorem prefactor_remainder_identity
    {D D0 κ : ℝ} (hκ : κ ≠ 0) :
    D / κ - D0 = (D - D0) / κ + (1 / κ - 1) * D0 := by
  field_simp [hκ]
  ring

/-- The prefactor correction adds at most `(δ/2)|D0|` to any core remainder bound. -/
theorem abs_prefactor_remainder_le
    {D D0 κ δ : ℝ}
    (hκ : 1 ≤ κ)
    (hκdiff : κ - 1 ≤ δ / 2) :
    |D / κ - D0| ≤ |D - D0| + (δ / 2) * |D0| := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hinv := abs_inv_kappa_sub_one_le hκ hκdiff
  have hcore : |D - D0| / κ ≤ |D - D0| :=
    div_le_self (abs_nonneg _) hκ
  rw [prefactor_remainder_identity hκpos.ne']
  calc
    |(D - D0) / κ + (1 / κ - 1) * D0| ≤
        |(D - D0) / κ| + |(1 / κ - 1) * D0| := abs_add _ _
    _ = |D - D0| / κ + |1 / κ - 1| * |D0| := by
      rw [abs_div, abs_of_pos hκpos, abs_mul]
    _ ≤ |D - D0| + (δ / 2) * |D0| := by
      gcongr

/-- Plugging any certified structured core majorant into the prefactor estimate yields
the final algebraic envelope before the overall `2/(SU)` normalization. -/
theorem abs_prefactor_remainder_le_of_core_bound
    {D D0 κ δ M : ℝ}
    (hκ : 1 ≤ κ)
    (hκdiff : κ - 1 ≤ δ / 2)
    (hcore : |D - D0| ≤ M) :
    |D / κ - D0| ≤ M + (δ / 2) * |D0| := by
  exact (abs_prefactor_remainder_le hκ hκdiff).trans
    (add_le_add_right hcore ((δ / 2) * |D0|))

end GppScalarBoxPrefactorRemainder

#print axioms GppScalarBoxPrefactorRemainder.abs_inv_kappa_sub_one_le
#print axioms GppScalarBoxPrefactorRemainder.prefactor_remainder_identity
#print axioms GppScalarBoxPrefactorRemainder.abs_prefactor_remainder_le
#print axioms GppScalarBoxPrefactorRemainder.abs_prefactor_remainder_le_of_core_bound
