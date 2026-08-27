import GppVerify.CelestialHolography.ScalarBoxStructuredPhysicalConvergence
import Mathlib.Tactic

/-!
# External numerator transfer for the regulated scalar box

An external cut numerator that is independent of the regulator and of the cut
integration variable multiplies the already-controlled scalar remainder without
changing its regulator order.  This is the exact algebraic step used to transfer
the scalar-box regulator theorem to four-dimensional cut-constructible Yang--Mills
numerators.
-/

namespace GppScalarBoxExternalNumeratorTransfer

/-- Multiplying both the regulated object and its asymptotic/core approximation by a
fixed external numerator multiplies the error bound by the numerator's absolute value. -/
theorem abs_external_mul_remainder_le
    (N J J0 B : ℝ) (hB : |J - J0| ≤ B) :
    |N * J - N * J0| ≤ |N| * B := by
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left hB (abs_nonneg N)

/-- In the physical four-point continuation `s=-S`, `u=-U`, masslessness fixes
`t=S+U`; consequently the stripped MHV Yang--Mills box numerator `s*t` is
`-S*(S+U)`. -/
theorem ym_mhv_st_numerator (S U : ℝ) :
    (-S) * (S + U) = -(S * (S + U)) := by
  ring

/-- For positive channel variables, the absolute value of the MHV numerator is
exactly `S*(S+U)`. -/
theorem abs_ym_mhv_numerator
    {S U : ℝ} (hS : 0 < S) (hU : 0 < U) :
    |-(S * (S + U))| = S * (S + U) := by
  rw [abs_neg, abs_of_pos]
  positivity

/-- The scalar remainder estimate transfers verbatim to the stripped MHV
Yang--Mills numerator.  This theorem is deliberately only the external-numerator
step: state sums, global amplitude phases, and D-dimensional rational terms are
not asserted here. -/
theorem abs_ym_mhv_remainder_le
    {S U J J0 B : ℝ} (hS : 0 < S) (hU : 0 < U)
    (hB : |J - J0| ≤ B) :
    |(-(S * (S + U))) * J - (-(S * (S + U))) * J0| ≤
      S * (S + U) * B := by
  have h := abs_external_mul_remainder_le (-(S * (S + U))) J J0 B hB
  rw [abs_ym_mhv_numerator hS hU] at h
  exact h

end GppScalarBoxExternalNumeratorTransfer

#print axioms GppScalarBoxExternalNumeratorTransfer.abs_external_mul_remainder_le
#print axioms GppScalarBoxExternalNumeratorTransfer.ym_mhv_st_numerator
#print axioms GppScalarBoxExternalNumeratorTransfer.abs_ym_mhv_numerator
#print axioms GppScalarBoxExternalNumeratorTransfer.abs_ym_mhv_remainder_le
