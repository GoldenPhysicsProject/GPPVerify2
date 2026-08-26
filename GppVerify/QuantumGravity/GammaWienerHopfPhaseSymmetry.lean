import GppVerify.QuantumGravity.GammaWienerHopfFactor
import Mathlib.Tactic

/-!
# Conjugate-reciprocal symmetry of the real-axis Gamma phase

The normalized Gamma factors already satisfy `Hminus = conj Hplus` and are both
nonzero on the real spectral axis.  Their quotient is therefore not merely unimodular:
it obeys the exact scattering-phase symmetry `conj Q = Q⁻¹`.

This remains a real-axis statement and makes no Hardy/outer/inner factor claim.
-/

namespace GppGammaWienerHopfPhase

open Complex
open GppGammaWienerHopf

/-- Real-axis Gamma phase ratio. -/
noncomputable def Q (k : ℝ) : ℂ := Hminus k / Hplus k

/-- The real-axis Gamma phase ratio never vanishes. -/
theorem Q_ne_zero (k : ℝ) : Q k ≠ 0 := by
  unfold Q
  exact div_ne_zero (Hminus_ne_zero k) (Hplus_ne_zero k)

/-- Exact conjugate-reciprocal symmetry of the Gamma phase. -/
theorem conj_Q_eq_inv (k : ℝ) :
    (starRingEnd ℂ) (Q k) = (Q k)⁻¹ := by
  have hstarMinus : (starRingEnd ℂ) (Hminus k) = Hplus k := by
    rw [Hminus_eq_conj_Hplus]
    simp
  have hstarPlus : (starRingEnd ℂ) (Hplus k) = Hminus k := by
    exact (Hminus_eq_conj_Hplus k).symm
  have hstarDiv :
      (starRingEnd ℂ) (Hminus k / Hplus k) =
        (starRingEnd ℂ) (Hminus k) / (starRingEnd ℂ) (Hplus k) := by
    exact map_div (starRingEnd ℂ) (Hminus k) (Hplus k)
  unfold Q
  rw [hstarDiv, hstarMinus, hstarPlus, inv_div]

/-- The phase ratio has unit modulus, restated in the phase notation. -/
theorem norm_Q (k : ℝ) : ‖Q k‖ = 1 := by
  exact norm_Hminus_div_Hplus k

/-- Every chamber power keeps conjugate-reciprocal symmetry. -/
theorem conj_Q_pow_eq_inv_pow (m : ℕ) (k : ℝ) :
    (starRingEnd ℂ) ((Q k) ^ m) = ((Q k) ^ m)⁻¹ := by
  rw [map_pow, conj_Q_eq_inv, inv_pow]

end GppGammaWienerHopfPhase

#print axioms GppGammaWienerHopfPhase.conj_Q_eq_inv
#print axioms GppGammaWienerHopfPhase.norm_Q
#print axioms GppGammaWienerHopfPhase.conj_Q_pow_eq_inv_pow
