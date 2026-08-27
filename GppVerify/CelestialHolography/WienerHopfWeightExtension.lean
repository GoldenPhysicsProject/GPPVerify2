import GppVerify.CelestialHolography.MehlerFockSpectralWeight
import Mathlib.Tactic

/-!
# Continuous extension of the Wiener--Hopf spectral weight

The raw project weight `pi*lambda/sinh(pi*lambda)` is represented in Lean using
totalized division, so its literal value at `lambda = 0` is `0`. Analytically the
singularity is removable and the continuous value is `1`. This file separates the
mathematically intended spectral weight from that totalized-division artifact.

No continuity theorem is asserted here yet; the exact value at the origin, agreement
off the origin, and strict positivity on the whole real axis are algebraic/sign facts.
-/

namespace GppWienerHopfWeightExtension

open GppMehlerFockSpectral

/-- Wiener--Hopf weight with the removable origin assigned its analytic value `1`. -/
noncomputable def extendedWienerHopfWeight (lam : ℝ) : ℝ :=
  if lam = 0 then 1 else wienerHopfWeight lam

@[simp] theorem extendedWienerHopfWeight_zero :
    extendedWienerHopfWeight 0 = 1 := by
  simp [extendedWienerHopfWeight]

/-- Away from the removable point, the extended and raw weights agree exactly. -/
theorem extendedWienerHopfWeight_eq {lam : ℝ} (hlam : lam ≠ 0) :
    extendedWienerHopfWeight lam = wienerHopfWeight lam := by
  simp [extendedWienerHopfWeight, hlam]

/-- The extended Wiener--Hopf spectral weight is strictly positive for every real
spectral parameter, including the removable origin. -/
theorem extendedWienerHopfWeight_pos (lam : ℝ) :
    0 < extendedWienerHopfWeight lam := by
  by_cases hlam : lam = 0
  · subst lam
    simp
  · rw [extendedWienerHopfWeight_eq hlam]
    unfold wienerHopfWeight
    rcases lt_or_gt_of_ne hlam with hneg | hpos
    · exact div_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg Real.pi_pos hneg)
        (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg Real.pi_pos hneg))
    · exact div_pos
        (mul_pos Real.pi_pos hpos)
        (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hpos))

/-- Hence the extended weight never vanishes. -/
theorem extendedWienerHopfWeight_ne_zero (lam : ℝ) :
    extendedWienerHopfWeight lam ≠ 0 :=
  ne_of_gt (extendedWienerHopfWeight_pos lam)

end GppWienerHopfWeightExtension

#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_zero
#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_eq
#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_pos
#print axioms GppWienerHopfWeightExtension.extendedWienerHopfWeight_ne_zero
