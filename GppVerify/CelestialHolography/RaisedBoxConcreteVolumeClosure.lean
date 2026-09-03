import GppVerify.CelestialHolography.RaisedBoxConcreteMoment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Concrete raised-box simplex volume closure

This file closes the normalization gap between the actual real affine-simplex
volume used by `simplexMoment` and the auxiliary complex Beta/Gamma reduction.
The concrete nested interval integral is evaluated directly by the fundamental
theorem of calculus, avoiding version-sensitive special-function integral lemmas.
-/

namespace GppRaisedBoxConcreteVolumeClosure

open Set MeasureTheory
open scoped Interval
open GppRaisedBoxConcreteMoment

/-- The actual real affine three-simplex used by the raised-box moment has
volume exactly `1/6`. -/
theorem simplexVolume_eq_one_sixth :
    simplexVolume = (1 / 6 : ℝ) := by
  have hinner : ∀ x1 : ℝ,
      (∫ x2 in (0 : ℝ)..(1 - x1), (1 - x1 - x2)) =
        (1 - x1) ^ 2 / 2 := by
    intro x1
    let F : ℝ → ℝ := fun x2 => (1 - x1) * x2 - x2 ^ 2 / 2
    have hF : ∀ x2 ∈ Set.uIcc (0 : ℝ) (1 - x1),
        HasDerivAt F (1 - x1 - x2) x2 := by
      intro x2 hx2
      dsimp [F]
      convert (by fun_prop : HasDerivAt
        (fun y : ℝ => (1 - x1) * y - y ^ 2 / 2) _ x2) using 1 <;> ring
    have hint : IntervalIntegrable (fun x2 : ℝ => 1 - x1 - x2)
        volume 0 (1 - x1) :=
      (continuous_const.sub continuous_id).intervalIntegrable
    calc
      (∫ x2 in (0 : ℝ)..(1 - x1), (1 - x1 - x2)) =
          F (1 - x1) - F 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
      _ = (1 - x1) ^ 2 / 2 := by
        dsimp [F]
        ring
  unfold simplexVolume
  simp only [intervalIntegral.integral_const]
  simp_rw [hinner]
  let G : ℝ → ℝ := fun x1 => x1 / 2 - x1 ^ 2 / 2 + x1 ^ 3 / 6
  have hG : ∀ x1 ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt G ((1 - x1) ^ 2 / 2) x1 := by
    intro x1 hx1
    dsimp [G]
    convert (by fun_prop : HasDerivAt
      (fun y : ℝ => y / 2 - y ^ 2 / 2 + y ^ 3 / 6) _ x1) using 1 <;> ring
  have hout : IntervalIntegrable (fun x1 : ℝ => (1 - x1) ^ 2 / 2)
      volume 0 1 := by
    fun_prop
  calc
    (∫ x1 in (0 : ℝ)..1, (1 - x1) ^ 2 / 2) = G 1 - G 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hG hout
    _ = (1 / 6 : ℝ) := by
      dsimp [G]
      norm_num

/-- Consequently the concrete raised-box moment at zero regulator is exactly
`1/6`. -/
theorem simplexMoment_zero_eq_one_sixth (S T : ℝ) :
    simplexMoment 0 S T = (1 / 6 : ℝ) := by
  rw [simplexMoment_zero]
  exact simplexVolume_eq_one_sixth

end GppRaisedBoxConcreteVolumeClosure

#print axioms GppRaisedBoxConcreteVolumeClosure.simplexVolume_eq_one_sixth
#print axioms GppRaisedBoxConcreteVolumeClosure.simplexMoment_zero_eq_one_sixth
