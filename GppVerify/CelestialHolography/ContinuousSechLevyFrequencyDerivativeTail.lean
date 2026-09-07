import GppVerify.CelestialHolography.ContinuousSechLevyFrequencyDerivativeBound

/-!
# Exponential tail infrastructure for the continuous sech Lévy derivative

The global derivative bound controls the origin but is not integrable at infinity.
This file isolates the exact hyperbolic-sine lower bound needed to recover exponential
decay on `|x| >= 1`.  It is deliberately kept separate from differentiation under the
integral.
-/

namespace GppContinuousSechLevyFrequencyDerivativeTail

/-- On `|x| >= 1`, the hyperbolic denominator admits an explicit exponential lower
bound with no numerical approximation of `pi` or `exp (-2*pi)`. -/
theorem sinh_tail_lower {x : ℝ} (hx : 1 ≤ |x|) :
    ((1 - Real.exp (-(2 * Real.pi))) / 2) * Real.exp (Real.pi * |x|) ≤
      Real.sinh (Real.pi * |x|) := by
  let y : ℝ := Real.pi * |x|
  have hy : Real.pi ≤ y := by
    dsimp [y]
    nlinarith [Real.pi_pos]
  have hmono : Real.exp (-(2 * y)) ≤ Real.exp (-(2 * Real.pi)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have htail :
      Real.exp (-y) ≤ Real.exp y * Real.exp (-(2 * Real.pi)) := by
    calc
      Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp y * Real.exp (-(2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_pos y).le
  have hcore :
      ((1 - Real.exp (-(2 * Real.pi))) / 2) * Real.exp y ≤ Real.sinh y := by
    rw [Real.sinh_eq]
    nlinarith
  simpa [y] using hcore

end GppContinuousSechLevyFrequencyDerivativeTail

#print axioms GppContinuousSechLevyFrequencyDerivativeTail.sinh_tail_lower
