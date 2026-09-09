import Mathlib.Tactic

/-!
# Critical half-density resonance algebra

At the critical half-density weight, the smooth Möbius correction indexed by `n`
has continuum exponent `1/n - 3/2`, while the prime-repetition channel indexed by
`m` has exponent `-m/2`.  This file formalizes the exact algebraic resonance
condition between those two scaling degrees.

This is only a scaling identity.  It does not assert convergence, positivity, an
explicit-formula theorem, or RH.
-/

namespace GppHalfDensityResonance

/-- For nonzero real `n`, equality of the Möbius and repetition scaling exponents is
exactly the algebraic resonance equation `n * (3 - m) = 2`. -/
theorem exponent_resonance_iff {n m : ℝ} (hn : n ≠ 0) :
    1 / n - 3 / 2 = -m / 2 ↔ n * (3 - m) = 2 := by
  constructor
  · intro h
    field_simp [hn] at h
    nlinarith
  · intro h
    field_simp [hn]
    nlinarith

/-- The leading primitive channel is resonant: `(n,m) = (1,1)`. -/
theorem primitive_resonance :
    (1 : ℝ)⁻¹ - 3 / 2 = -(1 : ℝ) / 2 := by
  norm_num

/-- The prime-square channel is the nontrivial secondary resonance: `(n,m) = (2,2)`. -/
theorem square_resonance :
    (2 : ℝ)⁻¹ - 3 / 2 = -(2 : ℝ) / 2 := by
  norm_num

end GppHalfDensityResonance

#print axioms GppHalfDensityResonance.exponent_resonance_iff
#print axioms GppHalfDensityResonance.primitive_resonance
#print axioms GppHalfDensityResonance.square_resonance
