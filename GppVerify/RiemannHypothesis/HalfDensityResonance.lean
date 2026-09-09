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

/-- Among positive natural-number channel labels, the resonance equation has exactly
the primitive and prime-square solutions.  This is the discrete selection statement
behind the two exceptional critical-half-density sectors. -/
theorem nat_resonance_unique {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : n * (3 - m) = 2) :
    (n = 1 ∧ m = 1) ∨ (n = 2 ∧ m = 2) := by
  have hn_le : n ≤ 2 := by
    exact Nat.le_of_dvd (by norm_num) ⟨3 - m, h.symm⟩
  have hm_lt : m < 3 := by
    by_contra hnot
    have h3 : 3 ≤ m := Nat.le_of_not_gt hnot
    have hz : 3 - m = 0 := Nat.sub_eq_zero_of_le h3
    rw [hz, Nat.mul_zero] at h
    norm_num at h
  have hm_le : m ≤ 2 := by omega
  interval_cases n <;> interval_cases m <;> norm_num at hn hm h ⊢

end GppHalfDensityResonance

#print axioms GppHalfDensityResonance.exponent_resonance_iff
#print axioms GppHalfDensityResonance.primitive_resonance
#print axioms GppHalfDensityResonance.square_resonance
#print axioms GppHalfDensityResonance.nat_resonance_unique
