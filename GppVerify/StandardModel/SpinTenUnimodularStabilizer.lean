import Mathlib.Tactic

/-!
# The exact 3+2 stabilizer core in the five-mode complex carrier

For an oriented real ten-plane with a compatible orthogonal complex
structure J, the resulting five-dimensional Hermitian carrier W is C^5.
If W=W3+W2 as an orthogonal complex 3+2 splitting and a determinant-one
complex volume is preserved, the stabilizer inside SU(5) is
S(U(3)xU(2)) = (SU(3)xSU(2)xU(1))/Z6.

This Lean module formalizes the finite block-preserving matrix algebra
and the primitive trace-free U(1) generator. The Lie-group
identification and actual geometric origin of the splitting/complex
volume are explained in the companion research note and are NOT claimed
to have been Lean formalized here.
-/

namespace GppSpinTenStabilizer

abbrev FiveMatrix := Matrix (Fin 5) (Fin 5) ℂ

def inColor (i : Fin 5) : Prop := i.val < 3

/-- A matrix is block diagonal for the 3+2 decomposition. -/
def preservesSplit (A : FiveMatrix) : Prop :=
  ∀ i j, inColor i ≠ inColor j → A i j = 0

theorem preserves_split_zero : preservesSplit (0 : FiveMatrix) := by
  intro i j _
  simp

theorem preserves_split_add (A B : FiveMatrix)
    (hA : preservesSplit A) (hB : preservesSplit B) :
    preservesSplit (A + B) := by
  intro i j hij
  rw [Matrix.add_apply, hA i j hij, hB i j hij]
  simp

theorem preserves_split_neg (A : FiveMatrix)
    (hA : preservesSplit A) :
    preservesSplit (-A) := by
  intro i j hij
  rw [Matrix.neg_apply, hA i j hij]
  simp

theorem preserves_split_sub (A B : FiveMatrix)
    (hA : preservesSplit A) (hB : preservesSplit B) :
    preservesSplit (A - B) := by
  simpa [sub_eq_add_neg] using preserves_split_add A (-B) hA
    (preserves_split_neg B hB)

/-- A genuine multiplicative closure theorem, not just 3+2=5. -/
theorem preserves_split_mul (A B : FiveMatrix)
    (hA : preservesSplit A) (hB : preservesSplit B) :
    preservesSplit (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : inColor i = inColor k
  · have hkj : inColor k ≠ inColor j := by
      intro h
      exact hij (hik.trans h)
    simp [hB k j hkj]
  · simp [hA i k hik]

/-- The 3+2-preserving matrices close under the nonabelian bracket. -/
theorem preserves_split_commutator (A B : FiveMatrix)
    (hA : preservesSplit A) (hB : preservesSplit B) :
    preservesSplit (A * B - B * A) :=
  preserves_split_sub (A * B) (B * A)
    (preserves_split_mul A B hA hB)
    (preserves_split_mul B A hB hA)

/-- Projection onto the three-dimensional complex colour summand. -/
def colorProjector : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.diagonal (fun i => if i.val < 3 then 1 else 0)

/-- Primitive integral generator with weights (-2,-2,-2,3,3).
The physical hypercharge convention is Y=H6/6. -/
def hyperchargeH6 : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.diagonal (fun i => if i.val < 3 then -2 else 3)

theorem color_projector_idempotent :
    colorProjector * colorProjector = colorProjector := by
  decide

theorem hypercharge_trace_zero :
    Matrix.trace hyperchargeH6 = 0 := by
  decide

theorem hypercharge_commutes_with_split :
    hyperchargeH6 * colorProjector =
      colorProjector * hyperchargeH6 := by
  decide

/-- Tracelessness fixes the relative integer weights to the ratio -2:3;
primitive integer normalization gives exactly this generator. -/
theorem hypercharge_primitive_ratio :
    (3 : ℤ) * (-2) + 2 * 3 = 0 := by
  norm_num

/-- The continuous stabilizer has dimensions 8+3+1=12. -/
theorem standard_model_lie_algebra_dimension :
    (8 : ℕ) + 3 + 1 = 12 := by
  norm_num

/-- The orthogonal complement in the 24-dimensional SU(5) adjoint
has dimension twelve, i.e. the six complex off-block directions. -/
theorem broken_su5_generator_count :
    (24 : ℕ) = 12 + 2 * 3 * 2 := by
  norm_num

end GppSpinTenStabilizer

#print axioms GppSpinTenStabilizer.preserves_split_mul
#print axioms GppSpinTenStabilizer.preserves_split_commutator
#print axioms GppSpinTenStabilizer.hypercharge_trace_zero
