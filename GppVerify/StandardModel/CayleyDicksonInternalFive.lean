import Mathlib.Tactic

/-!
# Internal complex five-plane from the nested division-algebra flag

With the distinguished nested subalgebra chain C_i ⊂ H ⊂ O,
choose the Cayley-Dickson basis
  O = span_R(1,i,j,k,l,il,jl,kl),
  H = span_R(1,i,j,k),
  C_i = span_R(1,i).

The real six-plane C_i^perp = span(j,k,l,il,jl,kl) inherits
J6(x)=x*i. The quaternionic real four-plane H inherits J4(h)=h*i.
Both operators square to -I and preserve the Euclidean norm.
Therefore W6 ⊕ W4 has a complex rank-3 ⊕ rank-2 polarization.

This module explicitly verifies the integer matrices of J6 and J4.
It does NOT formalize the octonion multiplication table or an
embedding of this external direct-sum carrier in a physical bundle.
Those are named downstream obligations.
-/

namespace GppCayleyDicksonFive

/-- Right multiplication by i on (j,k,l,il,jl,kl).
Signs follow (a,b)(c,d)=(ac - conj(d)b, da+b conj(c)). -/
def J6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ 0, 1, 0, 0, 0, 0;
     -1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0,-1, 0, 0, 0;
      0, 0, 0, 0, 0,-1;
      0, 0, 0, 0, 1, 0]

/-- Right multiplication by i on the quaternionic basis (1,i,j,k). -/
def J4 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 0,-1, 0, 0;
      1, 0, 0, 0;
      0, 0, 0, 1;
      0, 0,-1, 0]

theorem octonionic_complement_complex_structure :
    J6 * J6 = -(1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  decide

theorem quaternionic_complex_structure :
    J4 * J4 = -(1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide

theorem octonionic_complement_orthogonal :
    J6.transpose * J6 = (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  decide

theorem quaternionic_orthogonal :
    J4.transpose * J4 = (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  decide

/-- Real dimensions of the division-algebra-derived internal carrier. -/
theorem five_complex_modes_from_flag :
    (8 : ℕ) - 2 = 6 ∧
    6 / 2 = 3 ∧
    4 / 2 = 2 ∧
    (8 - 2) + 4 = 10 := by
  norm_num

end GppCayleyDicksonFive

#print axioms GppCayleyDicksonFive.octonionic_complement_complex_structure
#print axioms GppCayleyDicksonFive.quaternionic_complex_structure
#print axioms GppCayleyDicksonFive.octonionic_complement_orthogonal
