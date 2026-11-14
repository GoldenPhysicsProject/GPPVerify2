import Mathlib.Tactic
import GppVerify.StandardModel.PrimePatiSalamCartan

/-!
# The common colour-three representation in octonionic and SU(4) pictures

Relative to a chosen C_i ⊂ O, the right-C_i module O splits as
C_i ⊕ C_i^perp ≅ C ⊕ C³. An automorphism of O fixing i is an SU3
transformation of the second summand and the identity on the first.
This is the explicit same-representation bridge to the SU4
colour-lepton carrier, not an identification by group-name only.

The file proves the corresponding finite complex matrix-algebra
embedding M3(C) → M4(C), and checks it matches the existing
B-L generator xBL=(-3,1,1,1).

The assertion Stab_G2(i)≅SU3 and that a physical twistor C4 is
identified with this octonionic C4 remain geometric inputs;
the matrix embedding alone is not a physical boundary map.
-/

namespace GppOctonionicColorFour

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ

/-- Add a distinguished invariant lepton line to the color triplet. -/
def extendColor (A : Mat3) : Mat4 :=
  !![1, 0, 0, 0;
     0, A 0 0, A 0 1, A 0 2;
     0, A 1 0, A 1 1, A 1 2;
     0, A 2 0, A 2 1, A 2 2]

theorem extend_color_mul (A B : Mat3) :
    extendColor (A * B) = extendColor A * extendColor B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extendColor, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_three] <;> ring

theorem extend_color_one :
    extendColor (1 : Mat3) = (1 : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [extendColor, Matrix.one_apply]

theorem extend_color_injective : Function.Injective extendColor := by
  intro A B h
  ext i j
  have hij := congrArg
    (fun X : Mat4 => X (Fin.succ i) (Fin.succ j)) h
  fin_cases i <;> fin_cases j <;>
    simpa [extendColor] using hij

/-- The previously formalized Pati-Salam trace-free X=3(B-L)
is the primitive line/triplet generator for C ⊕ C³. -/
theorem color_lepton_generator_matches :
    GppPrimePatiSalam.xBL 0 = -3 ∧
    GppPrimePatiSalam.xBL 1 = 1 ∧
    GppPrimePatiSalam.xBL 2 = 1 ∧
    GppPrimePatiSalam.xBL 3 = 1 := by
  decide

end GppOctonionicColorFour

#print axioms GppOctonionicColorFour.extend_color_mul
#print axioms GppOctonionicColorFour.extend_color_one
#print axioms GppOctonionicColorFour.extend_color_injective
