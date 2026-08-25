import Mathlib.Tactic

/-!
# Five-dimensional Ward reconstruction of a four-dimensional massive-vector projector

A massive four-dimensional vector obtained from a five-dimensional massless gauge field
has cut momentum `K = (p, κ)` with `p^2 = κ^2 = μ^2`.  The correct Ward identity is

  p · J₄ = κ J₅,

not, in general, `p · J₄ = 0`.

This file formalizes the scalar algebraic core showing that the longitudinal term of the
four-dimensional massive polarization projector exactly reconstructs the fifth-current
contribution.
-/

namespace GppMassiveVectorWardReconstruction

/-- If the five-dimensional Ward identities give `p·J = κ J₅` on both sides of a
cut and `μ² = κ²`, then the longitudinal massive-projector term is exactly `J₅L J₅R`. -/
theorem longitudinal_term_eq_fifth_current
    {pJL pJR jL5 jR5 κ μ : ℝ}
    (hμ : μ ^ 2 = κ ^ 2)
    (hμ0 : μ ≠ 0)
    (hL : pJL = κ * jL5)
    (hR : pJR = κ * jR5) :
    pJL * pJR / μ ^ 2 = jL5 * jR5 := by
  rw [hL, hR, hμ]
  have hκ0 : κ ≠ 0 := by
    intro hκ
    rw [hκ, zero_pow (by norm_num)] at hμ
    have : μ ^ 2 = 0 := hμ
    exact hμ0 (sq_eq_zero_iff.mp this)
  field_simp [hκ0]
  ring

/-- Consequently the four-dimensional massive-vector projector contraction equals the
negative five-dimensional metric contraction, written here as its 4D and fifth pieces. -/
theorem massive_projector_eq_fiveDim_contraction
    {j4dot pJL pJR jL5 jR5 κ μ : ℝ}
    (hμ : μ ^ 2 = κ ^ 2)
    (hμ0 : μ ≠ 0)
    (hL : pJL = κ * jL5)
    (hR : pJR = κ * jR5) :
    -j4dot + pJL * pJR / μ ^ 2 = -j4dot + jL5 * jR5 := by
  rw [longitudinal_term_eq_fifth_current hμ hμ0 hL hR]

end GppMassiveVectorWardReconstruction

#print axioms GppMassiveVectorWardReconstruction.longitudinal_term_eq_fifth_current
#print axioms GppMassiveVectorWardReconstruction.massive_projector_eq_fiveDim_contraction
