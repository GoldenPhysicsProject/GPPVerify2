import Mathlib.Tactic

/-!
# Exact scalar-box regulator algebra

This file isolates the rational algebra underlying the internally regulated scalar-box
endpoint/pole geometry. It deliberately does not formalize the square-root definitions
of `R` and `κ` or the remaining dilogarithmic error estimates. The statements here are
exact consequences of the Möbius variables and the quadratic relation for `κ * R`.
-/

namespace GppScalarBoxRegulatorAlgebra

/-- For the Möbius variables `q = (1-R)/(1+R)` and
`a = (κ-1)/(κ+1)`, their difference has the exact factorization

`q-a = 2(1-κR)/((1+R)(1+κ))`.
-/
theorem q_sub_a_factorization
    (R κ q a : ℝ)
    (hR : 1 + R ≠ 0)
    (hκ : 1 + κ ≠ 0)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1)) :
    q - a = 2 * (1 - κ * R) / ((1 + R) * (1 + κ)) := by
  rw [hq, ha]
  field_simp
  ring

/-- Rationalization of the quadratic endpoint relation. If

`(κR)^2 = 1 - 4m^2/(S(U+4m))`,

then the small difference `1-κR` carries an exact factor `m^2`.
-/
theorem one_sub_kappa_mul_R_factorization
    (S U m R κ : ℝ)
    (hSU : S * (U + 4 * m) ≠ 0)
    (hplus : 1 + κ * R ≠ 0)
    (hsq : (κ * R) ^ 2 = 1 - 4 * m ^ 2 / (S * (U + 4 * m))) :
    1 - κ * R =
      (4 * m ^ 2 / (S * (U + 4 * m))) / (1 + κ * R) := by
  apply (eq_div_iff hplus).2
  calc
    (1 - κ * R) * (1 + κ * R) = 1 - (κ * R) ^ 2 := by ring
    _ = 4 * m ^ 2 / (S * (U + 4 * m)) := by rw [hsq]; ring

/-- Combining the Möbius identity with the quadratic relation gives the exact positive-scale
factorization used in the scalar-box regulator analysis:

`q-a = 8m^2 / [S(U+4m)(1+κR)(1+R)(1+κ)]`.

No positivity is asserted here; positivity follows separately once the physical domain
`S,U,m,R,κ > 0` and the relevant denominator bounds are established.
-/
theorem q_sub_a_exact_m_sq
    (S U m R κ q a : ℝ)
    (hSU : S * (U + 4 * m) ≠ 0)
    (hplus : 1 + κ * R ≠ 0)
    (hR : 1 + R ≠ 0)
    (hκ : 1 + κ ≠ 0)
    (hq : q = (1 - R) / (1 + R))
    (ha : a = (κ - 1) / (κ + 1))
    (hsq : (κ * R) ^ 2 = 1 - 4 * m ^ 2 / (S * (U + 4 * m))) :
    q - a =
      8 * m ^ 2 /
        (S * (U + 4 * m) * (1 + κ * R) * (1 + R) * (1 + κ)) := by
  rw [q_sub_a_factorization R κ q a hR hκ hq ha]
  rw [one_sub_kappa_mul_R_factorization S U m R κ hSU hplus hsq]
  field_simp
  ring

end GppScalarBoxRegulatorAlgebra

#print axioms GppScalarBoxRegulatorAlgebra.q_sub_a_factorization
#print axioms GppScalarBoxRegulatorAlgebra.one_sub_kappa_mul_R_factorization
#print axioms GppScalarBoxRegulatorAlgebra.q_sub_a_exact_m_sq
