import GppVerify.CelestialHolography.ScalarBoxRegulatorAlgebra
import Mathlib.Tactic

/-!
# Exact linear regulator factors for scalar-box Möbius endpoints

The regulated box uses

  q = (1-R)/(1+R),      a = (κ-1)/(κ+1).

The quadratic defining relations for `R` and `κ` can be rationalized before any
asymptotic estimate is taken.  This exposes one exact factor of the regulator `m`
in each endpoint.  Together with the already-certified quadratic estimate for `q-a`,
these identities isolate the hierarchy needed for the final logarithmic remainder.
-/

namespace GppScalarBoxEndpointLinearization

/-- Rationalizing `R² = U/(U+4m)` exposes an exact factor of `m` in the Möbius
endpoint `q=(1-R)/(1+R)`. -/
theorem q_exact_linear_m
    {U m R q : ℝ}
    (hU4 : U + 4 * m ≠ 0)
    (hR : 1 + R ≠ 0)
    (hq : q = (1 - R) / (1 + R))
    (hsq : R ^ 2 = U / (U + 4 * m)) :
    q = 4 * m / ((U + 4 * m) * (1 + R) ^ 2) := by
  have hsq' : R ^ 2 * (U + 4 * m) = U :=
    (eq_div_iff hU4).mp hsq
  rw [hq]
  field_simp [hU4, hR]
  nlinarith [hsq']

/-- Rationalizing

`κ² = 1 + 4m(S-m)/(SU)`

exposes an exact factor of `m` in `a=(κ-1)/(κ+1)`. -/
theorem a_exact_linear_m
    {S U m κ a : ℝ}
    (hSU : S * U ≠ 0)
    (hκ : κ + 1 ≠ 0)
    (ha : a = (κ - 1) / (κ + 1))
    (hsq : κ ^ 2 = 1 + 4 * m * (S - m) / (S * U)) :
    a = 4 * m * (S - m) / ((S * U) * (κ + 1) ^ 2) := by
  have hsq' : (κ ^ 2 - 1) * (S * U) = 4 * m * (S - m) := by
    have H := (sub_eq_iff_eq_add).2 hsq
    field_simp [hSU] at H ⊢
    nlinarith [H]
  rw [ha]
  field_simp [hSU, hκ]
  nlinarith [hsq']

end GppScalarBoxEndpointLinearization

#print axioms GppScalarBoxEndpointLinearization.q_exact_linear_m
#print axioms GppScalarBoxEndpointLinearization.a_exact_linear_m
