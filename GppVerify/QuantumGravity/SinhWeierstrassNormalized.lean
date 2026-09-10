import GppVerify.QuantumGravity.SinhWeierstrassProduct

/-!
# Normalized finite-product limit for the sinh Weierstrass product

The existing theorem in `SinhWeierstrassProduct` keeps the prefactor `π x` attached to the
finite product.  For the odd/even quotient argument we need the finite product itself.
Away from `x = 0`, this is obtained by multiplying the certified limit by `(π x)⁻¹`.
-/

namespace GppSinhWeierstrassNormalized

open Filter Topology

/-- Away from the removable point `x = 0`, the finite Weierstrass products themselves
    converge to `sinh (π x) / (π x)`. -/
theorem tendsto_prod_one_add_sq_div_normalized (x : ℝ) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∏ j ∈ Finset.range n,
          ((1 : ℝ) + x ^ 2 / ((j : ℝ) + 1) ^ 2))
      Filter.atTop
      (𝓝 (Real.sinh (Real.pi * x) / (Real.pi * x))) := by
  have h := GppSinhWeierstrass.tendsto_prod_one_add_sq_div x
  have hpx : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  have h' := h.const_mul (Real.pi * x)⁻¹
  convert h' using 1 <;> simp [hpx, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

end GppSinhWeierstrassNormalized

#print axioms GppSinhWeierstrassNormalized.tendsto_prod_one_add_sq_div_normalized
