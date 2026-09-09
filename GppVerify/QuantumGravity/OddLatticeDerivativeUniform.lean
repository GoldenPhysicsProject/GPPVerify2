import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Compact-uniform convergence of the odd-lattice logarithmic-derivative series

This module isolates the M-test step needed to pass from the finite odd/even
Weierstrass quotient to the `tanh` partial-fraction identity.

For

  f_n(x) = 2 x / ((2n+1)^2 + x^2),

the partial sums converge uniformly on every compact symmetric interval
`[-T,T]`.  The proof uses the explicit summable majorant

  |f_n(x)| <= 2T/(n+1)^2.

No identification of the limiting sum with `tanh` is asserted here; this is
only the analytic uniform-convergence bridge required for the subsequent
derivative-limit theorem.
-/

namespace GppOddLatticeDerivativeUniform

open Filter Set Topology

/-- The odd-lattice logarithmic-derivative summand. -/
def oddDerivativeTerm (n : ℕ) (x : ℝ) : ℝ :=
  2 * x / ((2 * (n : ℝ) + 1) ^ 2 + x ^ 2)

/-- The standard p-series majorant used on `[-T,T]`. -/
def oddDerivativeMajorant (T : ℝ) (n : ℕ) : ℝ :=
  2 * T / ((n : ℝ) + 1) ^ 2

/-- For nonnegative `T`, the compact majorant is summable. -/
theorem summable_oddDerivativeMajorant (T : ℝ) (hT : 0 ≤ T) :
    Summable (oddDerivativeMajorant T) := by
  have hbase : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
    rw [← summable_nat_add_iff 1]
    simpa using (summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hmul := hbase.mul_left (2 * T)
  simpa [oddDerivativeMajorant, div_eq_mul_inv, mul_assoc] using hmul

/-- On a compact symmetric interval, every odd-lattice term is bounded by the
summable p-series majorant. -/
theorem norm_oddDerivativeTerm_le_majorant
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-T) T) :
    ‖oddDerivativeTerm n x‖ ≤ oddDerivativeMajorant T n := by
  have hxabs : |x| ≤ T := by
    rw [abs_le]
    exact ⟨hx.1, hx.2⟩
  have hdenpos : 0 < (2 * (n : ℝ) + 1) ^ 2 + x ^ 2 := by
    positivity
  have hsmallpos : 0 < ((n : ℝ) + 1) ^ 2 := by
    positivity
  have hden : ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 + x ^ 2 := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith [sq_nonneg x]
  have hnum : |2 * x| ≤ 2 * T := by
    rw [abs_mul]
    norm_num
    nlinarith [abs_nonneg x]
  rw [oddDerivativeTerm, oddDerivativeMajorant, Real.norm_eq_abs, abs_div,
      abs_of_pos hdenpos]
  calc
    |2 * x| / ((2 * (n : ℝ) + 1) ^ 2 + x ^ 2)
        ≤ (2 * T) / ((2 * (n : ℝ) + 1) ^ 2 + x ^ 2) := by
          exact div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (2 * T) / ((n : ℝ) + 1) ^ 2 := by
          exact div_le_div_of_nonneg_left (by positivity) hsmallpos hden

/-- The partial sums of the odd logarithmic-derivative series converge uniformly
on every compact symmetric interval `[-T,T]`. -/
theorem tendstoUniformlyOn_oddDerivativeTerm
    (T : ℝ) (hT : 0 ≤ T) :
    TendstoUniformlyOn
      (fun N : ℕ => fun x : ℝ => ∑ n ∈ Finset.range N, oddDerivativeTerm n x)
      (fun x : ℝ => ∑' n : ℕ, oddDerivativeTerm n x)
      Filter.atTop (Set.Icc (-T) T) := by
  exact tendstoUniformlyOn_tsum_nat
    (summable_oddDerivativeMajorant T hT)
    (fun n x hx => norm_oddDerivativeTerm_le_majorant T hT n x hx)

end GppOddLatticeDerivativeUniform

#print axioms GppOddLatticeDerivativeUniform.summable_oddDerivativeMajorant
#print axioms GppOddLatticeDerivativeUniform.norm_oddDerivativeTerm_le_majorant
#print axioms GppOddLatticeDerivativeUniform.tendstoUniformlyOn_oddDerivativeTerm
