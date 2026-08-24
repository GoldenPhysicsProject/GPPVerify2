import GppVerify.RiemannHypothesis.SechFourthIntegral
import Mathlib.Tactic

/-!
# Exact half-line `sech^6` integral

This is the analytic core needed for the salvaged Wiener--Hopf/Parseval evaluation
of the full-plane cubic spectral-weight convolution.  The geometric A2 chamber
reduction is deliberately left separate.

We prove

  `∫_{0}^{∞} sech^6 x dx = 8/15`,

hence the full even integral is expected to be `16/15` once the symmetry step is
formalized.  No RH or amplitude claim is made here.
-/

namespace GppSechIntegral

open Filter MeasureTheory

/-- A polynomial antiderivative of `sech^6 x` in `tanh x`. -/
noncomputable def sechSixthAntideriv (x : ℝ) : ℝ :=
  Real.tanh x - (2/3 : ℝ) * Real.tanh x ^ 3 + (1/5 : ℝ) * Real.tanh x ^ 5

/-- Exact derivative: `F₆'(x)=1/cosh^6 x`. -/
theorem hasDerivAt_sechSixthAntideriv (x : ℝ) :
    HasDerivAt sechSixthAntideriv (1 / Real.cosh x ^ 6) x := by
  have ht := hasDerivAt_tanh' x
  have h := ht.sub ((ht.pow 3).const_mul (2/3 : ℝ)) |>.add
    ((ht.pow 5).const_mul (1/5 : ℝ))
  have hc6 : 1 / Real.cosh x ^ 6 = (1 - Real.tanh x ^ 2) ^ 3 := by
    rw [← one_div_cosh_sq]
    ring
  convert h using 1
  · rfl
  · rw [hc6]
    ring

/-- The elementary exponential form of `tanh`, useful for its limit at `+∞`. -/
theorem tanh_eq_exp_ratio (x : ℝ) :
    Real.tanh x =
      (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) := by
  have hsplit : Real.exp (-x) = Real.exp x * Real.exp (-(2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, hsplit]
  have hd : Real.exp x + Real.exp x * Real.exp (-(2 * x)) ≠ 0 := by
    positivity
  field_simp
  ring

/-- `tanh x -> 1` as `x -> +∞`, proved from the exponential ratio. -/
theorem tendsto_tanh_atTop_one :
    Tendsto Real.tanh atTop (nhds 1) := by
  rw [tendsto_congr tanh_eq_exp_ratio]
  have h2x : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Tendsto.const_mul_atTop two_pos tendsto_id
  have he : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h2x
  have hnum : Tendsto (fun x : ℝ => 1 - Real.exp (-(2 * x))) atTop (nhds 1) := by
    have h := tendsto_const_nhds.sub he
    simpa only [sub_zero] using h
  have hden : Tendsto (fun x : ℝ => 1 + Real.exp (-(2 * x))) atTop (nhds 1) := by
    have h := tendsto_const_nhds.add he
    simpa only [add_zero] using h
  have h := hnum.div hden one_ne_zero
  simpa using h

/-- The antiderivative tends to `8/15` at `+∞`. -/
theorem tendsto_sechSixthAntideriv :
    Tendsto sechSixthAntideriv atTop (nhds (8/15 : ℝ)) := by
  have ht := tendsto_tanh_atTop_one
  have h3 := (ht.pow 3).const_mul (2/3 : ℝ)
  have h5 := (ht.pow 5).const_mul (1/5 : ℝ)
  have h := ht.sub h3 |>.add h5
  convert h using 1 <;> norm_num [sechSixthAntideriv]

@[simp] theorem sechSixthAntideriv_zero : sechSixthAntideriv 0 = 0 := by
  simp [sechSixthAntideriv]

/-- **Exact spectral integral:** `∫_0^∞ sech^6 x dx = 8/15`. -/
theorem integral_Ioi_one_div_cosh_sixth :
    ∫ x in Set.Ioi (0 : ℝ), 1 / Real.cosh x ^ 6 = (8/15 : ℝ) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((hasDerivAt_sechSixthAntideriv 0).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_sechSixthAntideriv x)
    (fun x _ => by positivity)
    tendsto_sechSixthAntideriv
  simpa using h

end GppSechIntegral

#print axioms GppSechIntegral.integral_Ioi_one_div_cosh_sixth
