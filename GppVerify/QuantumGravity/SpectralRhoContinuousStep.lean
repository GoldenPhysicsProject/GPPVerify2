import GppVerify.QuantumGravity.SpectralRhoRecurrence

/-!
# Continuous Gamma-chamber step factor

Formal algebraic spine for the arbitrary-real chamber recurrence discovered in
GPPDiscovery2.  If

  ρ_c(x) = 2^(2c-1)/(π Γ(2c)) |Γ(c+ix)|²,

then the Gamma functional equation gives

  ρ_(c+1)(x) = F(c,x) ρ_c(x),
  F(c,x) = 2(c²+x²)/(c(2c+1)).

This module certifies the exact real step-factor algebra and its crossing threshold.
The analytic identification with the normalized continuous Gamma density is kept as a
separate theorem obligation.
-/

namespace GppSpectralRhoContinuousStep

/-- Real-parameter step factor for the continuous Gamma chamber. -/
noncomputable def continuousStepFactor (c x : ℝ) : ℝ :=
  2 * (c ^ 2 + x ^ 2) / (c * (2 * c + 1))

/-- The real continuous step factor is strictly positive on the physical chamber `c>0`. -/
theorem continuousStepFactor_pos
    (c x : ℝ) (hc : 0 < c) :
    0 < continuousStepFactor c x := by
  unfold continuousStepFactor
  positivity

/-- At the integer chamber `c=k+1`, the continuous step is exactly the previously
certified discrete Gamma-density step factor. -/
theorem continuousStepFactor_nat_succ
    (k : ℕ) (x : ℝ) :
    continuousStepFactor ((k : ℝ) + 1) x = GppSpectralRho.rhoStepFactor k x := by
  unfold continuousStepFactor GppSpectralRho.rhoStepFactor
  ring

/-- The step-factor defect from one has numerator exactly `2*x^2-c`. -/
theorem continuousStepFactor_sub_one
    (c x : ℝ) (hc : 0 < c) :
    continuousStepFactor c x - 1 =
      (2 * x ^ 2 - c) / (c * (2 * c + 1)) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlin : 2 * c + 1 ≠ 0 := by nlinarith
  unfold continuousStepFactor
  field_simp [hc0, hlin]
  ring

/-- The continuous chamber crosses unit step factor exactly at `2*x^2=c`. -/
theorem continuousStepFactor_eq_one_iff
    (c x : ℝ) (hc : 0 < c) :
    continuousStepFactor c x = 1 ↔ 2 * x ^ 2 = c := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlin : 2 * c + 1 ≠ 0 := by nlinarith
  constructor
  · intro h
    unfold continuousStepFactor at h
    field_simp [hc0, hlin] at h
    nlinarith
  · intro h
    unfold continuousStepFactor
    field_simp [hc0, hlin]
    nlinarith

/-- Above the crossing threshold the continuous chamber step factor is greater than one. -/
theorem continuousStepFactor_gt_one_iff
    (c x : ℝ) (hc : 0 < c) :
    1 < continuousStepFactor c x ↔ c < 2 * x ^ 2 := by
  have hden : 0 < c * (2 * c + 1) := by positivity
  unfold continuousStepFactor
  constructor
  · intro h
    have h' : c * (2 * c + 1) < 2 * (c ^ 2 + x ^ 2) := by
      simpa using (lt_div_iff₀ hden).mp h
    nlinarith
  · intro h
    apply (lt_div_iff₀ hden).mpr
    nlinarith

/-- Below the crossing threshold the continuous chamber step factor is less than one. -/
theorem continuousStepFactor_lt_one_iff
    (c x : ℝ) (hc : 0 < c) :
    continuousStepFactor c x < 1 ↔ 2 * x ^ 2 < c := by
  have hden : 0 < c * (2 * c + 1) := by positivity
  unfold continuousStepFactor
  constructor
  · intro h
    have h' : 2 * (c ^ 2 + x ^ 2) < 1 * (c * (2 * c + 1)) :=
      (div_lt_iff₀ hden).mp h
    nlinarith
  · intro h
    apply (div_lt_iff₀ hden).mpr
    nlinarith

/-- Exact algebraic transport identity induced by one continuous chamber step.

When `e = E_c[f]` and `ex2 = E_c[X² f]`, the left-hand side is the chamber
increment obtained from the Gamma recurrence.  If additionally `E_c[X²]=c/2`,
the right-hand bracket is exactly `Cov_c(f,X²)`. -/
theorem continuousStep_transport_identity
    (c e ex2 : ℝ) (hc : 0 < c) :
    2 * (c ^ 2 * e + ex2) / (c * (2 * c + 1)) - e =
      2 / (c * (2 * c + 1)) * (ex2 - (c / 2) * e) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlin : 2 * c + 1 ≠ 0 := by nlinarith
  field_simp [hc0, hlin]
  ring

/-- Rearranged all-moment step relation.  Analytically, setting
`e=M_{2m}(c)`, `enext=M_{2m}(c+1)`, and `ex2=M_{2m+2}(c)` gives the exact
even-moment recurrence. -/
theorem continuousStep_moment_rearrange
    (c e enext ex2 : ℝ) (hc : 0 < c)
    (hstep : enext = 2 * (c ^ 2 * e + ex2) / (c * (2 * c + 1))) :
    ex2 = c * (2 * c + 1) / 2 * enext - c ^ 2 * e := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlin : 2 * c + 1 ≠ 0 := by nlinarith
  rw [hstep]
  field_simp [hc0, hlin]
  ring

/-- Normalization of two consecutive chambers forces the second moment `c/2` from
the step recurrence alone. -/
theorem continuousStep_normalization_forces_second_moment
    (c m2 : ℝ) (hc : 0 < c)
    (hstep : (1 : ℝ) = 2 * (c ^ 2 + m2) / (c * (2 * c + 1))) :
    m2 = c / 2 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hlin : 2 * c + 1 ≠ 0 := by nlinarith
  field_simp [hc0, hlin] at hstep
  nlinarith

/-- A nonnegative covariance bracket forces monotone chamber transport.  This is the
algebraic core of radial stochastic ordering; the analytic layer only has to prove
that the relevant covariance bracket is nonnegative. -/
theorem continuousStep_transport_mono
    (c e ex2 : ℝ) (hc : 0 < c)
    (hcov : 0 ≤ ex2 - (c / 2) * e) :
    e ≤ 2 * (c ^ 2 * e + ex2) / (c * (2 * c + 1)) := by
  have hcoef : 0 < 2 / (c * (2 * c + 1)) := by positivity
  have hrhs : 0 ≤ 2 / (c * (2 * c + 1)) * (ex2 - (c / 2) * e) :=
    mul_nonneg (le_of_lt hcoef) hcov
  have hid := continuousStep_transport_identity c e ex2 hc
  linarith

end GppSpectralRhoContinuousStep
