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
  rw [← sub_pos]
  rw [continuousStepFactor_sub_one c x hc]
  have hden : 0 < c * (2 * c + 1) := by positivity
  rw [div_pos_iff_of_pos_right hden]
  nlinarith

/-- Below the crossing threshold the continuous chamber step factor is less than one. -/
theorem continuousStepFactor_lt_one_iff
    (c x : ℝ) (hc : 0 < c) :
    continuousStepFactor c x < 1 ↔ 2 * x ^ 2 < c := by
  rw [← sub_neg]
  rw [continuousStepFactor_sub_one c x hc]
  have hden : 0 < c * (2 * c + 1) := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith

end GppSpectralRhoContinuousStep