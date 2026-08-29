import GppVerify.RiemannHypothesis.EulerFactorLogDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Local Euler factor on the arithmetic principal series

This closes the local bridge left open in `EulerFactorLogDeriv.lean`:

  W_p(t) = 2 Re(-zeta_p'/zeta_p(1/2 + i t)).

The proof is entirely local.  Writing `r = p^(-1/2)` and `theta = t log p`, the centered
Euler phase is `r (cos theta - i sin theta)` and both sides reduce to

  2 log(p) (r cos(theta) - r^2) / (1 - 2 r cos(theta) + r^2).

No explicit formula, zero statement, or RH input is used.
-/

namespace GppCutkoskyWeil

open Complex Real

/-- The centered local Euler phase at `s = 1/2 + i t`. -/
noncomputable def centeredEulerPhase (p t : ℝ) : ℂ :=
  Complex.exp (-(((1 : ℂ) / 2) + Complex.I * (t : ℂ)) * Complex.log (p : ℂ))

/-- Real part of the centered Euler phase. -/
theorem centeredEulerPhase_re {p : ℝ} (hp : 0 < p) (t : ℝ) :
    (centeredEulerPhase p t).re =
      p ^ (-(1 : ℝ) / 2) * Real.cos (t * Real.log p) := by
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) :=
    (Complex.ofReal_log hp.le).symm
  have hre :
      (-(((1 : ℂ) / 2) + Complex.I * (t : ℂ)) * Complex.log (p : ℂ))).re =
        -(Real.log p) / 2 := by
    rw [hlog]
    simp
    ring
  have him :
      (-(((1 : ℂ) / 2) + Complex.I * (t : ℂ)) * Complex.log (p : ℂ))).im =
        -(t * Real.log p) := by
    rw [hlog]
    simp
    ring
  unfold centeredEulerPhase
  rw [Complex.exp_re, hre, him, Real.cos_neg]
  rw [Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- Imaginary part of the centered Euler phase. -/
theorem centeredEulerPhase_im {p : ℝ} (hp : 0 < p) (t : ℝ) :
    (centeredEulerPhase p t).im =
      -(p ^ (-(1 : ℝ) / 2) * Real.sin (t * Real.log p)) := by
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) :=
    (Complex.ofReal_log hp.le).symm
  have hre :
      (-(((1 : ℂ) / 2) + Complex.I * (t : ℂ)) * Complex.log (p : ℂ))).re =
        -(Real.log p) / 2 := by
    rw [hlog]
    simp
    ring
  have him :
      (-(((1 : ℂ) / 2) + Complex.I * (t : ℂ)) * Complex.log (p : ℂ))).im =
        -(t * Real.log p) := by
    rw [hlog]
    simp
    ring
  unfold centeredEulerPhase
  rw [Complex.exp_im, hre, him, Real.sin_neg]
  rw [Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- The centered local phase has the expected Poisson denominator norm square. -/
theorem one_sub_centeredEulerPhase_normSq {p : ℝ} (hp : 0 < p) (t : ℝ) :
    Complex.normSq (1 - centeredEulerPhase p t) =
      1 - 2 * p ^ (-(1 : ℝ) / 2) * Real.cos (t * Real.log p) + p⁻¹ := by
  let r : ℝ := p ^ (-(1 : ℝ) / 2)
  let θ : ℝ := t * Real.log p
  have hzre : (centeredEulerPhase p t).re = r * Real.cos θ := by
    simpa [r, θ] using centeredEulerPhase_re hp t
  have hzim : (centeredEulerPhase p t).im = -(r * Real.sin θ) := by
    simpa [r, θ] using centeredEulerPhase_im hp t
  have hrsq : r ^ 2 = p⁻¹ := by
    dsimp [r]
    rw [← Real.rpow_natCast (p ^ (-(1:ℝ)/2)) 2, ← Real.rpow_mul hp.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [Complex.normSq_apply]
  simp [hzre, hzim]
  have htrig := Real.sin_sq_add_cos_sq θ
  nlinarith

/-- The actual local log derivative evaluated on the principal series has the Poisson-kernel
real part expected from the prime wave response. -/
theorem re_minusLogDerivZetaP_principal {p : ℝ} (hp : 1 < p) (t : ℝ) :
    (minusLogDerivZetaP p (((1 : ℂ) / 2) + Complex.I * (t : ℂ))).re =
      Real.log p *
        (p ^ (-(1 : ℝ) / 2) * Real.cos (t * Real.log p) - p⁻¹) /
        (1 - 2 * p ^ (-(1 : ℝ) / 2) * Real.cos (t * Real.log p) + p⁻¹) := by
  have hp0 : 0 < p := lt_trans one_pos hp
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) :=
    (Complex.ofReal_log hp0.le).symm
  have hz :
      Complex.exp (-((((1 : ℂ) / 2) + Complex.I * (t : ℂ)) * Complex.log (p : ℂ))) =
        centeredEulerPhase p t := by
    rfl
  have hzre := centeredEulerPhase_re hp0 t
  have hzim := centeredEulerPhase_im hp0 t
  have hnorm := one_sub_centeredEulerPhase_normSq hp0 t
  unfold minusLogDerivZetaP
  rw [hz, hlog, Complex.div_re]
  simp [hzre, hzim, hnorm]
  ring

/-- **Local particle-wave bridge.** The vacuum-subtracted finite-place kernel is exactly
`2 Re(-zeta_p'/zeta_p)` on the arithmetic principal series. -/
theorem Wp_eq_two_mul_re_minusLogDerivZetaP {p : ℝ} (hp : 1 < p) (t : ℝ) :
    Wp p t =
      2 * (minusLogDerivZetaP p (((1 : ℂ) / 2) + Complex.I * (t : ℂ))).re := by
  have hp0 : 0 < p := lt_trans one_pos hp
  have hsq : (p ^ (-(1 : ℝ) / 2)) ^ 2 = p⁻¹ := by
    rw [← Real.rpow_natCast (p ^ (-(1:ℝ)/2)) 2, ← Real.rpow_mul hp0.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [re_minusLogDerivZetaP_principal hp t]
  unfold Wp Kp
  rw [← hsq]
  have hden :
      1 - 2 * p ^ (-(1 : ℝ) / 2) * Real.cos (t * Real.log p) +
          (p ^ (-(1 : ℝ) / 2)) ^ 2 ≠ 0 := by
    have hk := Kp_pos hp t
    unfold Kp at hk
    by_contra hzero
    rw [← hsq, hzero] at hk
    simp at hk
  field_simp [hden]
  ring

end GppCutkoskyWeil

#print axioms GppCutkoskyWeil.centeredEulerPhase_re
#print axioms GppCutkoskyWeil.one_sub_centeredEulerPhase_normSq
#print axioms GppCutkoskyWeil.re_minusLogDerivZetaP_principal
#print axioms GppCutkoskyWeil.Wp_eq_two_mul_re_minusLogDerivZetaP
