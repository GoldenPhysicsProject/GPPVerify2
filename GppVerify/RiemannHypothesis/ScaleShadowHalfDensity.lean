import GppVerify.RiemannHypothesis.ScaleMassDiagnostic
import Mathlib.Tactic

/-!
# Shadow symmetry of the half-density dilation character

For

  chi_s(a) = exp(log(a) * (s - 1/2)),

the shadow involution `s -> 1-s` negates the centered exponent. Hence it sends the
multiplicative dilation character to its reciprocal. Together with
`GppScaleMass.critical_line_iff_dilation_unitary`, this is the exact algebraic skeleton
behind the principal-series statement: on the unitary locus the shadow is the inverse
character, and therefore the Hermitian conjugate character.

No zeta-zero statement is used or implied.
-/

namespace GppScaleShadow

open Complex
open GppScaleMass

/-- Project celestial dictionary from the Mellin coordinate to scalar dimension. -/
noncomputable def celestialDelta (s : ℂ) : ℂ := 2 * s

/-- Shadow negates the half-density-centered exponent. -/
lemma shadow_centered_exponent (s : ℂ) :
    (1 - s) - (1 / 2 : ℂ) = -(s - (1 / 2 : ℂ)) := by
  ring

/-- The project dictionary `Delta = 2s` exactly intertwines the Riemann reflection
`s -> 1-s` with the scalar celestial shadow `Delta -> 2-Delta`. -/
theorem celestialDelta_shadow (s : ℂ) :
    celestialDelta (1 - s) = 2 - celestialDelta s := by
  unfold celestialDelta
  ring

/-- The Riemann critical line maps exactly to the scalar celestial principal line
`Re Delta = 1`. -/
theorem celestialDelta_re_eq_one_iff (s : ℂ) :
    (celestialDelta s).re = 1 ↔ s.re = 1 / 2 := by
  unfold celestialDelta
  simp only [map_mul, Complex.ofReal_ofNat_re]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

/-- On the critical line, celestial shadow is complex conjugation after `Delta=2s`. -/
theorem celestialDelta_shadow_eq_conj {s : ℂ} (hs : s.re = 1 / 2) :
    2 - celestialDelta s = (starRingEnd ℂ) (celestialDelta s) := by
  apply Complex.ext
  · simp [celestialDelta, hs]
    norm_num
  · simp [celestialDelta]

/-- The shadow character is exactly the reciprocal dilation character. -/
theorem dilationCharacter_shadow_eq_inv (s : ℂ) (a : ℝ) :
    dilationCharacter (1 - s) a = (dilationCharacter s a)⁻¹ := by
  unfold dilationCharacter
  rw [shadow_centered_exponent]
  rw [mul_neg, Complex.exp_neg]

/-- Applying shadow twice returns the original character. -/
theorem dilationCharacter_shadow_involution (s : ℂ) (a : ℝ) :
    dilationCharacter (1 - (1 - s)) a = dilationCharacter s a := by
  ring_nf

/-- On the critical line, complex conjugation of the spectral parameter is exactly
shadow: `star s = 1 - s`. -/
theorem conj_eq_shadow_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    (starRingEnd ℂ) s = 1 - s := by
  apply Complex.ext
  · simp [hs]
    norm_num
  · simp

/-- **Critical-line Hermitian shadow law.**  On `Re s = 1/2`, shadow is not merely
reciprocal: it is literally complex conjugation of the half-density character. -/
theorem dilationCharacter_shadow_eq_conj {s : ℂ} (hs : s.re = 1 / 2) (a : ℝ) :
    dilationCharacter (1 - s) a = (starRingEnd ℂ) (dilationCharacter s a) := by
  unfold dilationCharacter
  rw [← Complex.exp_conj]
  congr 1
  have hsconj := conj_eq_shadow_of_re_eq_half hs
  have hstarlog :
      (starRingEnd ℂ) ((Real.log a : ℝ) : ℂ) = ((Real.log a : ℝ) : ℂ) := by
    simp
  have hstarhalf :
      (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    apply Complex.ext <;> norm_num
  have hstarshift :
      (starRingEnd ℂ) (s - (1 / 2 : ℂ)) =
        (1 - s) - (1 / 2 : ℂ) := by
    calc
      (starRingEnd ℂ) (s - (1 / 2 : ℂ)) =
          (starRingEnd ℂ) s - (starRingEnd ℂ) (1 / 2 : ℂ) := by
            exact map_sub (starRingEnd ℂ) s (1 / 2 : ℂ)
      _ = (1 - s) - (1 / 2 : ℂ) := by rw [hsconj, hstarhalf]
  rw [map_mul, hstarlog, hstarshift]

/-- At a nontrivial positive scale, the critical line is exactly the locus on which
    the character is unitary; on that same locus shadow acts by inversion. -/
theorem critical_line_iff_unitary_with_shadow {s : ℂ} {a : ℝ}
    (ha : 0 < a) (ha1 : a ≠ 1) :
    s.re = 1 / 2 ↔
      (‖dilationCharacter s a‖ = 1 ∧
       dilationCharacter (1 - s) a = (dilationCharacter s a)⁻¹) := by
  constructor
  · intro hs
    exact ⟨GppScaleMass.critical_line_dilation_unitary hs a,
      dilationCharacter_shadow_eq_inv s a⟩
  · intro h
    exact GppScaleMass.critical_line_of_dilation_unitary ha ha1 h.1

end GppScaleShadow

#print axioms GppScaleShadow.celestialDelta_shadow
#print axioms GppScaleShadow.celestialDelta_re_eq_one_iff
#print axioms GppScaleShadow.celestialDelta_shadow_eq_conj
#print axioms GppScaleShadow.dilationCharacter_shadow_eq_inv
#print axioms GppScaleShadow.dilationCharacter_shadow_involution
#print axioms GppScaleShadow.conj_eq_shadow_of_re_eq_half
#print axioms GppScaleShadow.dilationCharacter_shadow_eq_conj
#print axioms GppScaleShadow.critical_line_iff_unitary_with_shadow
