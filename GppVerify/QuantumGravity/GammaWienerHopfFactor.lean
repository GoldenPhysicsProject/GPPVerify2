import GppVerify.QuantumGravity.GammaHalfModulusIdentity
import Mathlib.Tactic

/-!
# Normalized Gamma Wiener--Hopf factor on the real spectral axis

Define the two normalized half-Gamma factors

  Hplus(k)  = Gamma(1/2 - i k/(2*pi))^2 / pi,
  Hminus(k) = Gamma(1/2 + i k/(2*pi))^2 / pi.

The previously formalized half-shift reflection identity implies exactly

  Hplus(k) Hminus(k) = sech(k/2)^2.

This file proves the real-axis factorization and its integer-power semigroup.  It does
not claim the half-plane holomorphy/outer-function part of Wiener--Hopf theory; that is a
separate complex-analysis layer.
-/

namespace GppGammaWienerHopf

open Complex

/-- Upper-half-plane candidate factor, restricted here to real spectral parameter `k`. -/
noncomputable def Hplus (k : ℝ) : ℂ :=
  Complex.Gamma (((1 : ℂ) / 2) -
      (((k / (2 * Real.pi) : ℝ) : ℂ) * I)) ^ 2 / (Real.pi : ℂ)

/-- Lower-half-plane candidate factor, restricted here to real spectral parameter `k`. -/
noncomputable def Hminus (k : ℝ) : ℂ :=
  Complex.Gamma (((1 : ℂ) / 2) +
      (((k / (2 * Real.pi) : ℝ) : ℂ) * I)) ^ 2 / (Real.pi : ℂ)

/-- **Exact normalized Gamma factorization** of the `sech^2` spectral multiplier. -/
theorem Hplus_mul_Hminus (k : ℝ) :
    Hplus k * Hminus k =
      ((1 / (Real.cosh (k / 2)) ^ 2 : ℝ) : ℂ) := by
  have href := GppGammaHalfModulus.gamma_half_add_mul_gamma_half_sub
    (k / (2 * Real.pi))
  have hscale : Real.pi * (k / (2 * Real.pi)) = k / 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hscale] at href
  calc
    Hplus k * Hminus k =
        (Complex.Gamma (((1 : ℂ) / 2) +
            (((k / (2 * Real.pi) : ℝ) : ℂ) * I)) *
          Complex.Gamma (((1 : ℂ) / 2) -
            (((k / (2 * Real.pi) : ℝ) : ℂ) * I))) ^ 2 /
          (Real.pi : ℂ) ^ 2 := by
            unfold Hplus Hminus
            ring
    _ = ((((Real.pi / Real.cosh (k / 2) : ℝ) : ℂ) ^ 2) /
          (Real.pi : ℂ) ^ 2) := by rw [href]
    _ = ((1 / (Real.cosh (k / 2)) ^ 2 : ℝ) : ℂ) := by
      have hcosh : Real.cosh (k / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
      push_cast
      field_simp [Real.pi_ne_zero, hcosh]

/-- Every integer chamber inherits the same factorization multiplicatively. -/
theorem Hplus_pow_mul_Hminus_pow (m : ℕ) (k : ℝ) :
    Hplus k ^ m * Hminus k ^ m =
      (((1 / (Real.cosh (k / 2)) ^ 2 : ℝ) : ℂ) ^ m) := by
  rw [← mul_pow, Hplus_mul_Hminus]

end GppGammaWienerHopf

#print axioms GppGammaWienerHopf.Hplus_mul_Hminus
#print axioms GppGammaWienerHopf.Hplus_pow_mul_Hminus_pow
