import GppVerify.CelestialHolography.HolographicChain
import Mathlib.Tactic

/-!
# Antiunitary googly exchange on ∧²ℂ⁴

The Hodge-star decomposition in `HolographicChain` already gives explicit self-dual
and anti-self-dual sectors.  Complex conjugation alone preserves those sectors because
the chosen Hodge-star matrix is real.  The helicity/googly exchange therefore also
requires orientation reversal.  The map below combines complex conjugation with an
orientation sign flip and hence anti-commutes with the Hodge star.

This is the finite-dimensional algebraic core needed before identifying the same
operation with celestial shadow/time reversal.  No claim about the full nonlinear
Penrose-Ward correspondence is made here.
-/

namespace GppGooglyAntiunitaryExchange

open GppHolographicChain

/-- Explicit orientation-reversing anti-linear exchange on the ordered basis
`(e12,e13,e14,e23,e24,e34)` of `∧²ℂ⁴`.  The first three coordinates are conjugated;
the last three are conjugated and sign-reversed. -/
def googlyExchange (v : Fin 6 → ℂ) : Fin 6 → ℂ
  | 0 => Complex.conj (v 0)
  | 1 => Complex.conj (v 1)
  | 2 => Complex.conj (v 2)
  | 3 => -Complex.conj (v 3)
  | 4 => -Complex.conj (v 4)
  | 5 => -Complex.conj (v 5)

/-- The googly exchange is an involution. -/
theorem googlyExchange_involutive (v : Fin 6 → ℂ) :
    googlyExchange (googlyExchange v) = v := by
  ext i
  fin_cases i <;> simp [googlyExchange]

/-- The googly exchange preserves the coordinatewise Hermitian norm density. -/
theorem googlyExchange_normSq (v : Fin 6 → ℂ) (i : Fin 6) :
    Complex.normSq (googlyExchange v i) = Complex.normSq (v i) := by
  fin_cases i <;> simp [googlyExchange, Complex.normSq_conj]

/-- The key googly relation: orientation-reversing conjugation anti-commutes with
Hodge star.  Consequently it exchanges the `+1` and `-1` Hodge eigenspaces. -/
theorem hodgeStar_googlyExchange_anticommute (v : Fin 6 → ℂ) :
    hodgeStar.mulVec (googlyExchange v) =
      (-1 : ℂ) • googlyExchange (hodgeStar.mulVec v) := by
  ext i
  fin_cases i <;>
    simp (config := { decide := true })
      [hodgeStar, googlyExchange, Matrix.mulVec, dotProduct,
       Fin.sum_univ_six, Pi.smul_apply]

/-- Every self-dual mode is sent to an anti-self-dual mode. -/
theorem googlyExchange_selfDual_to_antiSelfDual
    {v : Fin 6 → ℂ} (hv : hodgeStar.mulVec v = v) :
    hodgeStar.mulVec (googlyExchange v) =
      (-1 : ℂ) • googlyExchange v := by
  rw [hodgeStar_googlyExchange_anticommute, hv]

/-- Every anti-self-dual mode is sent back to a self-dual mode. -/
theorem googlyExchange_antiSelfDual_to_selfDual
    {v : Fin 6 → ℂ} (hv : hodgeStar.mulVec v = (-1 : ℂ) • v) :
    hodgeStar.mulVec (googlyExchange v) = googlyExchange v := by
  rw [hodgeStar_googlyExchange_anticommute, hv]
  ext i
  fin_cases i <;> simp [googlyExchange]

end GppGooglyAntiunitaryExchange

#print axioms GppGooglyAntiunitaryExchange.googlyExchange_involutive
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_normSq
#print axioms GppGooglyAntiunitaryExchange.hodgeStar_googlyExchange_anticommute
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_selfDual_to_antiSelfDual
#print axioms GppGooglyAntiunitaryExchange.googlyExchange_antiSelfDual_to_selfDual
