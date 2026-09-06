import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Majorana / orientation algebra: surviving exact layer

Historical provenance:
- `zitterbewegung_T_boundary_FINAL.tex`
- `twistor_googly_dtoupin_v81.tex`

Chronology correction (2026-09-01): those manuscripts attempted to derive a
chirality exchange from ordinary Wigner time reversal. That step is invalid:
under Wigner `T`, both spin and momentum reverse, so helicity is preserved.
Consequently the former `True := trivial` scaffolds asserting that a T-boundary
forces Majorana neutrinos, a massless lightest neutrino, an inverted hierarchy,
neutrino delocalisation, or mirror-baryon abundance have been removed rather
than retained as fake Mathlib gaps.

What survives here is finite-dimensional algebra plus the elementary Dirac
zitterbewegung phase periodicity. No theorem below identifies celestial shadow,
charge conjugation, parity, proper-time reversal, and Wigner time reversal.
-/

namespace GppMajorana

/-! ## Basic field identities -/

/-- The antisymmetric epsilon matrix `ε = [[0,1],[-1,0]]`.

The same 2x2 matrix occurs in several constructions, but equality of matrix
representatives does not identify the corresponding physical operations.
Charge conjugation, the Grassmannian chart map, and the matrix part of Wigner
`T` must retain their distinct conjugation/representation data. -/
def epsilon : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- Exact finite-dimensional identity `ε² = -I`. -/
theorem epsilon_sq : epsilon * epsilon = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true })
      [epsilon, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply]

/-- `ε` is invertible: `det ε = 1`. -/
theorem epsilon_det : epsilon.det = 1 := by
  simp [epsilon, Matrix.det_fin_two_of]

/-- Legacy theorem name for the matrix component only.
The full charge-conjugation operator includes conjugation and representation
structure not formalized by this statement. -/
theorem charge_conjugation_sq : epsilon * epsilon = -1 :=
  epsilon_sq

/-! ## Zitterbewegung arithmetic -/

/-- The standard free-Dirac zitterbewegung angular-frequency factor
`ω = 2m` is positive for positive mass in natural units. -/
theorem zitterbewegung_frequency (m : ℝ) (hm : 0 < m) : 2 * m > 0 := by
  linarith

/-- The corresponding period `π/m` is positive for positive mass. -/
theorem zitterbewegung_period (m : ℝ) (hm : 0 < m) :
    Real.pi / m > 0 := by
  positivity

/-- Exact phase return for the free-Dirac interference frequency:
`exp(i * 2m * (π/m)) = 1` for nonzero mass.

This proves only the elementary oscillatory identity. It does not identify the
negative-energy component with a cosmological mirror sector. -/
theorem T_boundary_oscillation_period (m : ℝ) (hm : m ≠ 0) :
    Complex.exp (((2 * m * (Real.pi / m) : ℝ) : ℂ) * Complex.I) = 1 := by
  have hphase : 2 * m * (Real.pi / m) = 2 * Real.pi := by
    field_simp [hm]
    ring
  rw [hphase]
  simpa using Complex.exp_two_pi_mul_I

/-! ## Summary -/

/-- Honest summary of the finite-dimensional algebra certified here. -/
theorem majorana_summary :
    epsilon * epsilon = -1 ∧ epsilon.det = 1 :=
  ⟨epsilon_sq, epsilon_det⟩

end GppMajorana
