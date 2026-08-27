import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import GppVerify.QuantumInformation.TransposeNotCompletelyPositive

/-!
# The Half-Flip Proposition: Antimatter as the Unitary Shadow of CPT
# Lean 4 | GPPVerify
# Author: Daniel Toupin | Golden Physics Project

Source: half_flip_proposition_v11.tex

## What is formalized here

Lemma 2.1 (antiunitary conjugation is unitary composed with transpose, on
Hermitian inputs): for A = U∘K antiunitary (U unitary, K entrywise complex
conjugation) and ρ a Hermitian density operator, A ρ A⁻¹ = U ρ̄ Uᴴ, where ρ̄
is the entrywise conjugate of ρ; since ρ is Hermitian, ρ̄ = ρᵀ, so this
equals U ρᵀ Uᴴ. The whole content reduces to the one fact that a Hermitian
matrix's entrywise conjugate is its transpose, proved below
(`hermitian_map_star_eq_transpose`), from which the displayed identity
(`antiunitary_conj_eq_unitary_transpose`) follows immediately.

Proposition 4.1(a) (Wigner time reversal is the universal spin inverter):
on ℂ², T(ψ₁,ψ₂) = (conj ψ₂, -conj ψ₁) is exactly i·σy·K. Proved: ⟨ψ,Tψ⟩ = 0
identically (`wignerT_orthogonal`), and T² = -1 (`wignerT_wignerT`).

Proposition 2.2 (No-Enactment), for `d = 2`, is now imported from the actual
Choi-matrix / complete-positivity development and exposed below as a substantive
theorem rather than the former `True` placeholder.

Proposition 4.1(c) (the depolarizing channel E(ρ) = (1/3)Σᵢ σᵢρσᵢ is CPTP
and achieves inversion fidelity exactly 2/3) still needs the Bloch-sphere
fidelity computation; that remains open rather than being promoted.
-/

namespace GppHalfFlip

open scoped ComplexConjugate

/-- A Hermitian matrix's entrywise complex conjugate equals its transpose:
    the algebraic fact underlying Lemma 2.1. -/
theorem hermitian_map_star_eq_transpose {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : Matrix d d ℂ) (hρ : ρ.IsHermitian) :
    ρ.map (starRingEnd ℂ) = ρ.transpose := by
  ext i j
  have h : Matrix.conjTranspose ρ j i = ρ j i := by rw [hρ]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def] at h
  simpa only [Matrix.map_apply, Matrix.transpose_apply] using h

/-- Lemma 2.1: antiunitary conjugation of a Hermitian density operator is
    unitary conjugation of its transpose. -/
theorem antiunitary_conj_eq_unitary_transpose {d : Type*} [Fintype d] [DecidableEq d]
    (U ρ : Matrix d d ℂ) (hρ : ρ.IsHermitian) :
    U * ρ.map (starRingEnd ℂ) * Matrix.conjTranspose U
      = U * ρ.transpose * Matrix.conjTranspose U := by
  rw [hermitian_map_star_eq_transpose ρ hρ]

/-- Wigner time reversal T = i σ_y K on ℂ², in components:
    T(ψ₁,ψ₂) = (conj ψ₂, -conj ψ₁). -/
def wignerT (ψ1 ψ2 : ℂ) : ℂ × ℂ := (conj ψ2, -conj ψ1)

/-- Proposition 4.1(a), part 1: ⟨ψ,Tψ⟩ = 0 identically -- T maps every
    state to one orthogonal to it. -/
theorem wignerT_orthogonal (ψ1 ψ2 : ℂ) :
    conj ψ1 * (wignerT ψ1 ψ2).1 + conj ψ2 * (wignerT ψ1 ψ2).2 = 0 := by
  simp only [wignerT]
  ring

/-- Proposition 4.1(a), part 2: T² = -1. -/
theorem wignerT_wignerT (ψ1 ψ2 : ℂ) :
    wignerT (wignerT ψ1 ψ2).1 (wignerT ψ1 ψ2).2 = (-ψ1, -ψ2) := by
  simp only [wignerT, map_neg, ← RCLike.star_def, star_star]

/-- **Proposition 2.2 (No-Enactment), d = 2.**  The transpose map on
`M₂(ℂ)` is not completely positive.  This is the operational obstruction behind
trying to enact an antiunitary/transpose operation as a quantum channel. -/
theorem no_enactment :
    ¬ GppChoiMatrix.CompletelyPositive GppHalfFlipMatrix.transposeMap :=
  GppHalfFlipMatrix.transposeMap_not_completelyPositive

/-- Proposition 4.1(c): the channel E(ρ) = (1/3)Σᵢ σᵢρσᵢ is completely
    positive and trace preserving, and achieves inversion fidelity exactly
    2/3 uniformly on the Bloch sphere. Not formalized: needs the same
    complete-positivity notion together with a Bloch-sphere fidelity
    computation. Verified symbolically and on a 200-sample numerical
    ensemble in the companion script. -/
theorem universal_not_fidelity : True := trivial

end GppHalfFlip

#print axioms GppHalfFlip.no_enactment
