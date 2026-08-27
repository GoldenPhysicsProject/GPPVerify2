import GppVerify.RiemannHypothesis.WeilPositivityCriterion
import Mathlib.Tactic

/-!
# Finite interpolation bridge to the Weil paired-form criterion

The finite Weil form on a set `S` only samples a coefficient function at points of
`S` and their involutive partners.  Consequently one does not need global
surjectivity of an explicit-formula transform onto all functions on the zero set.
It is enough that the test-transform class interpolate arbitrary data on each
finite set `S ∪ iota(S)`.

This file formalizes that exact reduction.  It deliberately does not assert that
any particular Schwartz/Mellin/Paley--Wiener test class has the required finite
interpolation property; proving that analytic statement is the genuine remaining
bridge.
-/

namespace GppWeilInterpolationBridge

open Finset
open GppWeilCriterion

/-- Agreement on `S` and `iota(S)` is enough to preserve the paired form on `S`. -/
theorem pairedForm_eq_of_agree_on_pairSupport
    {ι : ℂ → ℂ} {S : Finset ℂ} {c d : ℂ → ℂ}
    (hS : ∀ ρ ∈ S, d ρ = c ρ)
    (hiS : ∀ ρ ∈ S, d (ι ρ) = c (ι ρ)) :
    pairedForm ι S d = pairedForm ι S c := by
  unfold pairedForm
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [hS ρ hρ, hiS ρ hρ]

/-- Abstract finite interpolation principle: positivity for all coefficient functions
coming from a test-transform class implies positivity of the full finite paired form,
provided those transforms can interpolate arbitrary coefficient data on every finite
pair-support. -/
theorem pairedForm_nonneg_of_finite_interpolation
    {T : Type*} {ι : ℂ → ℂ} {Z : Set ℂ}
    (coeff : T → ℂ → ℂ)
    (htestPos : ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ f : T,
      0 ≤ (pairedForm ι S (coeff f)).re)
    (hinterp : ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ c : ℂ → ℂ,
      ∃ f : T,
        (∀ ρ ∈ S, coeff f ρ = c ρ) ∧
        (∀ ρ ∈ S, coeff f (ι ρ) = c (ι ρ))) :
    ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ c : ℂ → ℂ,
      0 ≤ (pairedForm ι S c).re := by
  intro S hSZ c
  obtain ⟨f, hS, hiS⟩ := hinterp S hSZ c
  have heq : pairedForm ι S (coeff f) = pairedForm ι S c :=
    pairedForm_eq_of_agree_on_pairSupport hS hiS
  rw [← heq]
  exact htestPos S hSZ f

/-- **Explicit interpolation-to-RH reduction.** If a test-transform class is positive
for the zeta paired form and has finite interpolation on every finite subset of the
nontrivial zero set together with its shadow partners, then RH follows by the already
proved finite Weil criterion.

This theorem is a reduction, not an RH proof: the two analytic hypotheses below are
exactly what an explicit-formula/Wiener--Hopf construction must discharge. -/
theorem rh_of_testPos_finiteInterpolation
    {T : Type*} (coeff : T → ℂ → ℂ)
    (htestPos : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ f : T,
      0 ≤ (pairedForm zetaInvolution S (coeff f)).re)
    (hinterp : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ c : ℂ → ℂ,
      ∃ f : T,
        (∀ ρ ∈ S, coeff f ρ = c ρ) ∧
        (∀ ρ ∈ S, coeff f (zetaInvolution ρ) = c (zetaInvolution ρ))) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := by
  apply rh_iff_weil_pairedForm_nonneg.mpr
  exact pairedForm_nonneg_of_finite_interpolation coeff htestPos hinterp

end GppWeilInterpolationBridge

#print axioms GppWeilInterpolationBridge.pairedForm_eq_of_agree_on_pairSupport
#print axioms GppWeilInterpolationBridge.pairedForm_nonneg_of_finite_interpolation
#print axioms GppWeilInterpolationBridge.rh_of_testPos_finiteInterpolation
