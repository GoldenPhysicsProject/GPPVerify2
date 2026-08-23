import GppVerify.RiemannHypothesis.PrimeFermionDirac
import GppVerify.StandardModel.ThreeGenerations
import Mathlib.Tactic

/-!
# Cayley--Dickson / finite-prime Fock dimension bridge

The finite-prime fermionic construction and the Cayley--Dickson tower share one exact
structural operation: adjoining one new binary generator doubles the dimension.

For `n` fermionic prime channels, the exterior/Fock state count is `2^n`.  The
Cayley--Dickson vector-space dimension after `n` doublings is also `2^n`.  Hence their
dimension recursions agree exactly:

`1 -> 2 -> 4 -> 8 -> ...`.

This file formalizes that dimension-level bridge and a finite-prime Hodge energy.  It does
NOT identify the multiplication law of a Cayley--Dickson algebra with the exterior/CAR
algebra.  Those are different algebraic structures; what is established here is the exact
common doubling skeleton.
-/

namespace GppCayleyFock

open Complex

/-- Number of basis states in the fermionic Fock space of `n` binary prime channels. -/
def fockDim (n : ℕ) : ℕ := 2 ^ n

/-- Real vector-space dimension after `n` Cayley--Dickson doublings. -/
def cayleyDicksonDim (n : ℕ) : ℕ := GppSM.cdDim n

/-- The two constructions have exactly the same dimension sequence. -/
theorem fockDim_eq_cayleyDicksonDim (n : ℕ) :
    fockDim n = cayleyDicksonDim n := by
  rfl

/-- Adding one fermionic channel doubles the Fock dimension. -/
theorem fockDim_succ (n : ℕ) : fockDim (n + 1) = 2 * fockDim n := by
  simp [fockDim, pow_succ]

/-- One Cayley--Dickson step doubles the vector-space dimension. -/
theorem cayleyDicksonDim_succ (n : ℕ) :
    cayleyDicksonDim (n + 1) = 2 * cayleyDicksonDim n := by
  simp [cayleyDicksonDim, GppSM.cdDim, pow_succ]

/-- The first four common dimensions are exactly `1,2,4,8`. -/
theorem first_four_common_dimensions :
    (fockDim 0, fockDim 1, fockDim 2, fockDim 3) = (1, 2, 4, 8) := by
  norm_num [fockDim]

/-- Three binary fermionic channels have eight Fock basis states, matching the octonionic
Cayley--Dickson stage at the level of real dimension. -/
theorem three_channel_dimension :
    fockDim 3 = 8 ∧ cayleyDicksonDim 3 = 8 := by
  norm_num [fockDim, cayleyDicksonDim, GppSM.cdDim]

/-- A finite family of local Euler holonomies has the canonical nonnegative Hodge energy,
the sum of the one-prime Dirac-square coefficients. -/
noncomputable def finiteHodgeEnergy {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∑ i, Complex.normSq (z i)

/-- Finite multi-prime Hodge energy is nonnegative term by term. -/
theorem finiteHodgeEnergy_nonneg {n : ℕ} (z : Fin n → ℂ) :
    0 ≤ finiteHodgeEnergy z := by
  unfold finiteHodgeEnergy
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (z i)

/-- For a concrete finite prime family, the Hodge energy is obtained by substituting the
actual Euler holonomies `1 - exp(-s log p)` into the same positive sum. -/
noncomputable def finitePrimeHodgeEnergy {n : ℕ} (p : Fin n → ℝ) (s : ℂ) : ℝ :=
  finiteHodgeEnergy (fun i => GppPrimeFermion.eulerHolonomy (p i) s)

/-- The finite-prime Hodge energy is nonnegative for every complex spectral parameter. -/
theorem finitePrimeHodgeEnergy_nonneg {n : ℕ} (p : Fin n → ℝ) (s : ℂ) :
    0 ≤ finitePrimeHodgeEnergy p s := by
  exact finiteHodgeEnergy_nonneg _

end GppCayleyFock

#check @GppCayleyFock.fockDim_eq_cayleyDicksonDim
#check @GppCayleyFock.fockDim_succ
#check @GppCayleyFock.first_four_common_dimensions
#check @GppCayleyFock.finiteHodgeEnergy_nonneg
#check @GppCayleyFock.finitePrimeHodgeEnergy_nonneg
