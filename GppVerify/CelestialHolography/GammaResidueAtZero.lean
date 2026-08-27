import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-!
# Gamma simple-pole residue at zero

Mathlib defines `Gamma 0 = 0` by convention, so the mathematically meaningful
statement at the pole is a punctured-neighborhood limit.  Euler's recurrence

  Gamma(eps + 1) = eps * Gamma(eps)

turns the residue limit into ordinary continuity of Gamma at `1`.
-/

namespace GppGammaResidueAtZero

open Filter Set

/-- Real Gamma is continuous at `1`, obtained by restricting the complex Gamma
function, which is differentiable away from its poles. -/
theorem continuousAt_realGamma_one : ContinuousAt Real.Gamma 1 := by
  have hpoles : ∀ m : ℕ, (1 : ℂ) ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hc : ContinuousAt Complex.Gamma (1 : ℂ) :=
    (Complex.differentiableAt_Gamma (1 : ℂ) hpoles).continuousAt
  unfold Real.Gamma
  have hcomp : ContinuousAt (fun x : ℝ => Complex.Gamma (x : ℂ)) 1 :=
    hc.comp_of_eq continuous_ofReal.continuousAt (by norm_num)
  exact Complex.continuous_re.continuousAt.comp 1 hcomp

/-- **Gamma residue at the origin.** In the punctured real neighborhood of zero,
`eps * Gamma(eps)` tends to `1`.  This is exactly the residue input used by the
raised-dimensional box factorization. -/
theorem tendsto_mul_realGamma_zero :
    Tendsto (fun ε : ℝ => ε * Real.Gamma ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hshift :
      Tendsto (fun ε : ℝ => Real.Gamma (ε + 1))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hadd : Tendsto (fun ε : ℝ => ε + 1)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds
        (continuousAt_id.add continuousAt_const)
    simpa using continuousAt_realGamma_one.tendsto.comp hadd
  apply hshift.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := by simpa using hε
  exact (Real.Gamma_add_one hε0).symm

end GppGammaResidueAtZero

#print axioms GppGammaResidueAtZero.continuousAt_realGamma_one
#print axioms GppGammaResidueAtZero.tendsto_mul_realGamma_zero
