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
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    simp only [Complex.one_re, map_neg, Complex.natCast_re] at hre
    linarith
  have hc : Tendsto Complex.Gamma (nhds (1 : ℂ)) (nhds (1 : ℂ)) := by
    simpa using (Complex.differentiableAt_Gamma (1 : ℂ) hpoles).continuousAt
  have hof : Tendsto (fun x : ℝ => (x : ℂ)) (nhds 1) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have hcg : Tendsto (fun x : ℝ => Complex.Gamma (x : ℂ))
      (nhds 1) (nhds (1 : ℂ)) := hc.comp hof
  have hre : Tendsto (fun z : ℂ => z.re) (nhds (1 : ℂ)) (nhds 1) :=
    Complex.continuous_re.continuousAt
  have hreal := hre.comp hcg
  simpa [Real.Gamma] using hreal

/-- **Gamma residue at the origin.** In the punctured real neighborhood of zero,
`eps * Gamma(eps)` tends to `1`.  This is exactly the residue input used by the
raised-dimensional box factorization. -/
theorem tendsto_mul_realGamma_zero :
    Tendsto (fun ε : ℝ => ε * Real.Gamma ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hadd0 : Tendsto (fun ε : ℝ => ε + 1) (nhds 0) (nhds 1) := by
    simpa using (tendsto_id.add tendsto_const_nhds :
      Tendsto (fun ε : ℝ => ε + 1) (nhds 0) (nhds (0 + 1)))
  have hadd : Tendsto (fun ε : ℝ => ε + 1)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hadd0.mono_left inf_le_left
  have hshift :
      Tendsto (fun ε : ℝ => Real.Gamma (ε + 1))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    continuousAt_realGamma_one.comp hadd
  apply hshift.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := by simpa using hε
  exact Real.Gamma_add_one hε0

end GppGammaResidueAtZero

#print axioms GppGammaResidueAtZero.continuousAt_realGamma_one
#print axioms GppGammaResidueAtZero.tendsto_mul_realGamma_zero
