import GppVerify.CelestialHolography.RegulatedBoxLandenIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Branch-free real dilogarithm on the full negative axis

For `y < 0`, write `x = -y > 0` and use Landen as the definition

  Li2_neg(y) = -Li2(x/(1+x)) - (1/2) log(1+x)^2.

Equivalently,

  Li2_neg(y) = -Li2((-y)/(1-y)) - (1/2) log(1-y)^2.

The transformed dilogarithm argument always lies in `(0,1)`, so this extends the
project's real series to the entire negative axis without complex logarithms or branch
choices.  Its derivative is the classical real formula `-log(1-y)/y`.
-/

namespace GppRegulatedBoxDilogNegativeExtension

open GppRegulatedBoxDilogSeries
open GppRegulatedBoxDilogDerivative
open GppRegulatedBoxLandenIdentity

/-- Landen-defined real continuation to negative arguments.  Its intended domain is
`y < 0`; the formula itself is left total as a real function for compositional use. -/
noncomputable def li2NegativeExtension (y : ℝ) : ℝ :=
  -li2Series ((-y) / (1 - y)) - (Real.log (1 - y)) ^ 2 / 2

/-- On the original negative unit interval, the Landen extension agrees exactly with
the defining real power series. -/
theorem li2NegativeExtension_eq_series_neg
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    li2NegativeExtension (-x) = li2Series (-x) := by
  have hden : (1 + x : ℝ) ≠ 0 := by linarith
  have harg : (-(-x)) / (1 - (-x)) = x / (1 + x) := by ring
  have hlogarg : 1 - (-x) = 1 + x := by ring
  have hL := li2Series_landen hx0 hx1
  unfold li2NegativeExtension
  rw [harg, hlogarg]
  linarith

/-- The Landen extension has the classical real dilogarithm derivative at every
negative real argument. -/
theorem hasDerivAt_li2NegativeExtension
    {y : ℝ} (hy : y < 0) :
    HasDerivAt li2NegativeExtension (-Real.log (1 - y) / y) y := by
  have hyneg : 0 < -y := neg_pos.mpr hy
  have hdenpos : 0 < 1 - y := by linarith
  have hden : (1 - y : ℝ) ≠ 0 := ne_of_gt hdenpos
  have hyne : y ≠ 0 := ne_of_lt hy
  let a : ℝ := (-y) / (1 - y)
  have ha0 : 0 < a := by
    dsimp [a]
    exact div_pos hyneg hdenpos
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one hdenpos).2
    linarith

  have hnum : HasDerivAt (fun t : ℝ => -t) (-1) y := by
    simpa using (hasDerivAt_id y).neg
  have hdenfun : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
    convert (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y) using 1 <;> ring
  have hinner_raw := hnum.div hdenfun hden
  have hinner :
      HasDerivAt (fun t : ℝ => (-t) / (1 - t)) (-1 / (1 - y) ^ 2) y := by
    convert hinner_raw using 1 <;> field_simp [hden] <;> ring

  have hLiBase := hasDerivAt_li2Series ha0 ha1
  have hLiComp := hLiBase.comp y hinner

  have hone_minus : 1 - a = 1 / (1 - y) := by
    dsimp [a]
    field_simp [hden]
    ring
  have hrecipne : (1 / (1 - y) : ℝ) ≠ 0 := one_div_ne_zero hden
  have hlogrecip : Real.log (1 / (1 - y)) = -Real.log (1 - y) := by
    have hm := Real.log_mul hrecipne hden
    have hmul : (1 / (1 - y)) * (1 - y) = (1 : ℝ) := by
      field_simp [hden]
    rw [hmul, Real.log_one] at hm
    linarith
  have hLi :
      HasDerivAt (fun t : ℝ => -li2Series ((-t) / (1 - t)))
        (-Real.log (1 - y) / (y * (1 - y))) y := by
    rw [hone_minus, hlogrecip] at hLiComp
    have H := hLiComp.neg
    convert H using 1 <;> field_simp [hyne, hden] <;> ring

  have hlogBase : HasDerivAt Real.log (1 / (1 - y)) (1 - y) := by
    simpa using Real.hasDerivAt_log hden
  have hlogComp := hlogBase.comp y hdenfun
  have hlogSq :
      HasDerivAt (fun t : ℝ => -((Real.log (1 - t)) ^ 2 / 2))
        (Real.log (1 - y) / (1 - y)) y := by
    have H := (hlogComp.pow 2).div_const 2
    have Hneg := H.neg
    convert Hneg using 1 <;> field_simp [hden] <;> ring

  have hsum := hLi.add hlogSq
  have hcoef :
      -Real.log (1 - y) / (y * (1 - y)) +
          Real.log (1 - y) / (1 - y) = -Real.log (1 - y) / y := by
    field_simp [hyne, hden]
    ring
  unfold li2NegativeExtension
  convert hsum using 1
  exact hcoef.symm

end GppRegulatedBoxDilogNegativeExtension

#print axioms GppRegulatedBoxDilogNegativeExtension.li2NegativeExtension_eq_series_neg
#print axioms GppRegulatedBoxDilogNegativeExtension.hasDerivAt_li2NegativeExtension
