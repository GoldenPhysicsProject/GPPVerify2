import GppVerify.RiemannHypothesis.HeatTraceCriterion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Causal Dirichlet-heat boundary anomaly: scalar core

The causal replacement in the arithmetic heat-trace program uses the Dirichlet heat kernel
on the positive half-line and the unilateral translation by `a > 0`. On the diagonal, the
commutator kernel has the two pieces

  g(a) - g(a + 2x),             0 < x < a,
  g(2x - a) - g(2x + a),       x >= a,

where for the heat problem `g = g_t` is the normalized Gaussian.

For a finite cutoff `R`, affine changes of variables give exactly

  T_R(a) = a g(a) - (1/2) integral_[2R-a,2R+a] g.

The moving window has fixed width `2a`; hence it vanishes for every kernel `g(x) -> 0` as
`x -> +infinity`. The normalized heat Gaussian has this decay for every `t > 0`, so the
scalar anomaly is exactly

  lim_R T_R(a) = a / sqrt(4*pi*t) * exp(-a^2/(4t)).

This file does not yet package the Dirichlet heat operators or prove trace-classness of their
commutator. It closes the scalar diagonal-integral part of that operator theorem.
-/

namespace GppCausalHeatBoundaryAnomaly

open Filter Set Metric intervalIntegral

/-- The normalized one-dimensional heat Gaussian. -/
noncomputable def heatKernelGaussian (t x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / (4 * t)) / Real.sqrt (4 * Real.pi * t)

/-- Finite-cutoff diagonal integral of the causal heat/translation commutator. -/
noncomputable def truncatedBoundaryTrace (g : ℝ → ℝ) (a R : ℝ) : ℝ :=
  (∫ x in 0..a, (g a - g (a + 2 * x))) +
    ∫ x in a..R, (g (2 * x - a) - g (2 * x + a))

/-- Affine substitution for the boundary piece `g(a+2x)`. -/
theorem two_mul_integral_zero_a_add_two
    (g : ℝ → ℝ) (a : ℝ) :
    2 * (∫ x in 0..a, g (a + 2 * x)) = ∫ y in a..(3 * a), g y := by
  have h := intervalIntegral.mul_integral_comp_add_mul g 2 a (a := 0) (b := a)
  simpa [add_comm, add_left_comm, add_assoc] using h

/-- Affine substitution for `g(2x-a)` on the bulk interval. -/
theorem two_mul_integral_a_R_two_sub
    (g : ℝ → ℝ) (a R : ℝ) :
    2 * (∫ x in a..R, g (2 * x - a)) =
      ∫ y in a..(2 * R - a), g y := by
  have h := intervalIntegral.mul_integral_comp_mul_sub g 2 a (a := a) (b := R)
  simpa using h

/-- Affine substitution for `g(2x+a)` on the bulk interval. -/
theorem two_mul_integral_a_R_two_add
    (g : ℝ → ℝ) (a R : ℝ) :
    2 * (∫ x in a..R, g (2 * x + a)) =
      ∫ y in (3 * a)..(2 * R + a), g y := by
  have h := intervalIntegral.mul_integral_comp_mul_add g 2 a (a := a) (b := R)
  simpa using h

/-- **Exact finite-cutoff boundary cancellation.** The only remainder is a moving window
of the underlying kernel at the far endpoint. -/
theorem truncatedBoundaryTrace_eq_boundary_minus_tail
    (g : ℝ → ℝ) (a R : ℝ) :
    truncatedBoundaryTrace g a R =
      a * g a - (1 / 2 : ℝ) * (∫ y in (2 * R - a)..(2 * R + a), g y) := by
  unfold truncatedBoundaryTrace
  rw [integral_sub, integral_sub]
  have hconst : (∫ _x in (0 : ℝ)..a, g a) = a * g a := by
    simp [intervalIntegral.integral_const]
    ring
  rw [hconst]
  have h1 := two_mul_integral_zero_a_add_two g a
  have h2 := two_mul_integral_a_R_two_sub g a R
  have h3 := two_mul_integral_a_R_two_add g a R
  have hadd1 :
      (∫ y in a..(3 * a), g y) + (∫ y in (3 * a)..(2 * R + a), g y) =
        ∫ y in a..(2 * R + a), g y :=
    integral_add_adjacent_intervals _ _ _
  have hadd2 :
      (∫ y in a..(2 * R - a), g y) +
        (∫ y in (2 * R - a)..(2 * R + a), g y) =
        ∫ y in a..(2 * R + a), g y :=
    integral_add_adjacent_intervals _ _ _
  linarith

/-- **Fixed-width moving windows vanish for every kernel decaying at `+infinity`.**
No global integrability assumption is required. -/
theorem movingWindowIntegral_tendsto_zero
    {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ∫ y in (2 * R - a)..(2 * R + a), g y) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := ε / (4 * a)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hev : ∀ᶠ y : ℝ in atTop, dist (g y) 0 < C :=
    hg.eventually (ball_mem_nhds 0 hC)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine Filter.eventually_atTop.2 ⟨(N + a) / 2, ?_⟩
  intro R hR
  have hlow : N ≤ 2 * R - a := by linarith
  have hle : 2 * R - a ≤ 2 * R + a := by linarith
  have hpt : ∀ y ∈ Ι (2 * R - a) (2 * R + a), ‖g y‖ ≤ C := by
    intro y hy
    rw [uIoc_of_le hle] at hy
    have hNy : N ≤ y := le_trans hlow (le_of_lt hy.1)
    have hyC : dist (g y) 0 < C := hN y hNy
    simpa [Real.dist_eq, Real.norm_eq_abs] using le_of_lt hyC
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hwidth : |(2 * R + a) - (2 * R - a)| = 2 * a := by
    rw [show (2 * R + a) - (2 * R - a) = 2 * a by ring,
      abs_of_pos (mul_pos (by norm_num) ha)]
  rw [hwidth] at hbound
  have hcalc : C * (2 * a) = ε / 2 := by
    dsimp [C]
    field_simp [ha.ne']
    ring
  rw [hcalc] at hbound
  have hlt : ‖∫ y in (2 * R - a)..(2 * R + a), g y‖ < ε := by
    linarith
  simpa [dist_zero_right] using hlt

/-- **Generic scalar boundary anomaly limit.** If the underlying kernel decays at positive
infinity, the finite-cutoff diagonal trace converges to the boundary value `a*g(a)`. -/
theorem truncatedBoundaryTrace_tendsto_boundary
    {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => truncatedBoundaryTrace g a R) atTop (𝓝 (a * g a)) := by
  have htail := movingWindowIntegral_tendsto_zero hg ha
  have hhalf :
      Tendsto
        (fun R : ℝ => (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), g y))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul htail)
  have hmain :
      Tendsto
        (fun R : ℝ => a * g a - (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), g y))
        atTop (𝓝 (a * g a)) := by
    simpa using (tendsto_const_nhds.sub hhalf)
  have heq :
      (fun R : ℝ => truncatedBoundaryTrace g a R) =
        (fun R : ℝ => a * g a - (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), g y)) := by
    funext R
    exact truncatedBoundaryTrace_eq_boundary_minus_tail g a R
  rw [heq]
  exact hmain

/-- For every positive heat time, the normalized Gaussian decays at positive infinity. -/
theorem heatKernelGaussian_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (heatKernelGaussian t) atTop (𝓝 0) := by
  have hden : 0 < 4 * t := by positivity
  have harg : Tendsto (fun x : ℝ => x ^ 2 / (4 * t)) atTop atTop := by
    have hev : ∀ᶠ x : ℝ in atTop, x ≤ x ^ 2 / (4 * t) := by
      filter_upwards [eventually_ge_atTop (max 0 (4 * t))] with x hx
      have hx0 : 0 ≤ x := (le_max_left 0 (4 * t)).trans hx
      have hxt : 4 * t ≤ x := (le_max_right 0 (4 * t)).trans hx
      rw [le_div_iff₀ hden]
      nlinarith
    exact tendsto_atTop_mono' atTop hev tendsto_id
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (-(x ^ 2 / (4 * t)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp harg
  have hscale :
      Tendsto
        (fun x : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹ *
          Real.exp (-(x ^ 2 / (4 * t))))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp)
  simpa [heatKernelGaussian, div_eq_inv_mul, mul_comm] using hscale

/-- Specialization of the finite-cutoff identity to the normalized heat Gaussian. -/
theorem truncatedHeatBoundaryTrace_eq
    (t a R : ℝ) :
    truncatedBoundaryTrace (heatKernelGaussian t) a R =
      a * heatKernelGaussian t a -
        (1 / 2 : ℝ) *
          (∫ y in (2 * R - a)..(2 * R + a), heatKernelGaussian t y) := by
  exact truncatedBoundaryTrace_eq_boundary_minus_tail (heatKernelGaussian t) a R

/-- **Exact scalar causal heat-boundary anomaly.** -/
theorem truncatedHeatBoundaryTrace_tendsto
    {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    Tendsto (fun R : ℝ => truncatedBoundaryTrace (heatKernelGaussian t) a R)
      atTop
      (𝓝 (a / Real.sqrt (4 * Real.pi * t) * Real.exp (-(a ^ 2) / (4 * t)))) := by
  have h := truncatedBoundaryTrace_tendsto_boundary (heatKernelGaussian_tendsto_zero ht) ha
  convert h using 1
  unfold heatKernelGaussian
  ring

end GppCausalHeatBoundaryAnomaly

#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_zero_a_add_two
#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_a_R_two_sub
#print axioms GppCausalHeatBoundaryAnomaly.two_mul_integral_a_R_two_add
#print axioms GppCausalHeatBoundaryAnomaly.truncatedBoundaryTrace_eq_boundary_minus_tail
#print axioms GppCausalHeatBoundaryAnomaly.movingWindowIntegral_tendsto_zero
#print axioms GppCausalHeatBoundaryAnomaly.truncatedBoundaryTrace_tendsto_boundary
#print axioms GppCausalHeatBoundaryAnomaly.heatKernelGaussian_tendsto_zero
#print axioms GppCausalHeatBoundaryAnomaly.truncatedHeatBoundaryTrace_tendsto
