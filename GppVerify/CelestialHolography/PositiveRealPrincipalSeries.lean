import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Positive-real half-density principal series

Exact algebraic core of the positive-real principal-series dictionary used in the
Codex/GPT research track.

For the Lebesgue half-density dilation representation on `R_+`, generalized Mellin
modes have spectral parameter `s`, inversion acts by `s ↦ 1 - s`, and the unitary
axis is `Re s = 1/2`. Under the celestial transport `Δ = 2s`, the same reflection
becomes the scalar shadow `Δ ↦ 2 - Δ` and the unitary axis becomes `Re Δ = 1`.

This file formalizes only those exact complex-algebra statements. It makes no claim
that they constrain zeros of the Riemann zeta function.
-/

namespace GppPositiveReal

/-- Arithmetic spectral reflection induced by positive-real inversion. -/
def criticalReflection (s : ℂ) : ℂ := 1 - s

/-- Project dictionary from arithmetic Mellin weight to celestial conformal weight. -/
def celestialWeight (s : ℂ) : ℂ := 2 * s

/-- Scalar celestial shadow reflection. -/
def celestialShadow (Δ : ℂ) : ℂ := 2 - Δ

/-- Complex conjugation written componentwise, avoiding API-name dependence. -/
def complexConj (s : ℂ) : ℂ := ⟨s.re, -s.im⟩

/-- On the critical/unitary axis `Re s = 1/2`, inversion is complex conjugation. -/
theorem critical_reflection_eq_conj {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    criticalReflection s = complexConj s := by
  apply Complex.ext
  · simp [criticalReflection, complexConj, hs]
    norm_num
  · simp [criticalReflection, complexConj]

/-- Conversely, if inversion equals conjugation, then `s` lies on `Re s = 1/2`. -/
theorem critical_re_eq_half_of_reflection_eq_conj {s : ℂ}
    (h : criticalReflection s = complexConj s) :
    s.re = (1 : ℝ) / 2 := by
  have hre := congrArg Complex.re h
  simp [criticalReflection, complexConj] at hre
  linarith

/-- Exact characterization of the positive-real unitary axis. -/
theorem critical_reflection_eq_conj_iff {s : ℂ} :
    criticalReflection s = complexConj s ↔ s.re = (1 : ℝ) / 2 := by
  constructor
  · exact critical_re_eq_half_of_reflection_eq_conj
  · exact critical_reflection_eq_conj

/-- `Δ = 2s` maps the arithmetic critical axis to the scalar celestial principal axis. -/
theorem celestialWeight_re_eq_one {s : ℂ} (hs : s.re = (1 : ℝ) / 2) :
    (celestialWeight s).re = 1 := by
  simp [celestialWeight, hs]

/-- Conversely, `Re (2s) = 1` forces the arithmetic critical axis. -/
theorem critical_re_eq_half_of_celestialWeight_re_eq_one {s : ℂ}
    (hΔ : (celestialWeight s).re = 1) : s.re = (1 : ℝ) / 2 := by
  simp [celestialWeight] at hΔ
  linarith

/-- `Δ = 2s` identifies the arithmetic and scalar celestial unitary axes exactly. -/
theorem celestialWeight_re_eq_one_iff {s : ℂ} :
    (celestialWeight s).re = 1 ↔ s.re = (1 : ℝ) / 2 := by
  constructor
  · exact critical_re_eq_half_of_celestialWeight_re_eq_one
  · exact celestialWeight_re_eq_one

/-- `Δ = 2s` exactly intertwines `s ↦ 1-s` with the celestial shadow `Δ ↦ 2-Δ`. -/
theorem celestialWeight_intertwines_shadow (s : ℂ) :
    celestialWeight (criticalReflection s) = celestialShadow (celestialWeight s) := by
  simp [celestialWeight, criticalReflection, celestialShadow]
  ring

end GppPositiveReal
