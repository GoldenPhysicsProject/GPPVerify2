import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Zitterbewegung and the celestial shadow energy map: exact arithmetic layer

Historical provenance: this file originated from `zitterbewegung_T_boundary_FINAL.tex`, where the
factor `2E/ℏ` was discussed through a celestial-shadow pairing. Later archive work
(`Which_Way_Is_Forward_v6..v10`) gives a strictly cleaner origin for the physical factor two:
in the rest-frame Dirac two-state system `U(t) = exp(-i ω_C t σ₁)`, the adjoint/projective
`SU(2) → SO(3)` action rotates observables through angle `2 ω_C t`. Thus the zitterbewegung
factor two does not require celestial shadow.

The scalar statements below remain valid and useful as exact identities for the Mellin/shadow
energy map:

* `shadow_energy_eq` — under `λ = log(E/μ)`, the reflected energy coordinate is
  `Ẽ = μ·e^{-λ} = μ²/E`;
* `shadow_splitting` / `shadow_splitting_onshell` — the associated scalar splitting and its
  vanishing at `μ = E`;
* `shadow_frequency_onshell` — at `μ = E`, the sum `(E + μ²/E)/ℏ` is `2E/ℏ`;
* `beat_frequency` — the beat between scalar phase frequencies `±E/ℏ` is `2E/ℏ`;
* `zitter_scale_frequency_product` — with `a_Z = ℏ/(2mc)` and
  `ω_Z = 2mc²/ℏ`, their product is exactly `c`.
* `mirror_dm_bound` — a purely conditional arithmetic lemma: if a quantity `Ωmirror` equals
  `Ωb` and is bounded above by `Ωdm`, then `Ωdm/Ωb ≥ 1`. It is not evidence for a mirror
  sector and no longer carries the superseded `T`-boundary interpretation.

No theorem in this file identifies celestial shadow with Wigner time reversal, CPT, worldline
orientation reversal, or the Dirac negative-energy component. Those are separate structures and
would require additional equivariant/physical input.
-/

namespace GppZitter

/-- Under `λ = log(E/μ)`, the reflected energy coordinate is
    `Ẽ = μ·e^{-λ} = μ²/E`, exactly. -/
theorem shadow_energy_eq {E μ : ℝ} (hE : 0 < E) (hμ : 0 < μ) :
    μ * Real.exp (-(Real.log (E / μ))) = μ ^ 2 / E := by
  rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < E / μ)]
  field_simp
  ring

/-- The scalar splitting `E − Ẽ = E − μ²/E`. -/
theorem shadow_splitting {E μ : ℝ} (hE : 0 < E) (hμ : 0 < μ) :
    E - μ * Real.exp (-(Real.log (E / μ))) = E - μ ^ 2 / E := by
  rw [shadow_energy_eq hE hμ]

/-- At the on-shell Mellin scale `μ = E` the scalar splitting vanishes. -/
theorem shadow_splitting_onshell {E : ℝ} (hE : E ≠ 0) :
    E - E ^ 2 / E = 0 := by
  field_simp
  ring

/-- At `μ = E`, the scalar sum `(E + Ẽ)/ℏ` is exactly `2E/ℏ`.
    The physical origin of the Dirac zitterbewegung factor two is independently the
    `SU(2) → SO(3)` adjoint/projective action, not this scalar identity by itself. -/
theorem shadow_frequency_onshell {E hbar : ℝ} (hE : E ≠ 0) (hh : hbar ≠ 0) :
    (E + E ^ 2 / E) / hbar = 2 * E / hbar := by
  rw [show E ^ 2 / E = E from by field_simp; ring]
  ring

/-- The beat between the scalar phase frequencies `+E/ℏ` and `−E/ℏ` is `2E/ℏ`. -/
theorem beat_frequency {E hbar : ℝ} (hE : 0 < E) (hh : 0 < hbar) :
    |E / hbar - (-(E / hbar))| = 2 * E / hbar := by
  rw [sub_neg_eq_add, abs_of_pos (by positivity)]
  ring

/-- The exact Compton/zitter scale-frequency invariant:
    `(ℏ/(2mc)) · (2mc²/ℏ) = c`. -/
theorem zitter_scale_frequency_product {m c hbar : ℝ}
    (hm : m ≠ 0) (hc : c ≠ 0) (hh : hbar ≠ 0) :
    (hbar / (2 * m * c)) * (2 * m * c ^ 2 / hbar) = c := by
  field_simp
  ring

/-- Purely conditional arithmetic: if `Ωmirror = Ωb ≤ Ωdm` with `Ωb > 0`, then
    `Ωdm/Ωb ≥ 1`. This theorem makes no claim that such a mirror sector exists. -/
theorem mirror_dm_bound {Ωdm Ωb Ωmirror : ℝ} (hb : 0 < Ωb)
    (hmirror : Ωmirror = Ωb) (hle : Ωmirror ≤ Ωdm) :
    1 ≤ Ωdm / Ωb := by
  rw [le_div_iff₀ hb]
  linarith

end GppZitter