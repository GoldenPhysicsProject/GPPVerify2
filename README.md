# GPPVerify2 — Golden Physics Project Lean 4 formalization

`GPPVerify2` is the Codex/GPT formal-verification workbench for the Golden Physics Project. It is not an RH-only repository. The repository formalizes exact mathematical layers arising across celestial amplitudes, representation theory and spectral analysis, analytic number theory, thermodynamic number theory, Grassmannian geometry, quantum field theory, gravity, and the broader ONON framework.

**Blueprint:** https://lean.goldenphysics.org  
**Project:** https://goldenphysics.org  
**Author:** Daniel Toupin | ORCID: 0009-0003-7682-9579

The Codex working branch is `codex/lean-workbench`. Experimental and numerical work belongs in the companion repository `GPPDiscovery2` on `codex/discovery-workbench`; durable Codex research state belongs in the `codex` Supabase schema.

---

## What this repository is for

The governing rule is simple: formalize real mathematics, preserve the exact boundary between proved and open statements, and never make the repository look stronger by weakening the claim.

The current active program has four major research fronts.

### 1. Celestial amplitudes, dispersion, Yang–Mills and gravity

Formal targets include:

- celestial-cut and Mellin-transform kinematics;
- regulated scalar box identities, dispersion reconstruction, regulator limits, endpoint control, and raised-box/dimension-shift arguments;
- simplex majorants, Beta reductions, Fubini/Tonelli and dominated-convergence closure;
- honest fixed-loop-momentum Yang–Mills sewing numerators, including the `D_s = 4`, `μ ≠ 0` state sum rather than scalar reconstruction relabelled as gauge theory;
- higher-loop and generalized cuts;
- gravity cuts and the analytic/subtraction hypotheses required for amplitude reconstruction.

A cut identity is not by itself an amplitude theorem. Generalized-cut completeness, analyticity, subtraction data, normalization, color/state sums, and loop induction are tracked explicitly when required.

### 2. Half-densities, principal series, completed zeta and the Weil bridge

Formal targets include:

- positive-real dilation characters and half-density normalization;
- `Δ = 2s`, shadow `s ↦ 1-s`, and critical-line unitarity/conjugation;
- completed-zeta and Archimedean Gamma response;
- Mehler–Fock/Legendre spectral weights;
- Wiener–Hopf positive factors and exact spectral kernels;
- explicit-formula transport and the genuine Weil quadratic form.

The local representation-theoretic and spectral structure does **not** prove RH. A successful RH route must construct the completed global object without encoding unknown zeros, identify its quadratic form with the actual Weil explicit-formula criterion on an adequate test class, and prove the required global positivity unconditionally.

### 3. Prime-gas and number thermodynamics

Formal targets include:

- Gibbs measures on integers and prime/von-Mangoldt weighted ensembles;
- partition functions, free energy, entropy, response functions and cumulants;
- exact log-moment summability;
- finite and countable Fisher/Hessian geometry;
- covariance determinants and Vandermonde/Cauchy–Binet structure;
- thermodynamic limits and fluctuation geometry.

One-dimensional Fisher geometry is intrinsically flat; curvature claims therefore require a genuinely multi-parameter statistical family.

### 4. Exact spectral-weight, chamber and convolution mathematics

Formal targets include:

- exact Gamma/Mehler–Fock spectral-weight identities;
- positivity and recurrence of chamber polynomials;
- Wiener–Hopf factorization identities;
- chamber convolution formulas when they are actually justified;
- exact period/MZV structure at higher loop order.

Previously tempting extrapolations, such as unrestricted all-loop rationality of chamber integrals, are not treated as theorems without proof.

---

## Representative certified results

The repository contains many independent exact layers. Representative examples include:

- Haar self-duality and functional-equation infrastructure;
- the Grassmannian transition identity `τ ∘ τ = -id` as a theorem rather than an axiom;
- positive-real half-density/shadow dilation identities;
- exact Gamma/Mehler–Fock spectral recurrences and positivity results;
- Wiener–Hopf/Gamma factor identities;
- scalar-box endpoint, special-function and regulator lemmas;
- number-Gibbs entropy and differential thermodynamics;
- finite-support Fisher/Vandermonde identities, including the arbitrary finite normalized identity
  `ordered Vandermonde energy = 6 × det Cov(X, X²)`;
- countable raw-moment/Fisher determinant limit infrastructure.

These are reusable mathematical components. Their existence does not silently promote any still-open global theorem.

---

## Proof-status discipline

Three categories must always be distinguished:

1. **proved theorem** — Lean kernel checks the intended mathematical statement from Mathlib and explicitly listed assumptions;
2. **explicit axiom/input** — a named external physical or mathematical input whose role is visible in the dependency graph;
3. **honest scaffold/stub** — infrastructure placeholder that proves no substantive open claim and whose documentation names the missing mathematics.

Never collapse these categories in status reports.

### No-`sorry` rule

`codex/lean-workbench` is maintained under a zero-`sorry` discipline. New work must not introduce `sorry`, `admit`, or an equivalent unsound escape hatch. CI should treat this as an invariant, not as a one-time cleanup campaign.

### Stub retirement

Existing `True := trivial` scaffolds are not proofs. They should be retired only by replacing them with the intended theorem and a real proof. Deleting a difficult target, weakening its statement while retaining the name, or moving the claim into an axiom does not count as progress.

### Axiom minimization

The axiom inventory is audited separately from `sorry` and stubs. Physics inputs, mathematical external assumptions, and reducible convenience axioms should be categorized separately. Whenever Mathlib or an already-proved theorem can replace a custom axiom, the custom axiom should be removed.

---

## Discovery → formalization workflow

The Codex/GPT workflow is deliberately split across two repositories.

### `GPPDiscovery2`

Use `codex/discovery-workbench` for exact symbolic algebra, Python/SymPy/mpmath/NumPy/SciPy experiments, interval checks, numerical convergence studies, counterexample searches, period recognition, and reproducible derivations.

Numerical evidence is never imported into Lean as if it were a theorem. A discovery is promoted only after its exact mathematical statement, hypotheses, domains, branch choices, and singular cases are understood.

### `GPPVerify2`

Use `codex/lean-workbench` for exact theorem statements and kernel-checked proofs. Search the pinned Mathlib version before creating parallel infrastructure. Prefer standard Mathlib objects and theorems whenever they express the same mathematics cleanly.

Discovery scripts may generate constants or finite data used by a proof only when the generation procedure and validation are reproducible and the Lean theorem checks the mathematically relevant property rather than merely trusting an opaque numerical artifact.

---

## Mathlib alignment and maintenance

The project tracks a pinned Lean/Mathlib toolchain. Maintenance work includes:

- replacing obsolete custom lemmas with equivalent standard Mathlib results when doing so simplifies dependencies;
- avoiding redundant local definitions that obscure standard mathematical structure;
- keeping theorem statements stable while refactoring implementations;
- running the complete Lake build after substantive changes;
- auditing `sorry`, custom axioms, and vacuous scaffolds independently;
- using `#print axioms` on important theorem endpoints.

Refactoring is valuable only when it preserves or strengthens the actual theorem.

---

## Physics-to-mathematics translation

Physics notation is retained where useful, but theorem docstrings should identify the mathematical object being formalized. For non-obvious constructions, document mappings such as:

- physical scaling dimension ↔ complex principal-series parameter;
- shadow transform ↔ reciprocal/conjugate dilation character;
- cut phase space ↔ a measure/integral on a specified domain;
- regulator ↔ a parameterized integrable family with a stated limiting filter;
- state sum ↔ a finite sum over an explicitly defined polarization/state basis;
- thermodynamic susceptibility ↔ covariance/Hessian entry;
- spectral density ↔ a real/complex-valued function with stated positivity and normalization properties.

The purpose is not pedagogical decoration; it prevents verbal physics shorthand from hiding a different formal statement.

---

## Current high-value open boundaries

The most important active boundaries include:

- **scalar raised box:** package the fixed simplex majorant as an actual `Integrable` object, justify the required Fubini/Tonelli steps, and invoke measure-theoretic dominated convergence;
- **Yang–Mills:** compute and normalize the genuine fixed-loop-momentum `D_s = 4`, `μ ≠ 0` gluon sewing numerator and then extend to generalized cuts;
- **gravity:** higher-multiplicity/generalized-cut reconstruction with the necessary analytic hypotheses;
- **Weil/RH:** assemble the signed prime-plus-Archimedean global quadratic form, identify it with the genuine Weil criterion on the correct test class, and prove unconditional positivity;
- **number thermodynamics:** pass finite Fisher positivity cleanly to countable Gibbs/arithmetic ensembles using summability and normalization;
- **higher chamber integrals:** determine the correct period/MZV class rather than assume rationality;
- **broader ONON formalization:** replace remaining honest scaffolds in Grassmannian, QFT, Standard Model, Yang–Mills, gravity and number-theory modules by actual mathematics as infrastructure becomes available.

These boundaries are expected to move. Durable session-by-session state belongs in Supabase `codex.research_notes`, not in this README.

---

## Build and audit

```bash
lake exe cache get
lake build

# No-sorry invariant
grep -rn "^\s*sorry\s*$" --include="*.lean" GppVerify/

# Custom axiom inventory
grep -rn "^axiom " --include="*.lean" GppVerify/

# Honest scaffold inventory
grep -rn ": True := trivial" --include="*.lean" GppVerify/
```

Important endpoints should additionally be checked with `#print axioms` and the repository audit scripts.

---

## Blueprint and dependency map

```bash
pip install leanblueprint
cd blueprint
leanblueprint build
```

See `docs/DependencyMap.md` for the broader theorem dependency map. The live blueprint is at https://lean.goldenphysics.org.

---

## Status principle

This repository is an executable mathematical research program, not a claim counter. A theorem is reported as proved only when its intended statement is present and kernel-checked; a numerical or symbolic discovery is reported at its actual evidentiary level; and an unresolved global theorem remains unresolved until every required bridge is closed.