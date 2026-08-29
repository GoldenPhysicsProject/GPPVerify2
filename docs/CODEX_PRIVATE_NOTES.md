# Codex private research notes

## Persistent source-mining directive

Do not treat the current Lean tree as the origin or full extent of the Golden Physics Project's ideas. A substantial amount of the conceptual ancestry, abandoned routes, partial calculations, literature, and potentially reusable mathematics lives in the user's Google Drive `GPP` folder, especially `GPP/Everything` and `GPP/Old shit`.

When a current research front stalls, needs provenance, or exposes a missing bridge, deliberately mine the GPP Drive archive for earlier versions and adjacent ideas before assuming the route is exhausted. In particular, search for material that can be reinterpreted in the current **shadow** language (older material may use ONON / On the Nature of Nature terminology). Extract only mathematically defensible content, test it independently, and formalize it in GPPVerify2 only when justified.

High-value archive families already visible in the GPP folder include:

- celestial holography / shadow transforms / CPT / googly and twistor material;
- Riemann, Weil, Hadamard, spectral multiplicity, explicit-formula, adelic and thermodynamic approaches;
- prime-gas and arithmetic/statistical-mechanical work;
- Yang–Mills, mass-gap, loop-measure and cut constructions;
- E8 / projection geometry / Grassmannian-related material;
- QFT, Born-rule, spacetime/emergence and information-theoretic derivations;
- `MASTER_INDEX.md`, `MASTER_EXECUTIVE_SUMMARY.md`, `three_paths_master_plan.md`, `the_crucial_connection.md`, RH attack/integration notes, and the large `Celestial_Holography_v8_COMPLETE-5.tex` as useful maps into older work.

The point is not to resurrect old claims uncritically. The archive is a **discovery mine**: trace where current shadow ideas came from, recover lemmas/calculations that may have been dropped during rewrites, compare competing routes, and turn any surviving exact mathematics into executable discovery code and then Lean theorems.

Operational rule: periodically rotate an `archive mining` lane alongside CI repair, Lean formalization, generalized cuts, arithmetic/Weil work, spectral analysis, thermodynamics, geometry, and physics. Record useful recovered ideas with their source/provenance and whether they are verified, conjectural, superseded, or falsified.

## Persistent axiom/scaffold retirement directive

Axiom and stub removal is a first-class research lane in every rotation, not end-of-project cleanup. Re-run the ranked census regularly and attack whatever can be removed honestly:

- replace accidental axioms for fixed data or conventions by explicit definitions or theorem parameters;
- delete unused open-claim axioms rather than preserving them for narrative completeness;
- replace `True` compatibility stubs by the actual theorem when that theorem has since been formalized elsewhere;
- split large missing results into exact finite/algebraic cores plus clearly named analytic or physics gaps;
- build missing Mathlib-level infrastructure ourselves when the dependency is standard mathematics and tractable;
- keep genuine unformalized physics assumptions visible as hypotheses/structures instead of baking desired conclusions into definitions;
- never reduce the census by weakening a substantive theorem into a tautology merely to improve the number.

Current rotation pattern: hard frontier → archive mining/version comparison → executable discovery → Lean promotion → axiom/scaffold retirement → CI/upgradeability repair → another hard frontier. While CI runs, immediately advance another lane.

Note from 2026-08-29: the immediately preceding recollection was Hadamard rather than Hurwitz. Do not delete or preserve the Hurwitz classification axiom merely because of that recollection; decide its status by actual mathematical dependency and formalization value.
