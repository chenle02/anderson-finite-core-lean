# conj-anderson-lean

Lean 4 companion for the lab's audit of openai/math family 261, paper P2 (*Pure-Point Spectrum for
the Two-Dimensional Anderson Model at Every Positive Disorder*, upstream commit `adc7f124`).
Gate 2 of the program charter (Le-AI-Lab `docs/org/programs/2026-10-07-anderson-localization-audit-program.md`).

**Scope (honest):** only the finite-dimensional algebraic core is formalized, as a comparator
Challenge/Solution pair: the absorption identities and symmetric unitarity of the scattering matrix
(`mat:ward`), the common-phase closure formula (`mat:closure`), the exact single-port energy
identity with its time-reversal perfect square (`mat:energy-closure`), and the endpoint identity
(`boot:endpoint-identity`). **Not formalized:** `mat:cutoff`, `mat:weak`, and every analytic,
probabilistic or multiscale part of the paper, i.e. everything that carries the localization claim.
Nothing here verifies the paper's theorem. See `docs/scope.md`.

Pins: Lean `v4.34.1`, Mathlib `d13f23b723b8` (the lab's pins; same as the openai/math replay tree).
Working repo of the audit: `../conj-anderson-audit` (private).

## Layout and build

- `ComparatorChallenges/AndersonFiniteCore.lean` + `.json`: trusted definitions and the 21 theorem
  statements (`sorry` bodies); comparator config (`definition_names: []`, axioms propext/Quot.sound/Classical.choice).
- `AndersonAudit/FiniteCore.lean`: the solution (full proofs). `AndersonAudit/Axioms.lean`: `#print axioms`.
- `docs/scope.md`: printed types beside the paper sentences, fidelity verdicts, "Not formalized".
- `docs/search-log.md`: prior-art search record. `docs/printed-types.txt`: `#check` output at the pins.

```sh
lake exe cache get
systemd-run --user --scope -p CPUQuota=600% -p MemoryMax=16G lake build
```
