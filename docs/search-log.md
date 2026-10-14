# Search-before-building log (Gate 2, W6)

Skill: `search-before-building-lean`. Date: 2026-10-07/08 (Home-Dell). Searches run from the session
scratchpad, read-only. Zero hits do not prove absence: "not found in <sources> on <date>".

Pins checked: `.lake/packages/mathlib` HEAD = `d13f23b723b8a846827a245b89c10fc7d3f11612` = manifest rev
(identical to `~/lean-work/openai-math-072-replay/src/lean/lake-manifest.json`). Reservoir index tarball
`leanprover-reservoir-index-477b5e7` (877 packages). Palomar: 469 entries, revision 187.

## 1. Mathlib at the pin (`rg -n -i <term> .lake/packages/mathlib/Mathlib`)

| Term | Hits | Relevant declaration (file:line at pin) | Decision |
|---|---|---|---|
| `woodbury` | 8 | `Matrix.add_mul_mul_inv_eq_sub` (LinearAlgebra/Matrix/NonsingularInverse.lean:604), `add_mul_mul_inv_eq_sub'` (:615) | not used: needs `IsUnit` of `A`, `C` and of the capacitance matrix as hypotheses, while T2 must *derive* invertibility of `1 - zB`; the direct two-sided resolvent identities (`G_w = G - c G P Pᵀ G_w` and its mirror) are shorter and give the conclusion. Built. |
| `add_mul_mul_inv` | 8 | same + `Matrix.add_mul_mul_invOf_mul_eq_one` (Invertible.lean:149) | as above |
| `theorem det_fin_two\b` | 1 | `Matrix.det_fin_two` (Determinant/Basic.lean:806) | used indirectly (simp set) |
| `theorem adjugate_fin_two\b` | 1 | `Matrix.adjugate_fin_two` (Adjugate.lean:373) | **used** (T4b) |
| `adjugate_mul` | 1 | `Matrix.adjugate_mul` (Adjugate.lean:269) | **used** (T4c) |
| `theorem inv_def` | 16 | `Matrix.inv_def` (NonsingularInverse.lean:172) | **used** (T4b) |
| `theorem mul_nonsing_inv\b` / `nonsing_inv_mul\b` | 1 / 1 | NonsingularInverse.lean:211 / :217 | not needed (two-sided inverses are hypotheses, as in the charter) |
| `theorem inv_eq_right_inv` / `inv_eq_left_inv` | 1 / 1 | NonsingularInverse.lean:464 / :459 | **used** `inv_eq_right_inv` (T2) |
| `transpose_nonsing_inv` / `conjTranspose_nonsing_inv` | 11 / 6 | NonsingularInverse.lean:202 / :205 | not needed (we never use `⁻¹` of `𝓛`; `Gᵀ = G` proved from `𝓛 G = 1`) |
| `mul_eq_one_comm` | 20 | root `mul_eq_one_comm` (Algebra/Group/Monoid.lean:54, `IsDedekindFiniteMonoid`) | **used** (one-sided ⇒ two-sided) |
| `unitaryGroup` | 83 | `Matrix.unitaryGroup` (LinearAlgebra/UnitaryGroup.lean) | not used: T1(c) states `Sᴴ S = 1 ∧ S Sᴴ = 1` literally (charter wording) |
| `theorem IsHermitian` | 57 | `Matrix.IsHermitian` (Hermitian.lean:49) | not used in statements (`Hᵀ = H` for real `H` is the paper's hypothesis) |
| `theorem trace_mul_comm` | 2 | Matrix/Trace.lean:158 | not needed (T3 via entrywise double sums) |
| `theorem conjTranspose_mul\b` | 1 | ConjTranspose.lean:342 | **used** |
| `PosSemidef`, `conjTranspose_mul_mul_same`, `dotProduct_mulVec_nonneg` | — | PosDef.lean:60, :314, :306 | **used** (T1d) |
| `l2_opNorm_def`, `Matrix.Norms.L2Operator` | — | Analysis/CStarAlgebra/Matrix.lean:185-198 | **used** (`contraction_norm_le_one`) |
| `fromRows_mul`, `fromRows_mul_fromCols`, `transpose_fromCols` | — | Data/Matrix/ColumnRowPartitioned.lean:218, :237, :130 | **used** (T2 blocks) |
| `scattering` | 0 | — | build |
| `Anderson` | 152 | all author names (Aaron Anderson) | no relevant hit |

## 2. Loogle (`https://loogle.lean-lang.org/json?q=…`, indexes Mathlib master: discovery only)

| Query | Count | Decision |
|---|---|---|
| `Matrix.add_mul_mul_inv_eq_sub` | 1 | see §1 |
| `Matrix.det_fin_two` | 1 | §1 |
| `Matrix.adjugate_fin_two` | 1 | §1 |
| `Matrix.mul_nonsing_inv` | 1 | §1 |
| `Matrix.nonsing_inv_mul` | 1 | §1 |
| `Matrix.unitaryGroup` | 46 | §1 |
| `Matrix.IsHermitian` | 130 | §1 |
| `Matrix.trace_mul_comm` | 1 | §1 |
| `Matrix.conjTranspose_nonsing_inv` | 1 | §1 |
| `Matrix.inv_eq_left_inv` | 1 | §1 |
| `Matrix.IsSymm` | 74 | not used |
| `"Woodbury"` (docstring search) | 0 | — |
| `"scattering"` | 0 | — |
| `"resolvent", Matrix` | 0 | — |

## 3. Reservoir index (tarball `477b5e7`, `grep -ril … --include=metadata.json`)

`scattering` 0; `anderson` 0; `localization` 0; `resolvent` 0; `woodbury` 0; `random schr` 0;
`unitary matrix` 0. Decision: nothing to require.

## 4. Palomar (paged results API, 469 entries, revision 187)

`grep -i -e scattering -e anderson -e woodbury -e unitary -e resolvent`: 9 rows, none about scattering
matrices of resolvents or Anderson models (unitary-matrix factorization `alialiev78/gs_Lean_formalization`,
Fried-conjecture resonance clusters, MarkovProcess, Fourier–Jacobi, sofic groups, lean-spectral-theory,
lean-operator-theory, sequential products). Decision: none applicable.

## 5. GitHub long tail (`gh search repos/code --language Lean`)

| Query | Hits | Decision |
|---|---|---|
| repos `scattering matrix` | 0 | — |
| repos `Anderson localization` | 0 | — |
| repos `Woodbury` | 0 | — |
| code `Woodbury` | 10 | Mathlib copies/forks of NonsingularInverse/Invertible; `FormalFrontier/general-linear-groups`, `ShengtongZhang-alt/bilu-linial-opus`, `mario-ullrich/Lean-Discretization` (Sherman–Morrison). None needed: §1. |
| code `scattering matrix` | 5 | **lead**: `LeanPool/lean-pool` `LeanPool/MicrowaveNetworks/{Basic,PhaseShifters,HybridCouplersPhaseShifters}.lean` (Apache-2.0, 140★, rev `bbc67ff1`): S-parameter `Network n` with series/parallel/phase-shifter combinators. Different object (lossless network algebra, not the resolvent-derived `S = 1 + 2i YᵀGY`); not reused. `NikoBiele/RayTraceHeatTransfer.jl` formal/Thm31-32: radiative exchange, unrelated. |
| code `Anderson model` | 0 | — |

New lead for the lab ledger (`docs/org/lean-adoption-candidates.yaml`, not edited here: W6 may only write
this repo): `LeanPool/lean-pool` MicrowaveNetworks, `discovered_via: github-code-search@2026-10-08`,
status new, relevance: scattering-matrix network algebra.

## 6. `lean-pkg search` (registry, index, Loogle, LeanSearch, Reservoir, Palomar, GitHub; not `--record`)

| Term | registry | index | loogle | leansearch | reservoir | palomar | github |
|---|---|---|---|---|---|---|---|
| `scattering matrix` | 0 | 0 | skipped (not a Loogle query) | 10, none relevant | 0 | 0 | 5 (= §5) |
| `Woodbury` | 0 | 0 | skipped | 10 (Mathlib Woodbury) | 0 | 0 | 24 (Mathlib copies, §5) |
| `Anderson localization` | 0 | 0 | skipped | 10 (ring localization, false friend) | 0 | 0 | 0 |
| `resolvent identity` | 0 | 0 | skipped | 10 | 0 | 1 (MarkovProcess) | 24 (TauCeti/LeanPool operator resolvents, unbounded/semigroup setting) |

## Decision

**Build.** Every identity is a short finite-matrix computation over Mathlib's `Matrix` API; no
library formalizes the resolvent-derived scattering matrix, the closure formula, the energy identity
or the endpoint identity (not found in the sources above on 2026-10-08).
