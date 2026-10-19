<div align="center">

# Anderson finite core (Lean)

Lean 4 proofs of the finite-dimensional algebraic identities (absorption identities and unitarity of the scattering matrix $S=\mathbf 1+2iY^\top GY$, the common-phase closure formula, the single-port energy identity, the two-probe endpoint identity) used in a paper on pure-point spectrum for the two-dimensional Anderson model; the paper's localization theorem is **not** formalized.

[![Lean CI](https://github.com/chenle02/anderson-finite-core-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/chenle02/anderson-finite-core-lean/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.34.1-153e63)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-d13f23b-153e63)](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612)
[![License](https://img.shields.io/badge/license-Apache--2.0-153e63)](LICENSE)

[What is proved](#what-is-proved) · [Verification page](docs/scope.md) · [Build](#build-and-verify) · [Cite](CITATION.cff)

</div>

## What is proved

Twenty-one theorems about finite complex matrices, in [`AndersonAudit/FiniteCore.lean`](AndersonAudit/FiniteCore.lean),
each checked against its statement in [`ComparatorChallenges/AndersonFiniteCore.lean`](ComparatorChallenges/AndersonFiniteCore.lean).
Throughout, $\operatorname{Im}D=(D-D^*)/(2i)$, $Y$ is a real port matrix, $`H^\#`$ is real symmetric, $E$ is real,
$`\mathscr L=H^\#-E-iYY^\top`$ is the site matrix, $G$ is a two-sided inverse of $\mathscr L$, and $S=\mathbf 1+2iY^\top GY$.
Numbers are those of the paper (see [Paper and references](#paper-and-references)).

- **Lemma 3.1 (absorption identities, `mat:ward`).** For any invertible matrix $L$ with inverse $G$ and
  $W=-\operatorname{Im}L$: $\operatorname{Im}G=G^*WG=GWG^*$ (`AndersonAudit.ward_general`; the paper's
  hypothesis $W\ge YY^\top$ is not needed). If moreover $W\ge YY^\top$, then
  $\lVert Y^\top GYa\rVert^2\le\operatorname{Im}(a^*Y^\top GYa)$ for every $a$ and $\lVert Y^\top GY\rVert\le 1$
  (`contraction_ineq`, `contraction_norm_le_one`). For the physical system $\mathscr L$, $S$ is symmetric and
  unitary (`scattering_symm`, `scattering_unitary`).
- **Lemma 3.2 (common-phase closure, `mat:closure`).** With the ports split as $Y=[Y_R\mid Y_C]$ and
  $`S=\begin{pmatrix}A&T\\T^\top&B\end{pmatrix}`$, if the closed site matrix $\mathscr L+(w+i)Y_CY_C^\top$ ($w$ real)
  is invertible, then $\mathbf 1-zB$ is invertible and the retained-port scattering matrix is
  $A+Tz(\mathbf 1-zB)^{-1}T^\top$, $z=\frac{w+i}{w-i}$ (`AndersonAudit.closure_formula`).
- **Lemma 3.3 (the exact identity in its proof, `mat:energy-closure`) and equation (3.5).** For real $f$,
  $F=\operatorname{diag}(f)$, $\mathcal Q(M)=\operatorname{tr}(F^2-FMFM^*)$ and a symmetric matrix $A$:
  $`\mathcal Q(A+\gamma uu^\top)-\mathcal Q(A)=-2\operatorname{Re}(\gamma\,u^\top FA^*Fu)-|\gamma|^2(u^*Fu)^2`$
  (`AndersonAudit.energy_closure`); and for unitary $S$,
  $\mathcal Q(S)=\frac12\sum_{a,j}|S_{ja}|^2(f_j-f_a)^2$ (`energy_trace`).
- **Equation (10.15) (endpoint identity, `boot:endpoint-identity`).** For two probes of strength $\tau$ at sites
  $x\ne y$, with $G^0$ a right inverse of $L_0$, $`g=G^0|_{\{x,y\}}`$, $P$ the projection onto $`\{x,y\}`$ and $G$ a right
  inverse of $L_0-i\tau P$: $`2i\tau\,G^0_{xy}=S_{xy}\det(\mathbf 1-i\tau g)`$ with $`S=\mathbf 1+2i\tau\,G|_{\{x,y\}}`$
  (`AndersonAudit.endpoint_identity`), the multiplied-out form of
  $G^0_{xy}=\frac{S_{xy}}{2i\tau}\det(\mathbf 1-i\tau g)$.

The remaining theorems are the steps toward these. The [verification page](docs/scope.md) prints every Lean type
beside the paper's sentence, with a fidelity verdict for each (including where the Lean statement is stronger than
the paper's, and which hypotheses it does not use).

> [!IMPORTANT]
> **Not proved here.** Nothing in this repository verifies the paper's main theorem (Theorem 1.1: pure-point
> spectrum of the two-dimensional Anderson model at every positive disorder). Not formalized: `mat:cutoff`
> (Lemma 3.4), `mat:weak` (Lemma 3.5), `mat:phase` (Lemma 3.6), the conditional inequality (3.7) of Lemma 3.3,
> the Schur-complement and analyticity assertions of Lemmas 3.1-3.2, and every analytic, probabilistic or
> multiscale part of the paper (Sections 4-11 apart from equation (10.15)), that is, everything that carries
> the localization claim. See [Not formalized](docs/scope.md#not-formalized-and-why).

## Paper and references

OpenAI, *Pure-Point Spectrum for the Two-Dimensional Anderson Model at Every Positive Disorder*, OpenAI Math
Release preprint, September 23, 2026; openai/math family 261 (called P2 in [`claims.yaml`](claims.yaml)).
Source and PDF at [openai/math, commit `adc7f124`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026)
(`paper.pdf` SHA-256 `17487e3a2720b36fd7970cb6027726d8a21843bded4e1156ba998902ed96c098`).

The paper is by OpenAI's math project, not by Le Chen; this repository formalizes a small, finite-dimensional part
of it. Lemma, equation and label names above are the paper's, at that commit.

## Build and verify

Toolchain Lean `v4.34.1` ([`lean-toolchain`](lean-toolchain)); Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` ([`lake-manifest.json`](lake-manifest.json)).

```sh
git clone https://github.com/chenle02/anderson-finite-core-lean.git
cd anderson-finite-core-lean
lake exe cache get
lake build
```

`lake build` builds both default targets: the library `AndersonAudit` (the proofs) and `ComparatorChallenges`
(the trusted statements). `lake env lean AndersonAudit/Axioms.lean` prints the axioms of all 21 theorems.

To use it from another Lake project:

```toml
[[require]]
name = "AndersonAudit"
git = "https://github.com/chenle02/anderson-finite-core-lean.git"
```

then `import AndersonAudit.FiniteCore`.

## Trust and axioms

The build check recorded at commit `6b2c9d12f616` found `sorry` count 0 in `AndersonAudit/` and the axioms
`propext`, `Classical.choice` and `Quot.sound` only, and re-checked `AndersonAudit.FiniteCore` by kernel replay
(`leanchecker`). The comparator, with an independent kernel enabled, confirmed, at the same commit, that the 21 proofs prove exactly the statements in
[`ComparatorChallenges/AndersonFiniteCore.lean`](ComparatorChallenges/AndersonFiniteCore.lean), with no definition
holes (`definition_names: []`) and the same three permitted axioms; the configuration is
[`comparator/config-finite-core.json`](comparator/config-finite-core.json). The `sorry` bodies in the Challenge file
are intentional: it holds the statements only. Receipts: [`.lean-receipts/`](.lean-receipts/); commits after
`6b2c9d12f616` change documentation, CI and metadata only.

These checks establish the stated finite-dimensional identities. They do not establish that the identities are
the ones the paper's argument needs, or anything about the paper's main theorem.

## Built with lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
The receipts under [`.lean-receipts/`](.lean-receipts/) bind the build check and the statement comparison to a
source commit; [`claims.yaml`](claims.yaml) lists the 21 claims with their paper anchors.

## Authors and AI disclosure

Le Chen, Associate Professor, Department of Mathematics and Statistics, Auburn University.
The paper formalized here is by OpenAI ([openai/math](https://github.com/openai/math)).

Developed with AI assistance (Anthropic Claude) under Le Chen's direction; the fidelity review was done by the same
AI workflow, not by a human referee.

Released under Apache-2.0 ([LICENSE](LICENSE)); citation metadata in [CITATION.cff](CITATION.cff).
