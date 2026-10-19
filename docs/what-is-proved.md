# What is proved

<!-- Hand-written. Lean statements copied verbatim from AndersonAudit/FiniteCore.lean at commit 6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e (the commit the build receipt binds). Re-copy them when the receipts move. -->

This repository proves, in Lean 4 with Mathlib, the finite-dimensional matrix identities that one paper on
the two-dimensional Anderson model uses: the absorption identities and the symmetry and unitarity of the
scattering matrix, the common-phase closure formula, the exact identity behind the single-port energy
comparison, the trace form of the Dirichlet energy, and the two-probe endpoint identity. It does **not**
formalize the paper's localization theorem or any analytic, probabilistic or multiscale step.

Each card below is one result of the paper. The typeset statement is a transcription of the Lean statement
(every hypothesis and every conclusion), written in the paper's notation; Lean checks only the Lean
statement. The line-by-line ledger (every Lean type beside the paper's sentence, with a fidelity verdict,
including the 12 supporting theorems not shown here) is the [scope and fidelity page](scope.md).

## Notation

All matrices are finite: rows and columns are indexed by finite types (sites $n$, ports $m$, retained ports
$r$, closed ports $c$). Complex matrices are matrices over $\mathbb C$; "real" means the entries are real
(Lean: a matrix over $\mathbb R$, coerced entrywise by `cplx`).

- $M^\top$ is the transpose, $`M^*`$ the conjugate transpose (Lean `Mᵀ`, `Mᴴ`), as in the paper (setup section).
- $`\operatorname{Im}D=(D-D^*)/(2i)`$ is the Hermitian imaginary part (Lean `imPart D = (2 * I)⁻¹ • (D - Dᴴ)`).
- For a real symmetric $`H^\#`$ (Lean `H`, with `Hᵀ = H`), a real energy $E$ and a real port matrix $Y$, the
  site matrix is $`\mathscr L=H^\#-E-iYY^\top`$ (Lean `siteMatrix H E Y`).
- For a complex matrix $G$ (in the theorems: a two-sided inverse of the site matrix, $\mathscr LG=G\mathscr L=\mathbf 1$),
  the scattering matrix is $S=\mathbf 1+2iY^\top GY$ (Lean `scatteringMatrix Y G`), and
  $`Y_1^\top GY_2`$ is the port response block (Lean `portResponse Y₁ G Y₂`).
- $`[Y_R\mid Y_C]`$ is the port matrix with retained columns $Y_R$ and closed columns $Y_C$ (Lean `fromCols YR YC`).
- For real data $f$ on the ports, $F=\operatorname{diag}(f)$ (Lean `realDiag f`) and
  $`\mathcal Q(M)=\operatorname{tr}(F^2-FMFM^*)`$ (Lean `energyQ f M`, a complex number).
- For sites $x\ne y$: $P$ is the diagonal projection onto $`\{x,y\}`$ (Lean `twoSiteProj x y`), and
  $`M|_{\{x,y\}}`$ is the $2\times2$ compression of $M$ with rows and columns ordered $(x,y)$ (Lean `pairRestrict M x y`;
  its entry `0 1` is $M_{xy}$).
- $\lVert v\rVert$ is the Euclidean norm of a vector and $\lVert M\rVert$ the induced $\ell^2$ operator norm
  (Lean `Matrix.Norms.L2Operator`), the paper's default norm.
- The inverse of the site matrix is never written as Lean's `⁻¹` in a hypothesis: it is a matrix `G` with
  `𝓛 * G = 1` and `G * 𝓛 = 1`.

## Main results

All results are from OpenAI, *Pure-Point Spectrum for the Two-Dimensional Anderson Model at Every Positive
Disorder* (2026) [[1]](#references), at commit `adc7f124` of openai/math.

| # | Result | Reference | Lean | Status |
|---|---|---|---|---|
| 1 | [Absorption identity](#1-absorption-identity) | [1], Lemma 3.1, eq. (3.2) | `ward_general` | proved |
| 2 | [Port response is a contraction](#2-port-response-is-a-contraction) | [1], Lemma 3.1, eq. (3.3) | `contraction_ineq`, `contraction_norm_le_one` | proved |
| 3 | [The scattering matrix is symmetric and unitary](#3-the-scattering-matrix-is-symmetric-and-unitary) | [1], Lemma 3.1 | `scattering_symm`, `scattering_unitary` | proved |
| 4 | [Common-phase closure formula](#4-common-phase-closure-formula) | [1], Lemma 3.2, eq. (3.6) | `closure_formula` | proved |
| 5 | [Single-port closure: the exact identity](#5-single-port-closure-the-exact-identity) | [1], proof of Lemma 3.3 | `energy_closure` | proved (identity only; inequality (3.7) not formalized) |
| 6 | [Trace form of the Dirichlet energy](#6-trace-form-of-the-dirichlet-energy) | [1], eq. (3.5) | `energy_trace` | proved (scalar data) |
| 7 | [Two-probe endpoint identity](#7-two-probe-endpoint-identity) | [1], eq. (10.15) | `endpoint_identity` | proved |

Lean names are in the namespace `AndersonAudit`.

### 1. Absorption identity

The imaginary part of an inverse is the inverse sandwiched around the absorption.

**Statement.** Let $L,G$ be complex square matrices with $LG=\mathbf 1$ and $GL=\mathbf 1$, and put
$W=-\operatorname{Im}L$. Then

```math
\operatorname{Im}G=G^*WG
\qquad\text{and}\qquad
\operatorname{Im}G=GWG^* .
```

**Reference.** [1], Lemma 3.1 (Absorption identities, label `mat:ward`), equation (3.2) (`mat:ward-identity`);
[LaTeX source, `matrix.tex` line 48](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/build/sections/matrix.tex#L48).
Lemma and equation numbers checked against the LaTeX source (see [How the numbers were checked](#how-the-numbers-were-checked)).

**Compared with the reference.** The paper assumes $L=\mathscr L$ is the site matrix and
$W\ge YY^\top$; the Lean statement assumes only that $L$ is invertible (no hypothesis on $W$, no $Y$). It is
stronger than the paper's display (3.2) and implies it.

**Lean.** [`AndersonAudit.ward_general`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L97)

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem ward_general {n : Type} [Fintype n] [DecidableEq n] {L G : Matrix n n ℂ}
    (hLG : L * G = 1) (hGL : G * L = 1) :
    imPart G = Gᴴ * (-imPart L) * G ∧ imPart G = G * (-imPart L) * Gᴴ := by
  -- proof: see the source link
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved |
| Sorry count | 0 (build receipt, scan of `AndersonAudit/`) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt `axioms`; `#print axioms` log `gate-axioms.txt` at commit `6b2c9d12f616`) |
| Statement comparison | comparator receipt `.lean-receipts/6b2c9d12f616-comparator.json` at `6b2c9d12f616`: `result: pass`, the proof proves the statement in `ComparatorChallenges/AndersonFiniteCore.lean`; permitted axioms `propext`, `Quot.sound`, `Classical.choice`; Lean kernel and nanoda kernel both accept |
| Definitions judged by a person | not recorded (no `lean-pkg-signoff.json`; comparator `definition_names: []`) |
| Evidence commit | `6b2c9d12f616` (receipts in [`.lean-receipts/`](../.lean-receipts/)) |
| Human review | not recorded (no `formalization.yaml`); the README states the fidelity review was done by an AI workflow, not a human referee |
| Not covered | the Schur-complement assertions of Lemma 3.1 |
| Signed off | build check (receipt dated 2026-10-14) and comparator (receipt dated 2026-10-17); lean-pkg version not recorded in the receipts (mechanical checks only) |

</details>

### 2. Port response is a contraction

If the absorption dominates the ports, the port response $K=Y^\top GY$ is a contraction.

**Statement.** Let $L,G$ be complex square matrices with $LG=GL=\mathbf 1$, let $Y$ be a real $n\times m$
matrix, and assume $-\operatorname{Im}L-YY^\top$ is positive semidefinite (that is, $W=-\operatorname{Im}L\ge YY^\top$).
Then, for every $a\in\mathbb C^m$,

```math
\lVert Y^\top GYa\rVert^2\le\operatorname{Im}\bigl(a^*Y^\top GYa\bigr),
\qquad\text{and}\qquad
\lVert Y^\top GY\rVert\le 1 .
```

**Reference.** [1], Lemma 3.1 (`mat:ward`), equation (3.3) (`mat:ward-contraction`);
[LaTeX source, `matrix.tex` line 48](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/build/sections/matrix.tex#L48).
Numbers checked against the LaTeX source.

**Compared with the reference.** Same hypotheses and conclusions, except that $L$ is any invertible complex
matrix (the paper: the site matrix $\mathscr L$). In Lean, $\lVert v\rVert^2$ is written
$`\operatorname{Re}(v^*v)`$ and the matrix norm is the $\ell^2$ operator norm.

**Lean.** [`AndersonAudit.contraction_ineq`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L210) ·
[`AndersonAudit.contraction_norm_le_one`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L264)

<details markdown="1">
<summary>Lean statements (copy with the button on the code block)</summary>

```lean
theorem contraction_ineq {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    {L G : Matrix n n ℂ} (hLG : L * G = 1) (hGL : G * L = 1) (Y : Matrix n m ℝ)
    (hW : (-imPart L - cplx Y * (cplx Y)ᵀ).PosSemidef) (a : m → ℂ) :
    (star (((cplx Y)ᵀ * G * cplx Y) *ᵥ a) ⬝ᵥ (((cplx Y)ᵀ * G * cplx Y) *ᵥ a)).re ≤
      (star a ⬝ᵥ (((cplx Y)ᵀ * G * cplx Y) *ᵥ a)).im := by
  -- proof: see the source link

open scoped Matrix.Norms.L2Operator in
theorem contraction_norm_le_one {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] {L G : Matrix n n ℂ} (hLG : L * G = 1) (hGL : G * L = 1) (Y : Matrix n m ℝ)
    (hW : (-imPart L - cplx Y * (cplx Y)ᵀ).PosSemidef) :
    ‖(cplx Y)ᵀ * G * cplx Y‖ ≤ 1 := by
  -- proof: see the source link
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved |
| Sorry count | 0 (build receipt) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` for both theorems (build receipt; `gate-axioms.txt` at `6b2c9d12f616`) |
| Statement comparison | comparator receipt `.lean-receipts/6b2c9d12f616-comparator.json` at `6b2c9d12f616`: `result: pass` for both against `ComparatorChallenges/AndersonFiniteCore.lean` |
| Definitions judged by a person | not recorded (comparator `definition_names: []`) |
| Evidence commit | `6b2c9d12f616` |
| Human review | not recorded (AI fidelity review only, per the README) |
| Not covered | the intermediate bound $`\operatorname{Im}(a^*Ka)\le\lVert a\rVert\,\lVert Ka\rVert`$ is used inside the proof, not stated |
| Signed off | build check (2026-10-14) and comparator (2026-10-17); lean-pkg version not recorded (mechanical checks only) |

</details>

### 3. The scattering matrix is symmetric and unitary

For the physical system, time reversal gives $S^\top=S$ and absorption balance gives unitarity.

**Statement.** Let $`H^\#`$ be a real symmetric $n\times n$ matrix, $E$ real, $Y$ a real $n\times m$ matrix,
$`\mathscr L=H^\#-E-iYY^\top`$, and $G$ a complex matrix with $\mathscr LG=G\mathscr L=\mathbf 1$. Then
$S=\mathbf 1+2iY^\top GY$ satisfies

```math
S^\top=S,\qquad S^*S=\mathbf 1,\qquad SS^*=\mathbf 1 .
```

**Reference.** [1], Lemma 3.1 (`mat:ward`), the sentence "For the physical system in (3.1), $S$ is
symmetric and unitary" (no equation number);
[LaTeX source, `matrix.tex` line 59](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/build/sections/matrix.tex#L59).
Numbers checked against the LaTeX source.

**Compared with the reference.** Same hypotheses and conclusion. The paper's port columns are
$`\sqrt\sigma e_x`$; the Lean statement allows any real $Y$ (the paper says the identities apply to any real
rectangular $Y$). The symmetry proof uses only $\mathscr LG=\mathbf 1$.

**Lean.** [`AndersonAudit.scattering_symm`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L158) ·
[`AndersonAudit.scattering_unitary`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L173)

<details markdown="1">
<summary>Lean statements (copy with the button on the code block)</summary>

```lean
theorem scattering_symm {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E Y * G = 1) (_hGL : G * siteMatrix H E Y = 1) :
    (scatteringMatrix Y G)ᵀ = scatteringMatrix Y G := by
  -- proof: see the source link

theorem scattering_unitary {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E Y * G = 1) (hGL : G * siteMatrix H E Y = 1) :
    (scatteringMatrix Y G)ᴴ * scatteringMatrix Y G = 1 ∧
      scatteringMatrix Y G * (scatteringMatrix Y G)ᴴ = 1 := by
  -- proof: see the source link
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved |
| Sorry count | 0 (build receipt) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` for both theorems (build receipt; `gate-axioms.txt` at `6b2c9d12f616`) |
| Statement comparison | comparator receipt `.lean-receipts/6b2c9d12f616-comparator.json` at `6b2c9d12f616`: `result: pass` for both |
| Definitions judged by a person | not recorded (comparator `definition_names: []`) |
| Evidence commit | `6b2c9d12f616` |
| Human review | not recorded (AI fidelity review only, per the README) |
| Not covered | the Schur-complement and passivity assertions in the rest of Lemma 3.1 |
| Signed off | build check (2026-10-14) and comparator (2026-10-17); lean-pkg version not recorded (mechanical checks only) |

</details>

### 4. Common-phase closure formula

Closing a set of ports with a common real shift $w$ changes the retained-port scattering matrix by a
rational (Woodbury) formula in $z=(w+i)/(w-i)$.

**Statement.** Let $`H^\#`$ be a real symmetric $n\times n$ matrix, $E$ and $w$ real, $Y_R$ (an $n\times r$
matrix) and $Y_C$ (an $n\times c$ matrix) real, $\mathscr L$ the site matrix of $`(H^\#,E,[Y_R\mid Y_C])`$, $G$ a
two-sided inverse of $\mathscr L$, and $G_w$ a two-sided inverse of the closed site matrix
$`\mathscr L_w=\mathscr L+(w+i)Y_CY_C^\top`$. Put

```math
z=\frac{w+i}{w-i},\qquad
A=\mathbf 1+2iY_R^\top GY_R,\qquad
T=2iY_R^\top GY_C,\qquad
B=\mathbf 1+2iY_C^\top GY_C .
```

Then $\mathbf 1-zB$ is invertible and the scattering matrix of the closed system on the retained ports is

```math
\mathbf 1+2iY_R^\top G_wY_R=A+Tz(\mathbf 1-zB)^{-1}T^\top .
```

**Reference.** [1], Lemma 3.2 (Common-phase closure, `mat:closure`), equation (3.6)
(`mat:closure-formula`);
[LaTeX source, `matrix.tex` line 129](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/build/sections/matrix.tex#L129).
Numbers checked against the LaTeX source.

**Compared with the reference.** The paper writes $`S=\begin{pmatrix}A&T\\T^\top&B\end{pmatrix}`$ and describes
the closed system as "close every port in $C$ and add the real shift $`w\sigma_j`$"; its proof writes the closed
site matrix as $`\mathscr L_w`$, which is the hypothesis used here (the supporting theorem `closed_siteMatrix`
shows $`\mathscr L_w`$ is the site matrix of $`(H^\#+wY_CY_C^\top,E,Y_R)`$). The paper says "where the resulting
inverse exists"; Lean assumes $G_w$ exists and **derives** the invertibility of $\mathbf 1-zB$. Not formalized:
"the right-hand side is analytic for $|z|<1$" and the proof's remarks on removable singularities, finitely
many singular closing values and contractivity of $B$.

**Lean.** [`AndersonAudit.closure_formula`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L320)

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem closure_formula {n r c : Type} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c] {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ)
    (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) (w : ℝ) {G Gw : Matrix n n ℂ}
    (hLG : siteMatrix H E (fromCols YR YC) * G = 1)
    (hGL : G * siteMatrix H E (fromCols YR YC) = 1)
    (hLGw : (siteMatrix H E (fromCols YR YC) + ((w : ℂ) + I) • (cplx YC * (cplx YC)ᵀ)) * Gw = 1)
    (hGLw : Gw * (siteMatrix H E (fromCols YR YC) + ((w : ℂ) + I) • (cplx YC * (cplx YC)ᵀ)) = 1) :
    IsUnit (1 - (((w : ℂ) + I) / ((w : ℂ) - I)) • (1 + (2 * I) • portResponse YC G YC)) ∧
      scatteringMatrix YR Gw =
        (1 + (2 * I) • portResponse YR G YR) +
          (((w : ℂ) + I) / ((w : ℂ) - I)) •
            ((2 * I) • portResponse YR G YC *
              (1 - (((w : ℂ) + I) / ((w : ℂ) - I)) • (1 + (2 * I) • portResponse YC G YC))⁻¹ *
              ((2 * I) • portResponse YR G YC)ᵀ) := by
  -- proof: see the source link
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved |
| Sorry count | 0 (build receipt) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt; `gate-axioms.txt` at `6b2c9d12f616`) |
| Statement comparison | comparator receipt `.lean-receipts/6b2c9d12f616-comparator.json` at `6b2c9d12f616`: `result: pass` |
| Definitions judged by a person | not recorded (comparator `definition_names: []`) |
| Evidence commit | `6b2c9d12f616` |
| Human review | not recorded (AI fidelity review only, per the README) |
| Not covered | analyticity in $z$, removable singularities, finiteness of singular closing values, contractivity of $B$ |
| Signed off | build check (2026-10-14) and comparator (2026-10-17); lean-pkg version not recorded (mechanical checks only) |

</details>

### 5. Single-port closure: the exact identity

The energy change under a rank-one symmetric update is an explicit cross term minus a perfect square.

**Statement.** Let $f$ be real data on a finite port set, $F=\operatorname{diag}(f)$, $A$ a complex square
matrix with $A^\top=A$, $u$ a complex vector and $\gamma\in\mathbb C$. Then, as an identity of complex numbers,

```math
\mathcal Q\bigl(A+\gamma uu^\top\bigr)-\mathcal Q(A)
=-2\operatorname{Re}\bigl(\gamma\,u^\top FA^*Fu\bigr)-|\gamma|^2\,(u^*Fu)^2,
\qquad
\mathcal Q(M)=\operatorname{tr}(F^2-FMFM^*).
```

**Reference.** [1], the "exact identity" displayed in the proof of Lemma 3.3 (Conditional single-port
comparison, `mat:energy-closure`; the identity itself is unnumbered);
[LaTeX source, `matrix.tex` line 163](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/build/sections/matrix.tex#L163).
Numbers checked against the LaTeX source.

**Compared with the reference.** The paper states the identity for $`A=S_{\widehat a,\widehat a}`$,
$`u=S_{\widehat a,a}`$, $\gamma=z/(1-zb)$ and data shifted so that $f_a=0$, in the form
$`\mathcal Q_{S_z}(f_{\widehat a})-\mathcal Q_S(f)`$; the Lean statement is the identity for arbitrary $A$, $u$,
$\gamma$ in the trace form $\mathcal Q$. The reduction $`\mathcal Q_S(f)=\mathcal Q(A)`$ after the shift is not
formalized. The hypothesis $A^\top=A$ is stated but not used by the proof. **Not formalized:** the lemma's
actual statement, the conditional inequality (3.7), and the bound $`|u^\top FA^*Fu|\le\lVert Fu\rVert^2`$.

**Lean.** [`AndersonAudit.energy_closure`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L474)

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem energy_closure {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ)
    (A : Matrix r r ℂ) (_hA : Aᵀ = A) (u : r → ℂ) (γ : ℂ) :
    energyQ f (A + γ • vecMulVec u u) - energyQ f A =
      -2 * ((γ * (u ⬝ᵥ ((realDiag f * Aᴴ * realDiag f) *ᵥ u))).re : ℂ) -
        (Complex.normSq γ : ℂ) * (star u ⬝ᵥ (realDiag f *ᵥ u)) ^ 2 := by
  -- proof: see the source link
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (the identity only) |
| Sorry count | 0 (build receipt) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt; `gate-axioms.txt` at `6b2c9d12f616`) |
| Statement comparison | comparator receipt `.lean-receipts/6b2c9d12f616-comparator.json` at `6b2c9d12f616`: `result: pass` |
| Definitions judged by a person | not recorded (comparator `definition_names: []`) |
| Evidence commit | `6b2c9d12f616` |
| Human review | not recorded (AI fidelity review only, per the README) |
| Not covered | Lemma 3.3 itself (the conditional inequality (3.7)), the contraction bound, vector data |
| Signed off | build check (2026-10-14) and comparator (2026-10-17); lean-pkg version not recorded (mechanical checks only) |

</details>

### 6. Trace form of the Dirichlet energy

For a unitary scattering matrix, the Dirichlet energy of scalar data is a trace.

**Statement.** Let $f$ be real data on a finite port set, $F=\operatorname{diag}(f)$, and $S$ a complex
square matrix with $`S^*S=\mathbf 1`$ and $`SS^*=\mathbf 1`$. Then

```math
\frac12\sum_{a,j}|S_{ja}|^2\,(f_j-f_a)^2=\operatorname{tr}\bigl(F^2-FSFS^*\bigr).
```

**Reference.** [1], equation (3.5) (`mat:energy-trace`), with the energy $`\mathcal Q_S(f)`$ of equation
(3.4) (`mat:energies`);
[LaTeX source, `matrix.tex` line 123](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/build/sections/matrix.tex#L123).
Numbers checked against the LaTeX source.

**Compared with the reference.** Same hypothesis (unitarity) and conclusion, for scalar data. The
paper's extension to vector data ("one sums this identity over real components") is not formalized.

**Lean.** [`AndersonAudit.energy_trace`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L504)

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem energy_trace {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (S : Matrix r r ℂ)
    (hU : Sᴴ * S = 1) (hU' : S * Sᴴ = 1) :
    (((1 / 2 : ℝ) * ∑ a, ∑ j, Complex.normSq (S j a) * (f j - f a) ^ 2 : ℝ) : ℂ) =
      energyQ f S := by
  -- proof: see the source link
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved (scalar data) |
| Sorry count | 0 (build receipt) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt; `gate-axioms.txt` at `6b2c9d12f616`) |
| Statement comparison | comparator receipt `.lean-receipts/6b2c9d12f616-comparator.json` at `6b2c9d12f616`: `result: pass` |
| Definitions judged by a person | not recorded (comparator `definition_names: []`) |
| Evidence commit | `6b2c9d12f616` |
| Human review | not recorded (AI fidelity review only, per the README) |
| Not covered | vector-valued data; the single-port energy $`\mathcal M_a(f)`$ of (3.4) |
| Signed off | build check (2026-10-14) and comparator (2026-10-17); lean-pkg version not recorded (mechanical checks only) |

</details>

### 7. Two-probe endpoint identity

Removing two endpoint probes: the free Green function entry is the probed scattering entry times a
$2\times2$ determinant.

**Statement.** Let $L_0$, $G^0$, $G$ be complex $n\times n$ matrices, $x\ne y$ two sites, $\tau$ real, and
$P$ the projection onto $`\{x,y\}`$. Assume $`L_0G^0=\mathbf 1`$ and $`(L_0-i\tau P)G=\mathbf 1`$. Put
$`g=G^0|_{\{x,y\}}`$ and $`S=\mathbf 1+2i\tau\,G|_{\{x,y\}}`$. Then

```math
2i\tau\,G^0_{xy}=S_{xy}\,\det(\mathbf 1-i\tau g).
```

**Reference.** [1], equation (10.15) (`boot:endpoint-identity`), in Section 10, "Removing the two endpoint
probes";
[LaTeX source, `bootstrap.tex` line 531](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/build/sections/bootstrap.tex#L531).
Numbers checked against the LaTeX source.

**Compared with the reference.** The paper writes $`G^0_{xy}=\frac{S_{xy}}{2i\tau}\det(1-i\tau g)`$ with
$G^0=(H_N-E)^{-1}$ and constant-strength probes $\tau>0$; Lean states the form multiplied by $2i\tau$ (equivalent
for $\tau\ne0$), for any $L_0$ with a right inverse $G^0$ and any real $\tau$, and needs only right inverses.
Lean defines $S$ directly as $`\mathbf 1+2i\tau\,G|_{\{x,y\}}`$; the supporting theorem `endpoint_ports` shows this
is the scattering matrix of the two probe ports $`\sqrt\tau e_x,\sqrt\tau e_y`$ when $\tau\ge0$. The paper's
intermediate steps (damped compression, adjugate formula) are the supporting theorems
`endpoint_resolvent_step`, `endpoint_adjugate_entry` and `endpoint_damped_entry`. Not formalized: the moment
bounds that follow (10.15).

**Lean.** [`AndersonAudit.endpoint_identity`](https://github.com/chenle02/anderson-finite-core-lean/blob/6b2c9d12f6166ca98c4c750c77e83fbbbab1ed7e/AndersonAudit/FiniteCore.lean#L621)

<details markdown="1">
<summary>Lean statement (copy with the button on the code block)</summary>

```lean
theorem endpoint_identity {n : Type} [Fintype n] [DecidableEq n] {L₀ G₀ G : Matrix n n ℂ}
    {x y : n} (hxy : x ≠ y) (τ : ℝ) (h₀ : L₀ * G₀ = 1)
    (h : (L₀ - (I * τ) • twoSiteProj x y) * G = 1) :
    G₀ x y * (2 * I * τ) =
      (1 + (2 * I * τ) • pairRestrict G x y) 0 1 * (1 - (I * τ) • pairRestrict G₀ x y).det := by
  -- proof: see the source link
```

</details>

<details markdown="1">
<summary>Sign-off</summary>

| Field | Value |
|---|---|
| Status | proved |
| Sorry count | 0 (build receipt) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` (build receipt; `gate-axioms.txt` at `6b2c9d12f616`) |
| Statement comparison | comparator receipt `.lean-receipts/6b2c9d12f616-comparator.json` at `6b2c9d12f616`: `result: pass` |
| Definitions judged by a person | not recorded (comparator `definition_names: []`) |
| Evidence commit | `6b2c9d12f616` |
| Human review | not recorded (AI fidelity review only, per the README) |
| Not covered | the moment bounds after (10.15) and every probabilistic statement of Section 10 |
| Signed off | build check (2026-10-14) and comparator (2026-10-17); lean-pkg version not recorded (mechanical checks only) |

</details>

## Not proved here

- **The paper's main theorem** (Theorem 1.1: for each $h>0$, almost surely $H_v$ has pure-point spectrum,
  with spectrum $[-4-h,4+h]$). Nothing in this repository verifies it.
- Lemma 3.3 as stated (the conditional inequality (3.7)); Lemma 3.4 (`mat:cutoff`), Lemma 3.5 (`mat:weak`),
  Lemma 3.6 (`mat:phase`).
- The Schur-complement and passivity assertions of Lemma 3.1, the kernel remark after it, and the
  analyticity, removable-singularity, finitely-many-singular-values and contractivity sentences of Lemma 3.2.
- The vector-data versions of (3.5) and of Lemma 3.3.
- Every analytic, probabilistic or multiscale part of Sections 4 to 11, apart from equation (10.15): that is,
  everything that carries the localization claim.

The full list, with the reasons, is in [Not formalized](scope.md#not-formalized-and-why).

<details markdown="1">
<summary>Lean implementation notes</summary>

- **Inverses.** The resolvent $G=\mathscr L^{-1}$ is a matrix variable with `𝓛 * G = 1` (and, where stated,
  `G * 𝓛 = 1`), never Lean's totalized `⁻¹`, so no junk value of a singular inverse enters a hypothesis.
  The only `⁻¹` in a main statement is $(\mathbf 1-zB)^{-1}$ in card 4, whose invertibility is a proved
  conclusion.
- **Real matrices.** `H`, `Y`, `YR`, `YC` are real matrices; `cplx` coerces them entrywise to complex
  matrices. `Hᵀ = H` is the paper's "real symmetric".
- **Loewner order.** $W\ge YY^\top$ is `(W - cplx Y * (cplx Y)ᵀ).PosSemidef`.
- **Bilinear vs sesquilinear.** `u ⬝ᵥ (M *ᵥ u)` is $u^\top Mu$ (no conjugation); `star u ⬝ᵥ (M *ᵥ u)`
  is $`u^*Mu`$. `Complex.normSq γ` is $|\gamma|^2$.
- **Energy.** `energyQ f M` is the trace $`\operatorname{tr}(F^2-FMFM^*)`$, a complex number; it equals the
  paper's $`\mathcal Q_S(f)`$ for unitary $S$ by card 6.
- **Norm.** `contraction_norm_le_one` opens `Matrix.Norms.L2Operator` for its statement, so `‖·‖` is the
  $\ell^2$ operator norm; the link points at the `theorem` line, two lines below the `open ... in`.
- **Unused hypotheses (kept on purpose).** `_hGL` in `scattering_symm` and `_hA` in `energy_closure` are not
  used by the proofs; they keep the statements in the paper's setting.
- **Supporting theorems.** The other 12 theorems checked by the comparator (`ward_physical`,
  `contraction_identity`, `scattering_blocks`, `scattering_blocks_symm`, `closed_siteMatrix`,
  `energy_closure_general`, `quadForm_real`, `energy_closure_scattering`, `endpoint_ports`,
  `endpoint_resolvent_step`, `endpoint_adjugate_entry`, `endpoint_damped_entry`) are the steps and bridges;
  each is printed with its paper anchor and verdict on the [scope page](scope.md#theorems).

</details>

## How this was checked

The build check at commit `6b2c9d12f616` (receipt dated 2026-10-14) ran `lake build AndersonAudit
ComparatorChallenges`, `#print axioms` on all 21 theorems, kernel replay of `AndersonAudit.FiniteCore` with
`leanchecker`, and a `sorry`/`admit` scan of `AndersonAudit/` (0 hits). The comparator (receipt dated
2026-10-17, same commit), with the nanoda kernel enabled, confirmed that the 21 proofs prove exactly the
statements of [`ComparatorChallenges/AndersonFiniteCore.lean`](../ComparatorChallenges/AndersonFiniteCore.lean)
using only `propext`, `Quot.sound`, `Classical.choice`; configuration
[`comparator/config-finite-core.json`](../comparator/config-finite-core.json). Receipts:
[`.lean-receipts/`](../.lean-receipts/). Ledger: [scope and fidelity page](scope.md). To reproduce, see
[Build and verify](../README.md#build-and-verify).

### How the numbers were checked

Lemma and equation numbers were computed from the paper's LaTeX source at openai/math commit `adc7f124`
(`build/paper.tex` and `build/sections/*.tex`), not from the PDF: `paper.tex` sets
`\numberwithin{equation}{section}` and numbers lemmas with the theorem counter within sections; the
sections are input in the order introduction, setup, matrix, resonant, impedance, transmission, hierarchy,
screening, vanishing, bootstrap, spectral, so `matrix.tex` is Section 3 and `bootstrap.tex` is Section 10.
In `matrix.tex`, the theorem-type environments are, in order, `mat:ward`, `mat:closure`,
`mat:energy-closure` (Lemmas 3.1 to 3.3), and the numbered equations are `mat:response`, `mat:ward-identity`,
`mat:ward-contraction`, `mat:energies`, `mat:energy-trace`, `mat:closure-formula`,
`mat:conditional-comparison` ((3.1) to (3.7)). In `bootstrap.tex`, `boot:endpoint-identity` is the 15th
numbered equation, (10.15). Page numbers were not checked.

## References

1. OpenAI, *Pure-Point Spectrum for the Two-Dimensional Anderson Model at Every Positive Disorder*, OpenAI
   Math Release preprint, September 23, 2026 (openai/math family 261). Source and PDF at
   [openai/math, commit `adc7f124`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026)
   (`paper.pdf` SHA-256 `17487e3a2720b36fd7970cb6027726d8a21843bded4e1156ba998902ed96c098`). No DOI, arXiv
   or MathSciNet identifier; not in the refdb bibliography, so no citekey or SPDEs-Bib page.
