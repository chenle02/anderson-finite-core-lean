# Verification page: Anderson finite core (Lean)

This page sets each Lean statement beside the sentence of the paper it formalizes, with a fidelity
verdict for each. It is the verification page of this repository; the receipts it relies on are under
[`.lean-receipts/`](../.lean-receipts/).

## Verification at a glance

**How to read this page.** Lean has checked every step of the proofs listed here. It cannot check that
a Lean statement says what the paper says: for each theorem below, read the paper's sentence beside the
printed Lean type, and check that the hypotheses match.

- **Paper:** *Pure-Point Spectrum for the Two-Dimensional Anderson Model at Every Positive Disorder*,
  OpenAI, September 23, 2026; openai/math family 261 (called P2 in `claims.yaml`), at commit
  [`adc7f1241b42e322a6451854ab7e4b4c146bf78a`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026)
  (`paper.pdf` SHA-256 `17487e3a2720b36fd7970cb6027726d8a21843bded4e1156ba998902ed96c098`).
  The paper is not by the author of this repository.
- **Formalized:** the finite-dimensional algebraic identities of Lemma 3.1 (`mat:ward`), Lemma 3.2
  (`mat:closure`), the exact identity in the proof of Lemma 3.3 (`mat:energy-closure`) together with
  equation (3.5) (`mat:energy-trace`), and equation (10.15) (`boot:endpoint-identity`): 21 theorems.
- **Not formalized:** Theorem 1.1 (the localization theorem), the inequality (3.7) of Lemma 3.3,
  Lemmas 3.4-3.6, and Sections 4-11 apart from equation (10.15); see [Not formalized](#not-formalized-and-why).
  **Nothing in this repository verifies the paper's main theorem.**
- **Checks recorded:** the build check at commit `6b2c9d12f616` (`sorry` count 0 in `AndersonAudit/`,
  axioms `propext`, `Quot.sound`, `Classical.choice` only, kernel replay of `AndersonAudit.FiniteCore` with `leanchecker`)
  and a statement comparison (comparator, with an independent kernel) of all 21 theorems against the
  Challenge file at the same commit, with `definition_names: []` and the same three permitted axioms.

Paper anchors `<file>.tex:<line>` refer to the paper's public LaTeX source at that commit,
[`build/sections/`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/build/sections);
lemma and equation numbers are those of the paper's `paper.pdf` at the same commit.

Pins: Lean `leanprover/lean4:v4.34.1`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (and its
pinned transitive dependencies, `lake-manifest.json`). Challenge `ComparatorChallenges/AndersonFiniteCore.{lean,json}`
(`definition_names: []`, permitted axioms exactly `propext`, `Quot.sound`, `Classical.choice`);
solution `AndersonAudit/FiniteCore.lean`; axiom audit `AndersonAudit/Axioms.lean`. Every theorem below
is kernel-checked with axioms `[propext, Classical.choice, Quot.sound]` (no `sorry`, no project axioms).
Printed types: `#check @AndersonAudit.<name>` at the pin (namespace prefix stripped; full list in
[`printed-types.txt`](printed-types.txt)).

**This is the only part of the paper that is formalizable at reasonable cost.** Nothing in this
repository verifies the paper's localization theorem: what is formalized is the finite-dimensional
algebra (identities) that the paper's analytic and multiscale argument consumes.

Fidelity classes: over-claim / under-claim / definitional divergence / anchor mismatch, or faithful.
"Benign strengthening" = the Lean theorem drops a hypothesis the paper carries and is still
kernel-proved; it is not a soundness issue and is listed for transparency. Anchors were re-read at the
cited lines (no anchor mismatch found).

## Trusted definitions (the comparator's definition layer)

| Lean | Paper object | Anchor |
|---|---|---|
| `cplx A` | real matrix as complex matrix | matrix.tex:4-9 |
| `imPart D = (2I)⁻¹ • (D − Dᴴ)` | $\operatorname{Im}D=(D-D^*)/(2i)$ | setup.tex:41 |
| `siteMatrix H E Y = cplx H − E•1 − I•(cplx Y * (cplx Y)ᵀ)` | $`\mathscr L=H^\#-E-iYY^\top`$ | matrix.tex:11 |
| `scatteringMatrix Y G = 1 + (2I)•((cplx Y)ᵀ * G * cplx Y)` | $S=\one+2iY^\top GY$ | matrix.tex:13 |
| `portResponse Y₁ G Y₂ = (cplx Y₁)ᵀ * G * cplx Y₂` | blocks $Y_1^\top GY_2$ | matrix.tex:71, 133, 150 |
| `realDiag f`, `energyQ f M = tr(F F − F M F Mᴴ)` | $F=\diag(f)$, $\tr(F^2-FSFS^*)$ | matrix.tex:122-124 |
| `twoSiteProj x y`, `pairRestrict M x y`, `probeMatrix x y τ` | $P$, $`g=G^0|_{\{x,y\}}`$, probe ports $\sqrt\tau e_x,\sqrt\tau e_y$ | bootstrap.tex:517-519; matrix.tex:4-7 |

Representation notes: $G=\mathscr L^{-1}$ is represented by a matrix `G` with `𝓛 * G = 1` and
`G * 𝓛 = 1` (a design choice), never by `⁻¹`, so no totalized inverse enters T1–T3 statements. Ports are any
real rectangular `Y` (the paper: "The absorption identities below apply to any real rectangular $Y$",
matrix.tex:44-46); the strength-$\sigma$ column convention is recovered in `endpoint_ports` and in the
`closed_siteMatrix` note.

## Theorems

### T1 — Lemma 3.1, `mat:ward` (matrix.tex:48-102)

#### `ward_general`

```lean
@ward_general : ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {L G : Matrix n n ℂ},
  L * G = 1 →
    G * L = 1 →
      imPart G = Gᴴ * -imPart L * G ∧
        imPart G = G * -imPart L * Gᴴ
```

- Paper: matrix.tex:48-53 — "Suppose $\mathscr L$ is invertible and $W=-\operatorname{Im}\mathscr L\ge YY^\top$. Then $\operatorname{Im}G=G^*WG=GWG^*$"; proof matrix.tex:66-71.
- Verdict: Faithful. The lemma's standing hypothesis $W\ge YY^\top$ is not needed for this display and is not assumed (benign strengthening, proved). `imPart` is the paper's Hermitian imaginary part (setup.tex:41).

#### `ward_physical`

```lean
@ward_physical : ∀ {n m : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]
  {H : Matrix n n ℝ},
  Hᵀ = H →
    ∀ (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ},
      siteMatrix H E Y * G = 1 →
        G * siteMatrix H E Y = 1 →
          G - Gᴴ = (2 * I) • (Gᴴ * (cplx Y * (cplx Y)ᵀ) * G) ∧
            G - Gᴴ = (2 * I) • (G * (cplx Y * (cplx Y)ᵀ) * Gᴴ)
```

- Paper: matrix.tex:10-15 (`mat:response`, equation (3.1)) + matrix.tex:52, 66-70; stated in the form `G − Gᴴ = (2I)•(Gᴴ(YYᵀ)G) = (2I)•(G(YYᵀ)Gᴴ)`.
- Verdict: Faithful. `siteMatrix H E Y = H − E·1 − i·YYᵀ` with `H` real, `Hᵀ = H`, `E` real, `Y` real, exactly `mat:response`.

#### `scattering_symm`

```lean
@scattering_symm : ∀ {n m : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]
  [inst_3 : DecidableEq m] {H : Matrix n n ℝ},
  Hᵀ = H →
    ∀ (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ},
      siteMatrix H E Y * G = 1 →
        G * siteMatrix H E Y = 1 →
          (scatteringMatrix Y G)ᵀ = scatteringMatrix Y G
```

- Paper: matrix.tex:59-60 — "For the physical system in \Cref{mat:response}, $S$ is symmetric and unitary"; matrix.tex:84-85 "Symmetry follows from $\mathscr L^\top=\mathscr L$ and the fact that $Y$ is real."
- Verdict: Faithful. Both-sided inverse assumed (by design); only `𝓛 G = 1` is used.

#### `scattering_unitary`

```lean
@scattering_unitary : ∀ {n m : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]
  [inst_3 : DecidableEq m] {H : Matrix n n ℝ},
  Hᵀ = H →
    ∀ (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ},
      siteMatrix H E Y * G = 1 →
        G * siteMatrix H E Y = 1 →
          (scatteringMatrix Y G)ᴴ * scatteringMatrix Y G = 1 ∧
            scatteringMatrix Y G * (scatteringMatrix Y G)ᴴ = 1
```

- Paper: matrix.tex:59-60 (same sentence), proof matrix.tex:78-84.
- Verdict: Faithful.

#### `contraction_identity`

```lean
@contraction_identity : ∀ {n m : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]
  {L G : Matrix n n ℂ},
  L * G = 1 →
    G * L = 1 →
      ∀ (Y : Matrix n m ℝ),
        imPart ((cplx Y)ᵀ * G * cplx Y) -
            ((cplx Y)ᵀ * G * cplx Y)ᴴ *
              ((cplx Y)ᵀ * G * cplx Y) =
          (cplx Y)ᵀ * Gᴴ * (-imPart L - cplx Y * (cplx Y)ᵀ) *
              G *
            cplx Y
```

- Paper: matrix.tex:71-77 (the equality $a^*Y^\top G^*WGYa=\operatorname{Im}(a^*Ka)$ and the bound by $\norm{Ka}^2$).
- Verdict: Faithful (operator form of the paper's quadratic-form step; any invertible `𝓛`, `W := −Im 𝓛`).

#### `contraction_ineq`

```lean
@contraction_ineq : ∀ {n m : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]
  {L G : Matrix n n ℂ},
  L * G = 1 →
    G * L = 1 →
      ∀ (Y : Matrix n m ℝ),
        (-imPart L - cplx Y * (cplx Y)ᵀ).PosSemidef →
          ∀ (a : m → ℂ),
            (star (((cplx Y)ᵀ * G * cplx Y) *ᵥ a) ⬝ᵥ
                  ((cplx Y)ᵀ * G * cplx Y) *ᵥ a).re ≤
              (star a ⬝ᵥ ((cplx Y)ᵀ * G * cplx Y) *ᵥ a).im
```

- Paper: matrix.tex:54-55 — "$\norm{Y^\top GYa}^2\le\operatorname{Im}(a^*Y^\top GYa)$" under $W\ge YY^\top$.
- Verdict: Faithful. `W ⪰ YYᵀ` is `PosSemidef (W − YYᵀ)` (Loewner order); `‖v‖² = Re(v* v)` is the Euclidean norm (setup.tex:44-45); `Im` of the scalar $a^*Ka$ is `Complex.im`.

#### `contraction_norm_le_one`

```lean
@contraction_norm_le_one : ∀ {n m : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype m]
  [inst_3 : DecidableEq m] {L G : Matrix n n ℂ},
  L * G = 1 →
    G * L = 1 →
      ∀ (Y : Matrix n m ℝ),
        (-imPart L - cplx Y * (cplx Y)ᵀ).PosSemidef →
          ‖(cplx Y)ᵀ * G * cplx Y‖ ≤ 1
```

- Paper: matrix.tex:56 — "$\norm{Y^\top GY}\le1$".
- Verdict: Faithful. Norm = Mathlib's ℓ² induced operator norm (`Matrix.Norms.L2Operator`), the paper's default (setup.tex:44-45).

### T2 — Lemma 3.2, `mat:closure` (matrix.tex:129-161)

#### `scattering_blocks`

```lean
@scattering_blocks : ∀ {n r c : Type} [inst : Fintype n] [Fintype r] [inst_2 : DecidableEq r] [Fintype c]
  [inst_4 : DecidableEq c] (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) (G : Matrix n n ℂ),
  scatteringMatrix (YR.fromCols YC) G =
    fromBlocks (1 + (2 * I) • portResponse YR G YR) ((2 * I) • portResponse YR G YC)
      ((2 * I) • portResponse YC G YR) (1 + (2 * I) • portResponse YC G YC)
```

- Paper: matrix.tex:131-134 — "write $`S=\begin{pmatrix}A&T\\T^\top&B\end{pmatrix}`$".
- Verdict: Faithful (no symmetry: the lower-left block is $2iY_C^\top GY_R$).

#### `scattering_blocks_symm`

```lean
@scattering_blocks_symm : ∀ {n r c : Type} [inst : Fintype n] [inst_1 : DecidableEq n]
  [inst_2 : Fintype r] [inst_3 : DecidableEq r] [inst_4 : Fintype c] [inst_5 : DecidableEq c] {H : Matrix n n ℝ},
  Hᵀ = H →
    ∀ (E : ℝ) (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) {G : Matrix n n ℂ},
      siteMatrix H E (YR.fromCols YC) * G = 1 →
        scatteringMatrix (YR.fromCols YC) G =
          fromBlocks (1 + (2 * I) • portResponse YR G YR) ((2 * I) • portResponse YR G YC)
            ((2 * I) • portResponse YR G YC)ᵀ (1 + (2 * I) • portResponse YC G YC)
```

- Paper: matrix.tex:131-134.
- Verdict: Faithful: with real symmetric $`H^\#`$ the lower-left block is $T^\top$, as the paper writes it.

#### `closed_siteMatrix`

```lean
@closed_siteMatrix : ∀ {n r c : Type} [inst : Fintype r] [inst_1 : Fintype c] [inst_2 : DecidableEq n]
  (H : Matrix n n ℝ) (E : ℝ) (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) (w : ℝ),
  siteMatrix H E (YR.fromCols YC) + (↑w + I) • (cplx YC * (cplx YC)ᵀ) =
    siteMatrix (H + w • (YC * YCᵀ)) E YR
```

- Paper: matrix.tex:135-136 "Close every port in $C$ and add the real shift $w\sigma_j$ to the physical diagonal" and matrix.tex:148-149 "$\mathscr L_w=\mathscr L+(w+i)Y_CY_C^\top$".
- Verdict: Faithful; this is the definitional bridge for T2: the paper's $\mathscr L_w$ is the physical site matrix of $`(H^\#+wY_CY_C^\top,E,Y_R)`$ (for port columns $\sqrt{{\sigma_j}}e_x$, $wY_CY_C^\top$ is the shift $w\sigma_j$ at each closed-port site). Hence T1 applies to the closed system: $S_z$ is symmetric and unitary.

#### `closure_formula`

```lean
@closure_formula : ∀ {n r c : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Fintype r]
  [inst_3 : DecidableEq r] [inst_4 : Fintype c] [inst_5 : DecidableEq c] {H : Matrix n n ℝ},
  Hᵀ = H →
    ∀ (E : ℝ) (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) (w : ℝ) {G Gw : Matrix n n ℂ},
      siteMatrix H E (YR.fromCols YC) * G = 1 →
        G * siteMatrix H E (YR.fromCols YC) = 1 →
          (siteMatrix H E (YR.fromCols YC) +
                  (↑w + I) • (cplx YC * (cplx YC)ᵀ)) *
                Gw =
              1 →
            Gw *
                  (siteMatrix H E (YR.fromCols YC) +
                    (↑w + I) • (cplx YC * (cplx YC)ᵀ)) =
                1 →
              IsUnit (1 - ((↑w + I) / (↑w - I)) • (1 + (2 * I) • portResponse YC G YC)) ∧
                scatteringMatrix YR Gw =
                  1 + (2 * I) • portResponse YR G YR +
                    ((↑w + I) / (↑w - I)) •
                      ((2 * I) • portResponse YR G YC *
                          (1 - ((↑w + I) / (↑w - I)) • (1 + (2 * I) • portResponse YC G YC))⁻¹ *
                        ((2 * I) • portResponse YR G YC)ᵀ)
```

- Paper: matrix.tex:137-142 — "Where the resulting inverse exists, its scattering matrix on the retained ports is $S_z=A+Tz(\one-zB)^{-1}T^\top$, $z=\frac{w+i}{w-i}$"; proof matrix.tex:147-154.
- Verdict: Faithful, with a benign strengthening: invertibility of `1 − z•B` is a conclusion, derived from the existence of `𝓛_w⁻¹` (the paper's "where the resulting inverse exists"), not a hypothesis. `w` real as in the paper. Under-claim (recorded, not formalized): the sentences "The right-hand side is analytic for $|z|<1$" (matrix.tex:144), "the formulas extend across any removable singularities", "only finitely many closing values can make the site matrix singular", "$B$ … contractive" (matrix.tex:155-160).

### T3 — Lemma 3.3, `mat:energy-closure` (matrix.tex:163-200), and equation (3.5), `mat:energy-trace`

#### `energy_closure_general`

```lean
@energy_closure_general : ∀ {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] (f : r → ℝ)
  (A : Matrix r r ℂ) (u w : r → ℂ) (γ : ℂ),
  energyQ f (A + γ • vecMulVec u w) - energyQ f A =
    -2 * ↑(γ * w ⬝ᵥ (realDiag f * Aᴴ * realDiag f) *ᵥ u).re -
      ↑(normSq γ) * (star u ⬝ᵥ realDiag f *ᵥ u * w ⬝ᵥ realDiag f *ᵥ star w)
```

- Paper: no paper sentence (the paper only treats $w=u$); this is the non-symmetric (magnetic) form of the identity in the proof of Lemma 3.3.
- Verdict: Faithful as the non-symmetric identity; holds for every `A`, `u`, `w`, `γ`.

#### `quadForm_real`

```lean
@quadForm_real : ∀ {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] (f : r → ℝ) (u : r → ℂ),
  (star u ⬝ᵥ realDiag f *ᵥ u).im = 0
```

- Paper: matrix.tex:195 — "The last square is real and nonnegative" (reality of $u^*Fu$).
- Verdict: Faithful.

#### `energy_closure`

```lean
@energy_closure : ∀ {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] (f : r → ℝ) (A : Matrix r r ℂ),
  Aᵀ = A →
    ∀ (u : r → ℂ) (γ : ℂ),
      energyQ f (A + γ • vecMulVec u u) - energyQ f A =
        -2 * ↑(γ * u ⬝ᵥ (realDiag f * Aᴴ * realDiag f) *ᵥ u).re -
          ↑(normSq γ) * (star u ⬝ᵥ realDiag f *ᵥ u) ^ 2
```

- Paper: matrix.tex:188-194 — "expansion of $S_z=A+\gamma uu^\top$ yields the exact identity $\mathcal Q_{S_z}(f_{\widehat a})-\mathcal Q_S(f)=-2\operatorname{Re}(\gamma u^\top FA^*Fu)-|\gamma|^2(u^*Fu)^2$".
- Verdict: Faithful to the identity (trace form 𝒬 = `energyQ`; `|γ|² = normSq γ`). **Finding:** the hypothesis `Aᵀ = A` (stated by design) is not used by the kernel proof: the identity holds for all `A`. Symmetry enters only through the rank-one form $\gamma uu^\top$ (i.e. $w=u$), see `energy_closure_scattering`. The paper does not claim otherwise; the remark that $A=A^\top$ gives $A^*=\bar A$, so that the two cross terms are conjugate, is true but unnecessary (the two cross terms are conjugate for every $A$).

#### `energy_closure_scattering`

```lean
@energy_closure_scattering : ∀ {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] (f : r → ℝ)
  (S : Matrix (Option r) (Option r) ℂ),
  Sᵀ = S →
    ∀ (γ : ℂ),
      energyQ f
            (S.submatrix some some + γ • vecMulVec (fun j => S (some j) none) fun j => S none (some j)) -
          energyQ f (S.submatrix some some) =
        -2 *
            ↑(γ *
                  (fun j => S (some j) none) ⬝ᵥ
                    (realDiag f * (S.submatrix some some)ᴴ * realDiag f) *ᵥ fun j =>
                      S (some j) none).re -
          ↑(normSq γ) * ((star fun j => S (some j) none) ⬝ᵥ realDiag f *ᵥ fun j => S (some j) none) ^ 2
```

- Paper: matrix.tex:165-168 ($u=S_{\widehat a,a}$, $b=S_{aa}$), matrix.tex:186-194 ($A=S_{\widehat a,\widehat a}$, $S_z=A+\gamma uu^\top$).
- Verdict: Faithful; this is where time reversal is load-bearing: `Sᵀ = S` forces $w=S_{{a,\widehat a}}^\top=u$ and the perfect square. Port index type `Option r`, closed port `none`.

#### `energy_trace`

```lean
@energy_trace : ∀ {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] (f : r → ℝ) (S : Matrix r r ℂ),
  Sᴴ * S = 1 → S * Sᴴ = 1 → ↑(1 / 2 * ∑ a, ∑ j, normSq (S j a) * (f j - f a) ^ 2) = energyQ f S
```

- Paper: matrix.tex:116-126 — "$\mathcal Q_S(f)=\frac12\sum_{a,j}|S_{ja}|^2|f_j-f_a|^2$ … For scalar data, writing $F=\diag(f)$, unitarity gives $\mathcal Q_S(f)=\tr(F^2-FSFS^*)$".
- Verdict: Faithful for scalar data. Under-claim: vector data ("one sums this identity over real components", matrix.tex:127) not formalized.

### T4 — equation (10.15), `boot:endpoint-identity` (bootstrap.tex:515-533)

#### `endpoint_ports`

```lean
@endpoint_ports : ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {x y : n},
  x ≠ y →
    ∀ {τ : ℝ},
      0 ≤ τ →
        ∀ (G : Matrix n n ℂ),
          cplx (probeMatrix x y τ) *
                (cplx (probeMatrix x y τ))ᵀ =
              ↑τ • twoSiteProj x y ∧
            scatteringMatrix (probeMatrix x y τ) G =
              1 + (2 * I * ↑τ) • pairRestrict G x y
```

- Paper: bootstrap.tex:517-519 ("two constant-strength probes $\tau$ at distinct sites $x,y$") with the port convention matrix.tex:4-7 (column $\sqrt\sigma e_x$) and $S$ of matrix.tex:13.
- Verdict: Faithful; definitional bridge: the `twoSiteProj`/`pairRestrict` objects of T4 are the paper's $YY^\top$ and $S$ for the probe ports.

#### `endpoint_resolvent_step`

```lean
@endpoint_resolvent_step : ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n]
  {L₀ G₀ G : Matrix n n ℂ} {x y : n},
  x ≠ y →
    ∀ (τ : ℝ),
      L₀ * G₀ = 1 →
        (L₀ - (I * ↑τ) • twoSiteProj x y) * G = 1 →
          (1 - (I * ↑τ) • pairRestrict G₀ x y) * pairRestrict G x y =
            pairRestrict G₀ x y
```

- Paper: bootstrap.tex:519-522 — "Resolvent subtraction gives the damped compression $g^{\rm damp}=(1-i\tau g)^{-1}g$."
- Verdict: Faithful (multiplied-out form, valid without assuming $1-i\tau g$ invertible). Benign strengthening: $L_0$ is any invertible matrix (paper: $H_N-E$); $L=L_0-i\tau P$ is the probed system.

#### `endpoint_adjugate_entry`

```lean
endpoint_adjugate_entry : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ), ((1 - c • g).adjugate * g) 0 1 = g 0 1
```

- Paper: bootstrap.tex:524-528 — "For a symmetric two-by-two matrix, direct multiplication by the adjugate shows …".
- Verdict: Faithful; benign strengthening: symmetry of $g$ is not needed.

#### `endpoint_damped_entry`

```lean
endpoint_damped_entry : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ) (τ : ℝ),
  (1 - (I * ↑τ) • g).det ≠ 0 → ((1 - (I * ↑τ) • g)⁻¹ * g) 0 1 = g 0 1 / (1 - (I * ↑τ) • g).det
```

- Paper: bootstrap.tex:526-528 — "$(g^{\rm damp})_{xy}=\frac{g_{xy}}{\det(1-i\tau g)}$".
- Verdict: Faithful under the paper's implicit $\det(1-i\tau g)\neq0$. Note: with Mathlib's totalized `⁻¹` and `/` the equation also holds when the determinant vanishes (both sides 0), so the kernel proof does not use the hypothesis (bound as `_hdet`); the hypothesis is kept so that the statement means what the paper means.

#### `endpoint_identity`

```lean
@endpoint_identity : ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {L₀ G₀ G : Matrix n n ℂ}
  {x y : n},
  x ≠ y →
    ∀ (τ : ℝ),
      L₀ * G₀ = 1 →
        (L₀ - (I * ↑τ) • twoSiteProj x y) * G = 1 →
          G₀ x y * (2 * I * ↑τ) =
            (1 + (2 * I * ↑τ) • pairRestrict G x y) 0 1 *
              (1 - (I * ↑τ) • pairRestrict G₀ x y).det
```

- Paper: bootstrap.tex:530-533 — "Since $S_{xy}=2i\tau(g^{\rm damp})_{xy}$, the exact identity is $G^0_{xy}=\frac{S_{xy}}{2i\tau}\det(1-i\tau g)$."
- Verdict: Faithful, multiplied by $2i\tau$ (equivalent for $\tau>0$, the paper's case); no invertibility of $1-i\tau g$ needed in this form. Benign strengthening: arbitrary invertible $L_0$, any real $\tau$.

## Open items / findings

- None of T1–T4 is open: every targeted statement is proved (T1 including the optional (d) and the
  operator-norm bound; T2 without assuming `1 − zB` invertible; T3 symmetric, non-symmetric and
  scattering forms plus `mat:energy-trace`; T4 (a)–(c)).
- Finding (T3): the hypothesis `Aᵀ = A` is not load-bearing for the identity; time reversal
  is load-bearing through `w = u` (`energy_closure_scattering`). Not a paper error.
- Finding (T4b): the paper's "for a symmetric two-by-two matrix" is not needed.
- Not formalized inside the targeted lemmas (under-claims, stated rather than hidden): the Schur-complement
  assertions of `mat:ward` (matrix.tex:60-62, 87-101) and the kernel remark (104-108); the analyticity,
  removable-singularity, finitely-many-singular-values and contractivity sentences of `mat:closure`
  (144, 155-160); the conditional-expectation inequality `mat:conditional-comparison` (176-178), the bound
  $|u^\top FA^*Fu|\le\norm{Fu}^2=\mathcal M_a(f)$ (196-198) and the vector-data extension (127, 200-) of
  `mat:energy-closure`; the reduction $\mathcal Q_S(f)=\mathcal Q(A)$ after subtracting $f_a$ (185-188),
  which is a one-line block computation; and everything after bootstrap.tex:533 (the moment bounds
  `boot:two-site`, Cauchy–Schwarz step).

## Not formalized (and why)

Scope fixed before the formalization began (2026-10-07):

Theorem 1.1 (`main:theorem`, the localization theorem), `mat:cutoff` (Lemma 3.4, an analytic estimate with
unspecified constants), `mat:weak` (Lemma 3.5, vector-valued Calderón–Zygmund), `mat:phase` (Lemma 3.6), and all of `resonant`, `impedance`, `transmission`, `hierarchy`,
`screening`, `vanishing`, `bootstrap` (beyond the endpoint identity), `spectral`. These carry the
localization claim; none is within reach of a Mathlib-level formalization at reasonable cost.

Consequently this repository says nothing about the truth of the paper's main theorem (pure point spectrum
of the 2-D Anderson model at every positive disorder). It certifies only that the finite-dimensional
identities listed above are correct as stated at the pins.
