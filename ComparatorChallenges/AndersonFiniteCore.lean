import Mathlib

/-!
# Comparator challenge: AndersonFiniteCore

Trusted statements (with `sorry` bodies) for
the finite-dimensional algebraic core of P2 (openai/math family 261, *Pure-Point Spectrum for the
Two-Dimensional Anderson Model at Every Positive Disorder*, upstream `adc7f124`).
Anchors are `sections/<file>.tex:<line>` under
`conj-anderson-audit/references/openai-math-261/Pure-Point-…-September-23-2026/build/`.

Scope: identities only. Nothing here verifies the localization theorem; see `docs/scope.md`.
-/

set_option autoImplicit false

namespace AndersonAudit

open Matrix Complex
open scoped ComplexOrder ComplexConjugate

noncomputable section

/-! ## Objects (trusted definitions) -/

/-- A real matrix viewed as a complex matrix (entrywise coercion `ℝ → ℂ`).
The physical matrix `H^#` and the port matrix `Y` are real (sections/matrix.tex:4-9). -/
def cplx {p q : Type} (A : Matrix p q ℝ) : Matrix p q ℂ := A.map (fun x : ℝ => (x : ℂ))

/-- Hermitian imaginary part `Im D = (D - Dᴴ)/(2i)` (sections/setup.tex:41). -/
def imPart {p : Type} (D : Matrix p p ℂ) : Matrix p p ℂ := (2 * I)⁻¹ • (D - Dᴴ)

/-- The site matrix `𝓛 = H^# - E - i Y Yᵀ` of `mat:response` (sections/matrix.tex:10-15). -/
def siteMatrix {n m : Type} [Fintype m] [DecidableEq n]
    (H : Matrix n n ℝ) (E : ℝ) (Y : Matrix n m ℝ) : Matrix n n ℂ :=
  cplx H - (E : ℂ) • (1 : Matrix n n ℂ) - I • (cplx Y * (cplx Y)ᵀ)

/-- The scattering matrix `S = 1 + 2i Yᵀ G Y` of `mat:response` (sections/matrix.tex:13), as a function of the
port matrix `Y` and of the resolvent `G` (which the theorems tie to `𝓛` by `𝓛 G = G 𝓛 = 1`). -/
def scatteringMatrix {n m : Type} [Fintype n] [DecidableEq m]
    (Y : Matrix n m ℝ) (G : Matrix n n ℂ) : Matrix m m ℂ :=
  1 + (2 * I) • ((cplx Y)ᵀ * G * cplx Y)

/-- The port response block `Y₁ᵀ G Y₂`; with `Y₁ = Y₂ = Y` it is `K = Yᵀ G Y` (sections/matrix.tex:71). -/
def portResponse {n p q : Type} [Fintype n] (Y₁ : Matrix n p ℝ) (G : Matrix n n ℂ)
    (Y₂ : Matrix n q ℝ) : Matrix p q ℂ :=
  (cplx Y₁)ᵀ * G * cplx Y₂

/-- `F = diag(f)` for real data `f` (sections/matrix.tex:122). -/
def realDiag {r : Type} [DecidableEq r] (f : r → ℝ) : Matrix r r ℂ :=
  diagonal fun j => (f j : ℂ)

/-- Trace form `𝒬(M) = tr(F² - F M F Mᴴ)` of the Dirichlet energy (sections/matrix.tex:122-126). -/
def energyQ {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (M : Matrix r r ℂ) : ℂ :=
  trace (realDiag f * realDiag f - realDiag f * M * realDiag f * Mᴴ)

/-- The coordinate projection `P` onto the two probe sites `{x, y}` (sections/bootstrap.tex:517-519). -/
def twoSiteProj {n : Type} [DecidableEq n] (x y : n) : Matrix n n ℂ :=
  diagonal fun k => if k = x ∨ k = y then 1 else 0

/-- Two probes of strength `τ` at sites `x, y`: columns `√τ e_x`, `√τ e_y` (sections/matrix.tex:4-7, sections/bootstrap.tex:517-518). -/
def probeMatrix {n : Type} [DecidableEq n] (x y : n) (τ : ℝ) : Matrix n (Fin 2) ℝ :=
  Matrix.of fun k i => if k = ![x, y] i then Real.sqrt τ else 0

/-- The `2 × 2` compression `M|_{x,y}` of a site matrix, ordered `(x, y)` (sections/bootstrap.tex:519). -/
def pairRestrict {n : Type} (M : Matrix n n ℂ) (x y : n) : Matrix (Fin 2) (Fin 2) ℂ :=
  M.submatrix ![x, y] ![x, y]

/-! ## T1 — `mat:ward` (absorption identities, symmetric unitary scattering matrix) -/

/-- T1(a), general form. `mat:ward-identity` (sections/matrix.tex:48-53, proof 66-71): if `𝓛` is invertible
and `W = -Im 𝓛`, then `Im G = Gᴴ W G = G W Gᴴ`. No hypothesis on `𝓛` beyond invertibility. -/
theorem ward_general {n : Type} [Fintype n] [DecidableEq n] {L G : Matrix n n ℂ}
    (hLG : L * G = 1) (hGL : G * L = 1) :
    imPart G = Gᴴ * (-imPart L) * G ∧ imPart G = G * (-imPart L) * Gᴴ := by
  sorry

/-- T1(a), physical case `W = Y Yᵀ` (sections/matrix.tex:10-15, 52, 66-70), in the `G - Gᴴ = 2i (…)` form of
the charter: `G - Gᴴ = 2i Gᴴ (Y Yᵀ) G = 2i G (Y Yᵀ) Gᴴ`. -/
theorem ward_physical {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E Y * G = 1) (hGL : G * siteMatrix H E Y = 1) :
    G - Gᴴ = (2 * I) • (Gᴴ * (cplx Y * (cplx Y)ᵀ) * G) ∧
      G - Gᴴ = (2 * I) • (G * (cplx Y * (cplx Y)ᵀ) * Gᴴ) := by
  sorry

/-- T1(b). "For the physical system in `mat:response`, `S` is symmetric" (sections/matrix.tex:59-60, 84-85):
`Sᵀ = S`, from `𝓛ᵀ = 𝓛` (real symmetric `H^#`) and real `Y`. -/
theorem scattering_symm {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E Y * G = 1) (_hGL : G * siteMatrix H E Y = 1) :
    (scatteringMatrix Y G)ᵀ = scatteringMatrix Y G := by
  sorry

/-- T1(c). "… and unitary" (sections/matrix.tex:59-60, 78-84): `Sᴴ S = 1` and `S Sᴴ = 1`. -/
theorem scattering_unitary {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E Y * G = 1) (hGL : G * siteMatrix H E Y = 1) :
    (scatteringMatrix Y G)ᴴ * scatteringMatrix Y G = 1 ∧
      scatteringMatrix Y G * (scatteringMatrix Y G)ᴴ = 1 := by
  sorry

/-- T1(d), identity. With `K = Yᵀ G Y` and `W = -Im 𝓛`:
`Im K - Kᴴ K = Yᵀ Gᴴ (W - Y Yᵀ) G Y` (the identity behind sections/matrix.tex:71-77). Any invertible `𝓛`. -/
theorem contraction_identity {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    {L G : Matrix n n ℂ} (hLG : L * G = 1) (hGL : G * L = 1) (Y : Matrix n m ℝ) :
    imPart ((cplx Y)ᵀ * G * cplx Y) - ((cplx Y)ᵀ * G * cplx Y)ᴴ * ((cplx Y)ᵀ * G * cplx Y) =
      (cplx Y)ᵀ * Gᴴ * (-imPart L - cplx Y * (cplx Y)ᵀ) * G * cplx Y := by
  sorry

/-- T1(d), inequality `mat:ward-contraction`, first half (sections/matrix.tex:54-55, 72-77): if
`W = -Im 𝓛 ⪰ Y Yᵀ` then `‖K a‖² ≤ Im(a* K a)`, with `‖v‖² = Re(v* v)` the Euclidean norm.
The operator-norm consequence is `contraction_norm_le_one`. -/
theorem contraction_ineq {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    {L G : Matrix n n ℂ} (hLG : L * G = 1) (hGL : G * L = 1) (Y : Matrix n m ℝ)
    (hW : (-imPart L - cplx Y * (cplx Y)ᵀ).PosSemidef) (a : m → ℂ) :
    (star (((cplx Y)ᵀ * G * cplx Y) *ᵥ a) ⬝ᵥ (((cplx Y)ᵀ * G * cplx Y) *ᵥ a)).re ≤
      (star a ⬝ᵥ (((cplx Y)ᵀ * G * cplx Y) *ᵥ a)).im := by
  sorry

open scoped Matrix.Norms.L2Operator in
/-- T1(d), second half of `mat:ward-contraction` (sections/matrix.tex:56, 76-78): `‖Yᵀ G Y‖ ≤ 1` in the
`ℓ²` operator norm (Mathlib's `Matrix.Norms.L2Operator`), under `W = -Im 𝓛 ⪰ Y Yᵀ`. -/
theorem contraction_norm_le_one {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] {L G : Matrix n n ℂ} (hLG : L * G = 1) (hGL : G * L = 1) (Y : Matrix n m ℝ)
    (hW : (-imPart L - cplx Y * (cplx Y)ᵀ).PosSemidef) :
    ‖(cplx Y)ᵀ * G * cplx Y‖ ≤ 1 := by
  sorry

/-! ## T2 — `mat:closure` (common-phase closure via Woodbury) -/

/-- Block form of `S` for ports split as `Y = [Y_R | Y_C]` (sections/matrix.tex:131-134), no symmetry used:
the lower-left block is `2i Y_Cᵀ G Y_R`. -/
theorem scattering_blocks {n r c : Type} [Fintype n] [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c] (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) (G : Matrix n n ℂ) :
    scatteringMatrix (fromCols YR YC) G =
      fromBlocks (1 + (2 * I) • portResponse YR G YR) ((2 * I) • portResponse YR G YC)
        ((2 * I) • portResponse YC G YR) (1 + (2 * I) • portResponse YC G YC) := by
  sorry

/-- `S = [[A, T], [Tᵀ, B]]` exactly as written at sections/matrix.tex:131-134, for the physical system
(real symmetric `H^#`). -/
theorem scattering_blocks_symm {n r c : Type} [Fintype n] [DecidableEq n] [Fintype r]
    [DecidableEq r] [Fintype c] [DecidableEq c] {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ)
    (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E (fromCols YR YC) * G = 1) :
    scatteringMatrix (fromCols YR YC) G =
      fromBlocks (1 + (2 * I) • portResponse YR G YR) ((2 * I) • portResponse YR G YC)
        ((2 * I) • portResponse YR G YC)ᵀ (1 + (2 * I) • portResponse YC G YC) := by
  sorry

/-- Closing the ports `C` = removing their absorption and adding the real shift `w Y_C Y_Cᵀ`
(= `w σ_j` at the site of each closed port of strength `σ_j`, sections/matrix.tex:135-136, 148-149):
`𝓛 + (w + i) Y_C Y_Cᵀ` is the physical site matrix of `(H^# + w Y_C Y_Cᵀ, E, Y_R)`. -/
theorem closed_siteMatrix {n r c : Type} [Fintype r] [Fintype c] [DecidableEq n]
    (H : Matrix n n ℝ) (E : ℝ) (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) (w : ℝ) :
    siteMatrix H E (fromCols YR YC) + ((w : ℂ) + I) • (cplx YC * (cplx YC)ᵀ) =
      siteMatrix (H + w • (YC * YCᵀ)) E YR := by
  sorry

/-- T2. `mat:closure-formula` (sections/matrix.tex:129-145, proof 147-154). Closing the ports in `C` gives
`𝓛_w = 𝓛 + (w + i) Y_C Y_Cᵀ` (sections/matrix.tex:148-149). If `𝓛` and `𝓛_w` are invertible ("where the
resulting inverse exists", sections/matrix.tex:137-138), then `1 - z B` is invertible and
`1 + 2i Y_Rᵀ 𝓛_w⁻¹ Y_R = A + z T (1 - z B)⁻¹ Tᵀ` with `z = (w + i)/(w - i)`.
Invertibility of `1 - z B` is a conclusion, not a hypothesis. -/
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
  sorry

/-! ## T3 — `mat:energy-closure` (single-port energy identity, time-reversal perfect square) -/

/-- T3, general (non-symmetric) form: for ANY `A`, `u`, `w`, `γ` and real diagonal `F`,
`𝒬(A + γ u wᵀ) - 𝒬(A) = -2 Re(γ wᵀ F Aᴴ F u) - |γ|² (u* F u)(wᵀ F w̄)`.
This is the identity the magnetic (non-time-reversal) closure produces (Gate 0, §3). -/
theorem energy_closure_general {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ)
    (A : Matrix r r ℂ) (u w : r → ℂ) (γ : ℂ) :
    energyQ f (A + γ • vecMulVec u w) - energyQ f A =
      -2 * ((γ * (w ⬝ᵥ ((realDiag f * Aᴴ * realDiag f) *ᵥ u))).re : ℂ) -
        (Complex.normSq γ : ℂ) *
          ((star u ⬝ᵥ (realDiag f *ᵥ u)) * (w ⬝ᵥ (realDiag f *ᵥ star w))) := by
  sorry

/-- `u* F u` is real for real diagonal `F` (sections/matrix.tex:195 uses this). -/
theorem quadForm_real {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (u : r → ℂ) :
    (star u ⬝ᵥ (realDiag f *ᵥ u)).im = 0 := by
  sorry

/-- T3, the paper's exact identity (sections/matrix.tex:189-194): for `S_z = A + γ u uᵀ`,
`𝒬(S_z) - 𝒬(A) = -2 Re(γ uᵀ F Aᴴ F u) - |γ|² (u* F u)²`.
The hypothesis `Aᵀ = A` is stated as in the charter but is NOT used by the proof: the identity
holds for every `A` (it is `energy_closure_general` at `w = u`). Symmetry is load-bearing only
through the rank-one form `γ u uᵀ` (i.e. `w = u`); see `energy_closure_scattering`. -/
theorem energy_closure {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ)
    (A : Matrix r r ℂ) (_hA : Aᵀ = A) (u : r → ℂ) (γ : ℂ) :
    energyQ f (A + γ • vecMulVec u u) - energyQ f A =
      -2 * ((γ * (u ⬝ᵥ ((realDiag f * Aᴴ * realDiag f) *ᵥ u))).re : ℂ) -
        (Complex.normSq γ : ℂ) * (star u ⬝ᵥ (realDiag f *ᵥ u)) ^ 2 := by
  sorry

/-- T3, read off a symmetric scattering matrix: ports `Option r`, port `a = none`,
`A = S_{â,â}`, `u = S_{â,a}`, `w = S_{a,â}` (sections/matrix.tex:165-168, 186-189). Single-port closure gives
`A + γ u wᵀ`; the hypothesis `Sᵀ = S` forces `w = u` and yields the perfect square `(u* F u)²`.
This is where time reversal enters. -/
theorem energy_closure_scattering {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ)
    (S : Matrix (Option r) (Option r) ℂ) (hS : Sᵀ = S) (γ : ℂ) :
    energyQ f (S.submatrix some some +
        γ • vecMulVec (fun j => S (some j) none) (fun j => S none (some j))) -
      energyQ f (S.submatrix some some) =
      -2 * ((γ * ((fun j => S (some j) none) ⬝ᵥ
          ((realDiag f * (S.submatrix some some)ᴴ * realDiag f) *ᵥ fun j => S (some j) none))).re : ℂ) -
        (Complex.normSq γ : ℂ) *
          (star (fun j => S (some j) none) ⬝ᵥ (realDiag f *ᵥ fun j => S (some j) none)) ^ 2 := by
  sorry

/-- `mat:energy-trace` (sections/matrix.tex:116-126): for unitary `S`,
`½ Σ_{a,j} |S_ja|² (f_j - f_a)² = tr(F² - F S F Sᴴ)`. Links `energyQ` to the paper's `𝒬_S(f)`. -/
theorem energy_trace {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (S : Matrix r r ℂ)
    (hU : Sᴴ * S = 1) (hU' : S * Sᴴ = 1) :
    (((1 / 2 : ℝ) * ∑ a, ∑ j, Complex.normSq (S j a) * (f j - f a) ^ 2 : ℝ) : ℂ) =
      energyQ f S := by
  sorry

/-! ## T4 — `boot:endpoint-identity` -/

/-- The two probes are ports in the sense of sections/matrix.tex:4-15: for `τ ≥ 0`, `Y Yᵀ = τ P` and
`S = 1 + 2i Yᵀ G Y = 1 + 2iτ G|_{x,y}` (sections/bootstrap.tex:517-530). -/
theorem endpoint_ports {n : Type} [Fintype n] [DecidableEq n] {x y : n} (hxy : x ≠ y)
    {τ : ℝ} (hτ : 0 ≤ τ) (G : Matrix n n ℂ) :
    cplx (probeMatrix x y τ) * (cplx (probeMatrix x y τ))ᵀ = (τ : ℂ) • twoSiteProj x y ∧
      scatteringMatrix (probeMatrix x y τ) G = 1 + (2 * I * τ) • pairRestrict G x y := by
  sorry

/-- T4(a). Resolvent subtraction (sections/bootstrap.tex:517-522): `L = L₀ - iτ P`, `g = G₀|_{x,y}`;
then `(1 - iτ g) G|_{x,y} = g`, i.e. `G|_{x,y} = g^damp` when `1 - iτ g` is invertible. -/
theorem endpoint_resolvent_step {n : Type} [Fintype n] [DecidableEq n] {L₀ G₀ G : Matrix n n ℂ}
    {x y : n} (hxy : x ≠ y) (τ : ℝ) (h₀ : L₀ * G₀ = 1)
    (h : (L₀ - (I * τ) • twoSiteProj x y) * G = 1) :
    (1 - (I * τ) • pairRestrict G₀ x y) * pairRestrict G x y = pairRestrict G₀ x y := by
  sorry

/-- T4(b), adjugate form (sections/bootstrap.tex:524-528): `(adj(1 - c g) g)_{xy} = g_{xy}` for every `2 × 2` `g`
(symmetry of `g`, assumed in the paper, is not needed). -/
theorem endpoint_adjugate_entry (g : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    (adjugate (1 - c • g) * g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = g 0 1 := by
  sorry

/-- T4(b), the paper's displayed form (sections/bootstrap.tex:526-528): `(g^damp)_{xy} = g_{xy} / det(1 - iτ g)`,
under the paper's standing invertibility `det(1 - iτ g) ≠ 0`. -/
theorem endpoint_damped_entry (g : Matrix (Fin 2) (Fin 2) ℂ) (τ : ℝ)
    (_hdet : (1 - (I * τ) • g).det ≠ 0) :
    ((1 - (I * τ) • g)⁻¹ * g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = g 0 1 / (1 - (I * τ) • g).det := by
  sorry

/-- T4(c). `boot:endpoint-identity` (sections/bootstrap.tex:530-533), multiplied out:
`G⁰_{xy} · 2iτ = S_{xy} · det(1 - iτ g)` with `S = 1 + 2iτ G|_{x,y}` (sections/bootstrap.tex:530).
No invertibility of `1 - iτ g` is needed in this multiplied-out form. -/
theorem endpoint_identity {n : Type} [Fintype n] [DecidableEq n] {L₀ G₀ G : Matrix n n ℂ}
    {x y : n} (hxy : x ≠ y) (τ : ℝ) (h₀ : L₀ * G₀ = 1)
    (h : (L₀ - (I * τ) • twoSiteProj x y) * G = 1) :
    G₀ x y * (2 * I * τ) =
      (1 + (2 * I * τ) • pairRestrict G x y) 0 1 * (1 - (I * τ) • pairRestrict G₀ x y).det := by
  sorry

end

end AndersonAudit
