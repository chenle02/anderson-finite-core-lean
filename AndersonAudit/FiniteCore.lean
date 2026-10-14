import Mathlib

/-!
# AndersonAudit.FiniteCore

Solution module for the comparator challenge `ComparatorChallenges.AndersonFiniteCore`:
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

lemma cplx_conjTranspose {p q : Type} (A : Matrix p q ℝ) : (cplx A)ᴴ = (cplx A)ᵀ := by
  ext i j; simp [cplx]

lemma cplx_transpose {p q : Type} (A : Matrix p q ℝ) : (cplx A)ᵀ = cplx Aᵀ := by
  ext i j; simp [cplx]

lemma cplx_conjTranspose_of_symm {p : Type} {H : Matrix p p ℝ} (hH : Hᵀ = H) :
    (cplx H)ᴴ = cplx H := by
  rw [cplx_conjTranspose, cplx_transpose, hH]

lemma cplx_fromCols {n p q : Type} (A : Matrix n p ℝ) (B : Matrix n q ℝ) :
    cplx (fromCols A B) = fromCols (cplx A) (cplx B) := by
  ext i (j | j) <;> simp [cplx]

lemma cplx_add {p q : Type} (A B : Matrix p q ℝ) : cplx (A + B) = cplx A + cplx B := by
  ext i j; simp [cplx]

lemma cplx_smul {p q : Type} (c : ℝ) (A : Matrix p q ℝ) : cplx (c • A) = (c : ℂ) • cplx A := by
  ext i j; simp [cplx]

lemma cplx_mul {p q s : Type} [Fintype q] (A : Matrix p q ℝ) (B : Matrix q s ℝ) :
    cplx (A * B) = cplx A * cplx B := by
  ext i j; simp [cplx, mul_apply]

/-! ## T1 — `mat:ward` (absorption identities, symmetric unitary scattering matrix) -/

/-- T1(a), general form. `mat:ward-identity` (sections/matrix.tex:48-53, proof 66-71): if `𝓛` is invertible
and `W = -Im 𝓛`, then `Im G = Gᴴ W G = G W Gᴴ`. No hypothesis on `𝓛` beyond invertibility. -/
theorem ward_general {n : Type} [Fintype n] [DecidableEq n] {L G : Matrix n n ℂ}
    (hLG : L * G = 1) (hGL : G * L = 1) :
    imPart G = Gᴴ * (-imPart L) * G ∧ imPart G = G * (-imPart L) * Gᴴ := by
  have h1 : Gᴴ * Lᴴ = 1 := by rw [← conjTranspose_mul, hLG, conjTranspose_one]
  have h2 : Lᴴ * Gᴴ = 1 := by rw [← conjTranspose_mul, hGL, conjTranspose_one]
  have e1 : Gᴴ * (Lᴴ - L) * G = G - Gᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.one_mul, Matrix.mul_assoc, hLG, Matrix.mul_one]
  have e2 : G * (Lᴴ - L) * Gᴴ = G - Gᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, hGL, Matrix.one_mul]
  have hW : -imPart L = (2 * I)⁻¹ • (Lᴴ - L) := by
    rw [imPart, ← smul_neg, neg_sub]
  refine ⟨?_, ?_⟩
  · rw [hW, Matrix.mul_smul, Matrix.smul_mul, e1, imPart]
  · rw [hW, Matrix.mul_smul, Matrix.smul_mul, e2, imPart]

lemma siteMatrix_conjTranspose {n m : Type} [Fintype m] [DecidableEq n]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) :
    (siteMatrix H E Y)ᴴ = siteMatrix H E Y + (2 * I) • (cplx Y * (cplx Y)ᵀ) := by
  have hV : (cplx Y * (cplx Y)ᵀ)ᴴ = cplx Y * (cplx Y)ᵀ := by
    rw [conjTranspose_mul, ← cplx_conjTranspose, conjTranspose_conjTranspose, cplx_conjTranspose]
  simp only [siteMatrix, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hV,
    cplx_conjTranspose_of_symm hH, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  module

lemma neg_imPart_siteMatrix {n m : Type} [Fintype m] [DecidableEq n]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) :
    -imPart (siteMatrix H E Y) = cplx Y * (cplx Y)ᵀ := by
  rw [imPart, siteMatrix_conjTranspose hH, sub_add_cancel_left, smul_neg, neg_neg, smul_smul,
    inv_mul_cancel₀ (by simp), one_smul]

/-- T1(a), physical case `W = Y Yᵀ` (sections/matrix.tex:10-15, 52, 66-70), in the `G - Gᴴ = 2i (…)` form of
the charter: `G - Gᴴ = 2i Gᴴ (Y Yᵀ) G = 2i G (Y Yᵀ) Gᴴ`. -/
theorem ward_physical {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E Y * G = 1) (hGL : G * siteMatrix H E Y = 1) :
    G - Gᴴ = (2 * I) • (Gᴴ * (cplx Y * (cplx Y)ᵀ) * G) ∧
      G - Gᴴ = (2 * I) • (G * (cplx Y * (cplx Y)ᵀ) * Gᴴ) := by
  obtain ⟨h1, h2⟩ := ward_general hLG hGL
  rw [neg_imPart_siteMatrix hH] at h1 h2
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  refine ⟨?_, ?_⟩
  · rw [← h1, imPart, smul_smul, mul_inv_cancel₀ h2I, one_smul]
  · rw [← h2, imPart, smul_smul, mul_inv_cancel₀ h2I, one_smul]

lemma siteMatrix_transpose {n m : Type} [Fintype m] [DecidableEq n]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) :
    (siteMatrix H E Y)ᵀ = siteMatrix H E Y := by
  simp only [siteMatrix, transpose_sub, transpose_smul, transpose_one, transpose_mul,
    transpose_transpose, cplx_transpose, hH]

lemma transpose_inverse_eq {n : Type} [Fintype n] [DecidableEq n] {L G : Matrix n n ℂ}
    (hLG : L * G = 1) (hL : Lᵀ = L) : Gᵀ = G := by
  have h : Gᵀ * L = 1 := by
    conv_lhs => rw [← hL]
    rw [← transpose_mul, hLG, transpose_one]
  calc Gᵀ = Gᵀ * (L * G) := by rw [hLG, Matrix.mul_one]
    _ = (Gᵀ * L) * G := by rw [Matrix.mul_assoc]
    _ = G := by rw [h, Matrix.one_mul]

/-- T1(b). "For the physical system in `mat:response`, `S` is symmetric" (sections/matrix.tex:59-60, 84-85):
`Sᵀ = S`, from `𝓛ᵀ = 𝓛` (real symmetric `H^#`) and real `Y`. -/
theorem scattering_symm {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E Y * G = 1) (_hGL : G * siteMatrix H E Y = 1) :
    (scatteringMatrix Y G)ᵀ = scatteringMatrix Y G := by
  have hG := transpose_inverse_eq hLG (siteMatrix_transpose hH E Y)
  simp only [scatteringMatrix, transpose_add, transpose_one, transpose_smul, transpose_mul,
    transpose_transpose, hG, Matrix.mul_assoc]

lemma K_conjTranspose {n m : Type} [Fintype n] (Y : Matrix n m ℝ) (G : Matrix n n ℂ) :
    ((cplx Y)ᵀ * G * cplx Y)ᴴ = (cplx Y)ᵀ * Gᴴ * cplx Y := by
  have : ((cplx Y)ᴴ * G * cplx Y)ᴴ = (cplx Y)ᴴ * Gᴴ * cplx Y := by
    simp [conjTranspose_mul, Matrix.mul_assoc]
  simpa [cplx_conjTranspose] using this

/-- T1(c). "… and unitary" (sections/matrix.tex:59-60, 78-84): `Sᴴ S = 1` and `S Sᴴ = 1`. -/
theorem scattering_unitary {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ) (Y : Matrix n m ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E Y * G = 1) (hGL : G * siteMatrix H E Y = 1) :
    (scatteringMatrix Y G)ᴴ * scatteringMatrix Y G = 1 ∧
      scatteringMatrix Y G * (scatteringMatrix Y G)ᴴ = 1 := by
  set K := (cplx Y)ᵀ * G * cplx Y with hKdef
  have hK : K - Kᴴ = (2 * I) • (Kᴴ * K) := by
    rw [hKdef, K_conjTranspose]
    have e : (cplx Y)ᵀ * G * cplx Y - (cplx Y)ᵀ * Gᴴ * cplx Y =
        (cplx Y)ᵀ * (G - Gᴴ) * cplx Y := by rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [e, (ward_physical hH E Y hLG hGL).1, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have hS : (scatteringMatrix Y G)ᴴ = 1 - (2 * I) • Kᴴ := by
    simp only [scatteringMatrix, conjTranspose_add, conjTranspose_one, conjTranspose_smul, ← hKdef,
      Complex.star_def, map_mul, Complex.conj_I, map_ofNat]
    rw [mul_neg, neg_smul, sub_eq_add_neg]
  have h1 : (scatteringMatrix Y G)ᴴ * scatteringMatrix Y G = 1 := by
    rw [hS, scatteringMatrix, ← hKdef, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    linear_combination (norm := module) (2 * I) • hK
  exact ⟨h1, mul_eq_one_comm.mp h1⟩

/-- T1(d), identity. With `K = Yᵀ G Y` and `W = -Im 𝓛`:
`Im K - Kᴴ K = Yᵀ Gᴴ (W - Y Yᵀ) G Y` (the identity behind sections/matrix.tex:71-77). Any invertible `𝓛`. -/
theorem contraction_identity {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    {L G : Matrix n n ℂ} (hLG : L * G = 1) (hGL : G * L = 1) (Y : Matrix n m ℝ) :
    imPart ((cplx Y)ᵀ * G * cplx Y) - ((cplx Y)ᵀ * G * cplx Y)ᴴ * ((cplx Y)ᵀ * G * cplx Y) =
      (cplx Y)ᵀ * Gᴴ * (-imPart L - cplx Y * (cplx Y)ᵀ) * G * cplx Y := by
  have hIm : imPart ((cplx Y)ᵀ * G * cplx Y) = (cplx Y)ᵀ * imPart G * cplx Y := by
    rw [imPart, imPart, K_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul]
  rw [hIm, (ward_general hLG hGL).1, K_conjTranspose]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- T1(d), inequality `mat:ward-contraction`, first half (sections/matrix.tex:54-55, 72-77): if
`W = -Im 𝓛 ⪰ Y Yᵀ` then `‖K a‖² ≤ Im(a* K a)`, with `‖v‖² = Re(v* v)` the Euclidean norm.
The operator-norm consequence is `contraction_norm_le_one`. -/
theorem contraction_ineq {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    {L G : Matrix n n ℂ} (hLG : L * G = 1) (hGL : G * L = 1) (Y : Matrix n m ℝ)
    (hW : (-imPart L - cplx Y * (cplx Y)ᵀ).PosSemidef) (a : m → ℂ) :
    (star (((cplx Y)ᵀ * G * cplx Y) *ᵥ a) ⬝ᵥ (((cplx Y)ᵀ * G * cplx Y) *ᵥ a)).re ≤
      (star a ⬝ᵥ (((cplx Y)ᵀ * G * cplx Y) *ᵥ a)).im := by
  set K := (cplx Y)ᵀ * G * cplx Y with hKdef
  have hD : (imPart K - Kᴴ * K).PosSemidef := by
    rw [hKdef, contraction_identity hLG hGL Y]
    have := hW.conjTranspose_mul_mul_same (G * cplx Y)
    simpa [conjTranspose_mul, cplx_conjTranspose, Matrix.mul_assoc] using this
  have h0 := hD.dotProduct_mulVec_nonneg a
  have e1 : star a ⬝ᵥ ((Kᴴ * K) *ᵥ a) = star (K *ᵥ a) ⬝ᵥ (K *ᵥ a) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  have e2 : star a ⬝ᵥ (Kᴴ *ᵥ a) = star (star a ⬝ᵥ (K *ᵥ a)) := by
    rw [star_dotProduct, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]
  have e3 : star a ⬝ᵥ ((imPart K - Kᴴ * K) *ᵥ a) =
      (2 * I)⁻¹ * (star a ⬝ᵥ (K *ᵥ a) - star (star a ⬝ᵥ (K *ᵥ a))) -
        star (K *ᵥ a) ⬝ᵥ (K *ᵥ a) := by
    rw [sub_mulVec, dotProduct_sub, e1, imPart, smul_mulVec, dotProduct_smul, sub_mulVec,
      dotProduct_sub, e2, smul_eq_mul]
  rw [e3] at h0
  have h0re := (Complex.nonneg_iff.mp h0).1
  set z := star a ⬝ᵥ (K *ᵥ a)
  have hz : ((2 * I)⁻¹ * (z - star z)).re = z.im := by
    have : z - star z = 2 * I * (z.im : ℂ) := by
      apply Complex.ext <;> simp
      ring
    rw [this, ← mul_assoc, inv_mul_cancel₀ (by simp), one_mul, Complex.ofReal_re]
  rw [Complex.sub_re, hz] at h0re
  simpa using h0re

lemma euclid_contraction {m : Type} [Fintype m] (K : Matrix m m ℂ)
    (h : ∀ a : m → ℂ, (star (K *ᵥ a) ⬝ᵥ (K *ᵥ a)).re ≤ (star a ⬝ᵥ (K *ᵥ a)).im)
    (x : EuclideanSpace ℂ m) :
    ‖(WithLp.toLp 2 (K *ᵥ WithLp.ofLp x) : EuclideanSpace ℂ m)‖ ≤ ‖x‖ := by
  set y : EuclideanSpace ℂ m := WithLp.toLp 2 (K *ᵥ WithLp.ofLp x) with hy
  have hyy : ‖y‖ ^ 2 = (star (K *ᵥ WithLp.ofLp x) ⬝ᵥ (K *ᵥ WithLp.ofLp x)).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct, hy,
      dotProduct_comm]
    rfl
  have hxy : (star (WithLp.ofLp x) ⬝ᵥ (K *ᵥ WithLp.ofLp x)).im ≤ ‖x‖ * ‖y‖ := by
    have hin : (inner ℂ x y : ℂ) = star (WithLp.ofLp x) ⬝ᵥ (K *ᵥ WithLp.ofLp x) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rw [← hin]
    exact (Complex.im_le_norm _).trans (norm_inner_le_norm x y)
  have key : ‖y‖ ^ 2 ≤ ‖x‖ * ‖y‖ := by
    rw [hyy]; exact (h _).trans hxy
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg x
  · nlinarith

open scoped Matrix.Norms.L2Operator in
/-- T1(d), second half of `mat:ward-contraction` (sections/matrix.tex:56, 76-78): `‖Yᵀ G Y‖ ≤ 1` in the
`ℓ²` operator norm (Mathlib's `Matrix.Norms.L2Operator`), under `W = -Im 𝓛 ⪰ Y Yᵀ`. -/
theorem contraction_norm_le_one {n m : Type} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] {L G : Matrix n n ℂ} (hLG : L * G = 1) (hGL : G * L = 1) (Y : Matrix n m ℝ)
    (hW : (-imPart L - cplx Y * (cplx Y)ᵀ).PosSemidef) :
    ‖(cplx Y)ᵀ * G * cplx Y‖ ≤ 1 := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact euclid_contraction _ (contraction_ineq hLG hGL Y hW) x

/-! ## T2 — `mat:closure` (common-phase closure via Woodbury) -/

/-- Block form of `S` for ports split as `Y = [Y_R | Y_C]` (sections/matrix.tex:131-134), no symmetry used:
the lower-left block is `2i Y_Cᵀ G Y_R`. -/
theorem scattering_blocks {n r c : Type} [Fintype n] [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c] (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) (G : Matrix n n ℂ) :
    scatteringMatrix (fromCols YR YC) G =
      fromBlocks (1 + (2 * I) • portResponse YR G YR) ((2 * I) • portResponse YR G YC)
        ((2 * I) • portResponse YC G YR) (1 + (2 * I) • portResponse YC G YC) := by
  rw [scatteringMatrix, cplx_fromCols, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols,
    ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp only [portResponse, zero_add]

/-- `S = [[A, T], [Tᵀ, B]]` exactly as written at sections/matrix.tex:131-134, for the physical system
(real symmetric `H^#`). -/
theorem scattering_blocks_symm {n r c : Type} [Fintype n] [DecidableEq n] [Fintype r]
    [DecidableEq r] [Fintype c] [DecidableEq c] {H : Matrix n n ℝ} (hH : Hᵀ = H) (E : ℝ)
    (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) {G : Matrix n n ℂ}
    (hLG : siteMatrix H E (fromCols YR YC) * G = 1) :
    scatteringMatrix (fromCols YR YC) G =
      fromBlocks (1 + (2 * I) • portResponse YR G YR) ((2 * I) • portResponse YR G YC)
        ((2 * I) • portResponse YR G YC)ᵀ (1 + (2 * I) • portResponse YC G YC) := by
  have hG := transpose_inverse_eq hLG (siteMatrix_transpose hH E _)
  rw [scattering_blocks]
  congr 1
  simp only [portResponse, transpose_smul, transpose_mul, transpose_transpose, hG,
    Matrix.mul_assoc]

/-- Closing the ports `C` = removing their absorption and adding the real shift `w Y_C Y_Cᵀ`
(= `w σ_j` at the site of each closed port of strength `σ_j`, sections/matrix.tex:135-136, 148-149):
`𝓛 + (w + i) Y_C Y_Cᵀ` is the physical site matrix of `(H^# + w Y_C Y_Cᵀ, E, Y_R)`. -/
theorem closed_siteMatrix {n r c : Type} [Fintype r] [Fintype c] [DecidableEq n]
    (H : Matrix n n ℝ) (E : ℝ) (YR : Matrix n r ℝ) (YC : Matrix n c ℝ) (w : ℝ) :
    siteMatrix H E (fromCols YR YC) + ((w : ℂ) + I) • (cplx YC * (cplx YC)ᵀ) =
      siteMatrix (H + w • (YC * YCᵀ)) E YR := by
  have hY : cplx (fromCols YR YC) * (cplx (fromCols YR YC))ᵀ =
      cplx YR * (cplx YR)ᵀ + cplx YC * (cplx YC)ᵀ := by
    rw [cplx_fromCols, transpose_fromCols, fromCols_mul_fromRows]
  rw [siteMatrix, siteMatrix, hY]
  simp only [cplx_add, cplx_smul, cplx_mul, cplx_transpose]
  module

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
  set L := siteMatrix H E (fromCols YR YC) with hLdef
  set P := cplx YC with hPdef
  set Q := cplx YR with hQdef
  set cc : ℂ := (w : ℂ) + I with hcc
  set z : ℂ := cc / ((w : ℂ) - I) with hzdef
  have hG : Gᵀ = G := transpose_inverse_eq hLG (siteMatrix_transpose hH E _)
  have hwI : (w : ℂ) - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hinvw := mul_inv_cancel₀ hwI
  have hz1 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have e : (1 - z) * ((w : ℂ) - I) = -(2 * I) := by
      rw [hzdef, hcc, div_eq_mul_inv]
      linear_combination (-((w : ℂ) + I)) * hinvw
    rw [h, zero_mul] at e
    have := congrArg Complex.im e
    norm_num at this
  have hscal : (1 - z) * cc = -(z * (2 * I)) := by
    rw [hzdef, hcc, div_eq_mul_inv]
    linear_combination (-((w : ℂ) + I)) * hinvw
  -- resolvent identities
  have eq1 : Gw = G - cc • (G * P * (Pᵀ * Gw)) := by
    have e : G * ((L + cc • (P * Pᵀ)) * Gw) = Gw + cc • (G * P * (Pᵀ * Gw)) := by
      rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, hGL, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul]
      simp only [Matrix.mul_assoc]
    rw [hLGw, Matrix.mul_one] at e
    exact eq_sub_of_add_eq e.symm
  have eq2 : Gw = G - cc • (Gw * P * (Pᵀ * G)) := by
    have e : (Gw * (L + cc • (P * Pᵀ))) * G = Gw + cc • (Gw * P * (Pᵀ * G)) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc Gw L, hLG, Matrix.mul_one,
        Matrix.mul_smul, Matrix.smul_mul]
      simp only [Matrix.mul_assoc]
    rw [hGLw, Matrix.one_mul] at e
    exact eq_sub_of_add_eq e.symm
  set X := Pᵀ * G * P with hX
  set N' := 1 - cc • (Pᵀ * Gw * P) with hN'
  have hXY : Pᵀ * Gw * P = X - cc • (X * (Pᵀ * Gw * P)) := by
    conv_lhs => rw [eq1]
    rw [hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have hNN : (1 + cc • X) * N' = 1 := by
    rw [hN', Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_smul]
    linear_combination (norm := module) (-cc) • hXY
  have hB : 1 - z • (1 + (2 * I) • portResponse YC G YC) = (1 - z) • (1 + cc • X) := by
    have : portResponse YC G YC = X := rfl
    rw [this]
    have hscal' : -(z * (2 * I)) = (1 - z) * cc := hscal.symm
    linear_combination (norm := module) hscal' • X
  have hinv : (1 - z • (1 + (2 * I) • portResponse YC G YC)) * ((1 - z)⁻¹ • N') = 1 := by
    rw [hB, Matrix.smul_mul, Matrix.mul_smul, hNN, smul_smul, mul_inv_cancel₀ hz1, one_smul]
  refine ⟨⟨⟨_, _, hinv, mul_eq_one_comm.mp hinv⟩, rfl⟩, ?_⟩
  rw [Matrix.inv_eq_right_inv hinv]
  -- the Q-sandwich
  have hPQ : Pᵀ * Gw * Q = N' * (Pᵀ * G * Q) := by
    conv_lhs => rw [eq2]
    rw [hN', Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have hQQ : Qᵀ * Gw * Q = Qᵀ * G * Q - cc • (Qᵀ * G * P * N' * (Pᵀ * G * Q)) := by
    conv_lhs => rw [eq1]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 2
    simp only [Matrix.mul_assoc] at hPQ ⊢
    rw [hPQ]
  have hT : ((2 * I) • portResponse YR G YC)ᵀ = (2 * I) • (Pᵀ * G * Q) := by
    simp only [portResponse, transpose_smul, transpose_mul, transpose_transpose, hG,
      Matrix.mul_assoc, hPdef, hQdef]
  have hs : (2 * I) * cc = -(z * (2 * I) * (2 * I) * (1 - z)⁻¹) := by
    have h1 := mul_inv_cancel₀ hz1
    linear_combination (2 * I * (1 - z)⁻¹) * hscal - (2 * I * cc) * h1
  rw [hT, scatteringMatrix, ← hQdef, hQQ]
  simp only [portResponse, ← hQdef, ← hPdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  set R : Matrix r r ℂ := Qᵀ * G * P * N' * (Pᵀ * G * Q) with hR
  linear_combination (norm := module) hs.symm • R

/-! ## T3 — `mat:energy-closure` (single-port energy identity, time-reversal perfect square) -/

lemma trace_FMFMh {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (M : Matrix r r ℂ) :
    trace (realDiag f * M * realDiag f * Mᴴ) =
      ∑ i, ∑ j, (f i : ℂ) * M i j * f j * conj (M i j) := by
  have h : realDiag f * M * realDiag f = Matrix.of fun i j => (f i : ℂ) * M i j * f j := by
    ext i j; simp [realDiag, mul_diagonal, diagonal_mul]
  rw [h]
  simp only [trace, diag, mul_apply, of_apply, conjTranspose_apply, Complex.star_def]

/-- T3, general (non-symmetric) form: for ANY `A`, `u`, `w`, `γ` and real diagonal `F`,
`𝒬(A + γ u wᵀ) - 𝒬(A) = -2 Re(γ wᵀ F Aᴴ F u) - |γ|² (u* F u)(wᵀ F w̄)`.
This is the identity the magnetic (non-time-reversal) closure produces (Gate 0, §3). -/
theorem energy_closure_general {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ)
    (A : Matrix r r ℂ) (u w : r → ℂ) (γ : ℂ) :
    energyQ f (A + γ • vecMulVec u w) - energyQ f A =
      -2 * ((γ * (w ⬝ᵥ ((realDiag f * Aᴴ * realDiag f) *ᵥ u))).re : ℂ) -
        (Complex.normSq γ : ℂ) *
          ((star u ⬝ᵥ (realDiag f *ᵥ u)) * (w ⬝ᵥ (realDiag f *ᵥ star w))) := by
  have hX : w ⬝ᵥ ((realDiag f * Aᴴ * realDiag f) *ᵥ u) =
      ∑ i, ∑ j, w j * f j * conj (A i j) * f i * u i := by
    simp only [dotProduct, mulVec, realDiag, mul_diagonal, diagonal_mul, conjTranspose_apply,
      Complex.star_def, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hu : star u ⬝ᵥ (realDiag f *ᵥ u) = ∑ i, conj (u i) * f i * u i := by
    simp only [dotProduct, realDiag, mulVec_diagonal, Pi.star_apply, Complex.star_def]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hw : w ⬝ᵥ (realDiag f *ᵥ star w) = ∑ j, w j * f j * conj (w j) := by
    simp only [dotProduct, realDiag, mulVec_diagonal, Pi.star_apply, Complex.star_def]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [energyQ, energyQ, trace_sub, trace_sub, trace_FMFMh, trace_FMFMh, Complex.re_eq_add_conj,
    ← Complex.mul_conj, hX, hu, hw, Finset.sum_mul_sum]
  simp only [map_mul, map_sum, Complex.conj_conj, Complex.conj_ofReal, Matrix.add_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, map_add, Finset.mul_sum]
  rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma quadForm_eq_sum {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (u : r → ℂ) :
    star u ⬝ᵥ (realDiag f *ᵥ u) = ∑ i, ((f i * Complex.normSq (u i) : ℝ) : ℂ) := by
  simp only [dotProduct, realDiag, mulVec_diagonal, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [← Complex.mul_conj]
  ring

/-- `u* F u` is real for real diagonal `F` (sections/matrix.tex:195 uses this). -/
theorem quadForm_real {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (u : r → ℂ) :
    (star u ⬝ᵥ (realDiag f *ᵥ u)).im = 0 := by
  rw [quadForm_eq_sum, ← Complex.ofReal_sum, Complex.ofReal_im]

lemma quadForm_swap {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (u : r → ℂ) :
    u ⬝ᵥ (realDiag f *ᵥ star u) = star u ⬝ᵥ (realDiag f *ᵥ u) := by
  simp only [dotProduct, realDiag, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => by ring

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
  rw [energy_closure_general, quadForm_swap, sq]

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
  have hw : (fun j => S none (some j)) = fun j => S (some j) none := by
    funext j
    have := congrFun (congrFun hS (some j)) none
    simpa [transpose_apply] using this
  have hA : (S.submatrix some some)ᵀ = S.submatrix some some := by
    rw [transpose_submatrix, hS]
  rw [hw, energy_closure f _ hA]

/-- `mat:energy-trace` (sections/matrix.tex:116-126): for unitary `S`,
`½ Σ_{a,j} |S_ja|² (f_j - f_a)² = tr(F² - F S F Sᴴ)`. Links `energyQ` to the paper's `𝒬_S(f)`. -/
theorem energy_trace {r : Type} [Fintype r] [DecidableEq r] (f : r → ℝ) (S : Matrix r r ℂ)
    (hU : Sᴴ * S = 1) (hU' : S * Sᴴ = 1) :
    (((1 / 2 : ℝ) * ∑ a, ∑ j, Complex.normSq (S j a) * (f j - f a) ^ 2 : ℝ) : ℂ) =
      energyQ f S := by
  have hrow : ∀ j, ∑ a, S j a * conj (S j a) = 1 := by
    intro j
    have := congrFun (congrFun hU' j) j
    simpa [mul_apply, conjTranspose_apply, Complex.star_def] using this
  have hcol : ∀ a, ∑ j, S j a * conj (S j a) = 1 := by
    intro a
    have := congrFun (congrFun hU a) a
    simp only [mul_apply, conjTranspose_apply, Complex.star_def, one_apply_eq] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [energyQ, trace_sub, trace_FMFMh]
  have htr : trace (realDiag f * realDiag f) = ∑ i, ((f i : ℂ)) ^ 2 := by
    simp [trace, realDiag, sq]
  rw [htr]
  push_cast
  simp only [← Complex.mul_conj]
  have e1 : ∑ i, ((f i : ℂ)) ^ 2 = ∑ a, ∑ j, S j a * conj (S j a) * (f j : ℂ) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hrow, one_mul]
  have e2 : ∑ i, ((f i : ℂ)) ^ 2 = ∑ a, ∑ j, S j a * conj (S j a) * (f a : ℂ) ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, hcol, one_mul]
  have e3 : ∑ i, ∑ j, (f i : ℂ) * S i j * f j * conj (S i j) =
      ∑ a, ∑ j, S j a * conj (S j a) * (f j * f a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∑ i, ((f i : ℂ)) ^ 2 =
      (1 / 2 : ℂ) * (∑ a, ∑ j, S j a * conj (S j a) * (f j : ℂ) ^ 2 +
        ∑ a, ∑ j, S j a * conj (S j a) * (f a : ℂ) ^ 2) := by
    rw [← e1, ← e2]; ring
  rw [hsplit, e3]
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

/-! ## T4 — `boot:endpoint-identity` -/

/-- The two probes are ports in the sense of sections/matrix.tex:4-15: for `τ ≥ 0`, `Y Yᵀ = τ P` and
`S = 1 + 2i Yᵀ G Y = 1 + 2iτ G|_{x,y}` (sections/bootstrap.tex:517-530). -/
theorem endpoint_ports {n : Type} [Fintype n] [DecidableEq n] {x y : n} (hxy : x ≠ y)
    {τ : ℝ} (hτ : 0 ≤ τ) (G : Matrix n n ℂ) :
    cplx (probeMatrix x y τ) * (cplx (probeMatrix x y τ))ᵀ = (τ : ℂ) • twoSiteProj x y ∧
      scatteringMatrix (probeMatrix x y τ) G = 1 + (2 * I * τ) • pairRestrict G x y := by
  have hs : ((Real.sqrt τ : ℝ) : ℂ) * (Real.sqrt τ : ℂ) = τ := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hτ]
  constructor
  · ext k l
    simp only [cplx, probeMatrix, mul_apply, map_apply, transpose_apply, of_apply,
      Fin.sum_univ_two, twoSiteProj, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
    by_cases hk : k = x <;> by_cases hl : l = x <;> by_cases hk' : k = y <;>
      by_cases hl' : l = y <;> simp_all [eq_comm]
  · have hK : ∀ i j, ((cplx (probeMatrix x y τ))ᵀ * G * cplx (probeMatrix x y τ)) i j =
        (τ : ℂ) * G (![x, y] i) (![x, y] j) := by
      intro i j
      have hc : ∀ (k : n) (l : Fin 2), (((if k = ![x, y] l then Real.sqrt τ else 0 : ℝ)) : ℂ) =
          if k = ![x, y] l then ((Real.sqrt τ : ℝ) : ℂ) else 0 := fun k l => by
        split_ifs <;> simp
      simp only [mul_apply, cplx, probeMatrix, map_apply, transpose_apply, of_apply, hc, ite_mul,
        zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [← hs]; ring
    ext i j
    simp only [scatteringMatrix, pairRestrict, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      submatrix_apply, hK]
    ring

lemma mul_twoSiteProj_mul_apply {n : Type} [Fintype n] [DecidableEq n] {x y : n} (hxy : x ≠ y)
    (M N : Matrix n n ℂ) (i j : n) :
    (M * twoSiteProj x y * N) i j = M i x * N x j + M i y * N y j := by
  rw [mul_apply, Fintype.sum_eq_add x y hxy]
  · simp [twoSiteProj, mul_diagonal, hxy, hxy.symm]
  · intro k hk
    simp [twoSiteProj, mul_diagonal, hk.1, hk.2]

/-- T4(a). Resolvent subtraction (sections/bootstrap.tex:517-522): `L = L₀ - iτ P`, `g = G₀|_{x,y}`;
then `(1 - iτ g) G|_{x,y} = g`, i.e. `G|_{x,y} = g^damp` when `1 - iτ g` is invertible. -/
theorem endpoint_resolvent_step {n : Type} [Fintype n] [DecidableEq n] {L₀ G₀ G : Matrix n n ℂ}
    {x y : n} (hxy : x ≠ y) (τ : ℝ) (h₀ : L₀ * G₀ = 1)
    (h : (L₀ - (I * τ) • twoSiteProj x y) * G = 1) :
    (1 - (I * τ) • pairRestrict G₀ x y) * pairRestrict G x y = pairRestrict G₀ x y := by
  have h₀' : G₀ * L₀ = 1 := mul_eq_one_comm.mp h₀
  have key : G - (I * τ) • (G₀ * twoSiteProj x y * G) = G₀ := by
    have e : G₀ * ((L₀ - (I * τ) • twoSiteProj x y) * G) =
        G - (I * τ) • (G₀ * twoSiteProj x y * G) := by
      rw [← Matrix.mul_assoc, Matrix.mul_sub, h₀', Matrix.mul_smul, Matrix.sub_mul, Matrix.one_mul,
        Matrix.smul_mul]
    rw [h, Matrix.mul_one] at e
    exact e.symm
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  ext i j
  have e := congrFun (congrFun key (![x, y] i)) (![x, y] j)
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_twoSiteProj_mul_apply hxy] at e
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_apply, Fin.sum_univ_two,
    pairRestrict, submatrix_apply]
  simpa using e

/-- T4(b), adjugate form (sections/bootstrap.tex:524-528): `(adj(1 - c g) g)_{xy} = g_{xy}` for every `2 × 2` `g`
(symmetry of `g`, assumed in the paper, is not needed). -/
theorem endpoint_adjugate_entry (g : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    (adjugate (1 - c • g) * g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = g 0 1 := by
  simp [adjugate_fin_two, mul_apply, Fin.sum_univ_two]
  ring

/-- T4(b), the paper's displayed form (sections/bootstrap.tex:526-528): `(g^damp)_{xy} = g_{xy} / det(1 - iτ g)`,
under the paper's standing invertibility `det(1 - iτ g) ≠ 0`. -/
theorem endpoint_damped_entry (g : Matrix (Fin 2) (Fin 2) ℂ) (τ : ℝ)
    (_hdet : (1 - (I * τ) • g).det ≠ 0) :
    ((1 - (I * τ) • g)⁻¹ * g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = g 0 1 / (1 - (I * τ) • g).det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_apply, endpoint_adjugate_entry,
    smul_eq_mul, div_eq_inv_mul]

/-- T4(c). `boot:endpoint-identity` (sections/bootstrap.tex:530-533), multiplied out:
`G⁰_{xy} · 2iτ = S_{xy} · det(1 - iτ g)` with `S = 1 + 2iτ G|_{x,y}` (sections/bootstrap.tex:530).
No invertibility of `1 - iτ g` is needed in this multiplied-out form. -/
theorem endpoint_identity {n : Type} [Fintype n] [DecidableEq n] {L₀ G₀ G : Matrix n n ℂ}
    {x y : n} (hxy : x ≠ y) (τ : ℝ) (h₀ : L₀ * G₀ = 1)
    (h : (L₀ - (I * τ) • twoSiteProj x y) * G = 1) :
    G₀ x y * (2 * I * τ) =
      (1 + (2 * I * τ) • pairRestrict G x y) 0 1 * (1 - (I * τ) • pairRestrict G₀ x y).det := by
  set D := 1 - (I * τ) • pairRestrict G₀ x y
  have hstep := endpoint_resolvent_step hxy τ h₀ h
  have hadj : D.det • pairRestrict G x y = adjugate D * pairRestrict G₀ x y := by
    rw [← hstep, ← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have e := congrFun (congrFun hadj 0) 1
  rw [Matrix.smul_apply, endpoint_adjugate_entry, smul_eq_mul] at e
  have hg : pairRestrict G₀ x y 0 1 = G₀ x y := by simp [pairRestrict]
  rw [hg] at e
  rw [← e, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide), zero_add,
    smul_eq_mul]
  ring

end

end AndersonAudit
