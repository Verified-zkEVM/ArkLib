/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Batch
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ChallengeRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
  # Zero-check — Hachi Figure 5 / Lemma 10

  One challenge round reducing the batched polynomial identities `H₀ ≡ 0 ∧ H_α ≡ 0`
  (`relBatchedE`, `ZeroCheck/Batch.lean`) to evaluations at derived points; the two scalar
  evaluation claims then seed the sumcheck (`Sumcheck/Bridge.lean`). It is stated over the lifted
  witness `LiftedWitness Φ μ n` and the weak-binding `LiftCom`, and composes into the §4.3 opening
  chain (`Composition.lean`).

  ## Deviation from the paper's Lemma 10

  The paper's Figure 5 draws uniform vector challenges `(τ₀, τ_α) ∈ F^{m₀} × F^{m₁}`. A
  coordinate-wise family of accepting transcripts then only certifies that a multilinear `H`
  vanishes on the axis cross through the family's center, which for two or more variables does not
  imply `H ≡ 0` — e.g. `(t₁ - a)(t₂ - b)` vanishes on the cross through `(a, b)` without being
  zero (`LinearMvExtension.exists_nonzero_vanishing_on_axis_cross`). So the argument for Lemma 10
  as stated does not go through.

  This formalization instead draws a pair of scalar seeds `(ρ₀, ρ_α) ∈ F²` and derives the
  evaluation points along the Kronecker curves `τ₀ = κ_{m₀}(ρ₀)`, `τ_α = κ_{m₁}(ρ_α)`. Restricted
  to such a curve, a multilinear `H` becomes univariate of degree `< 2^m`, and this restriction is
  injective on multilinear polynomials (`LinearMvExtension.powAlgHom_eq_zero_iff`), so
  `D = zeroCheckD m₀ m₁ = max(2, 2^{m₀}, 2^{m₁})` distinct seeds per coordinate determine `H`. The
  algebraic core is in `ArkLib/Data/MvPolynomial/LinearMvExtension.lean`, and the generic one-round
  soundness engine is `OracleReduction/…/CoordinateWiseSpecialSoundness/ChallengeRound.lean`.

  ## Coordinate-wise special soundness

  `zeroCheck_coordinateWiseSpecialSound`: from `2D − 1` accepting transcripts whose seed pairs form
  a special-sound family, the extractor (`buildWitnessE`) does one of the following.

  1. Some branch carries an escape `.inr e`: pass it through.
  2. Two branches carry distinct short openings of the shared `t`: return the weak-binding escape
     `K.escOfCollision` (`K.collision_mem`, Hachi Remark 2 / Lemma 7; the `liftShort` conjunct of
     `relZeroCheck` supplies the required shortness).
  3. All branches share one opening `w̃`: per coordinate, the family's `D` distinct seeds are
     `≥ 2^m` Kronecker roots of the multilinear identity (`arm_eq_zero_of_family`), giving
     `H₀^{w̃} ≡ 0` and `H_α^{w̃} ≡ 0`, i.e. membership in `relBatchedE` via `.inl w̃`.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly CPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec
open CoordinateWise CoordinateWise.ChallengeRound

/-! ## Wire format and CWSS structure -/

/-- The zero-check's wire format: one verifier challenge carrying the seed pair `(ρ₀, ρ_α)` as a
`Fin 2 → F`, matching the generic one-round challenge engine `ChallengeRound`. -/
@[reducible] def pSpecZeroCheck (F : Type) : ProtocolSpec 1 :=
  ChallengeRound.pSpec F 2

instance instSampleableTypeChallengePSpecZeroCheck {F : Type} [SampleableType F] :
    ∀ i, SampleableType ((pSpecZeroCheck F).Challenge i) := inferInstance

/-- The coordinate-wise special soundness structure for the zero-check: the seed-pair challenge
has `ℓ = 2` scalar coordinates over `F`, with soundness parameter `k = D = zeroCheckD m₀ m₁`,
giving a family of `2·(D−1)+1 = 2D−1` transcripts. -/
def zeroCheckStructure (F : Type) (m₀ m₁ : ℕ) : CWSSStructure (pSpecZeroCheck F) :=
  chalStructure F 2 (zeroCheckD m₀ m₁) (by norm_num) (two_le_zeroCheckD m₀ m₁)

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound rBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

open MvPolynomial

/-- The zero-check's statement map: extend the lift statement by the two Kronecker seeds
`(seeds 0, seeds 1)`. -/
def zcMapStmt {TCom : Type} (stmt : LiftStatement Φ TCom F n μ) (seeds : Fin 2 → F) :
    ZeroCheckStatement Φ TCom F n μ :=
  ⟨stmt.1, stmt.2.1, stmt.2.2, seeds 0, seeds 1⟩

/-- The zero-check verifier (Figure 5): a pass-through that extends the lift statement by the two
seeds read from the challenge. The evaluation claims constrain the never-sent `w̃` and live in
`relZeroCheck`. -/
def zeroCheckVerifier {TCom : Type} :
    Verifier oSpec (LiftStatement Φ TCom F n μ) (ZeroCheckStatement Φ TCom F n μ)
      (pSpecZeroCheck F) where
  verify := fun stmt tr => pure (zcMapStmt Φ stmt (tr.challenges ⟨0, rfl⟩))

/-- The zero-check prover (challenge-only: the honest prover absorbs the seeds and carries its
lifted witness forward as the output witness). -/
def zeroCheckProver {TCom : Type} :
    Prover oSpec (LiftStatement Φ TCom F n μ) (LiftedWitness Φ μ n)
      (ZeroCheckStatement Φ TCom F n μ) (LiftedWitness Φ μ n) (pSpecZeroCheck F) where
  PrvState
    | 0 => LiftStatement Φ TCom F n μ × LiftedWitness Φ μ n
    | 1 => (LiftStatement Φ TCom F n μ × LiftedWitness Φ μ n) × (Fin 2 → F)
  input := id
  sendMessage
    | ⟨0, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, wit⟩, c⟩ => pure (zcMapStmt Φ stmt c, wit)

/-- The zero-check's output relation (Figure 5's residual claims): `w̃` opens `t`, is short
(`liftShort`), and both batched constraint polynomials vanish at the points derived from the
seeds — `H₀` at `κ_{m₀}(ρ₀)` and `H_α` at `κ_{m₁}(ρ_α)`.

The primary polynomials `hZero`/`hAlpha` are `CMlPolynomialEval` Boolean-value vectors.
The relation evaluates them directly with `CMlPolynomialEval.eval`; the derived Mathlib views
`hZeroML`/`hAlphaML` are used only inside the Kronecker root-counting proof.

The shortness conjunct is a temporary semantic admissibility condition needed by the
norm-conditioned weak-binding escape `K.collision_mem`: a single point evaluation of `H₀` does
not imply that the corresponding opening is short. In particular, this relation deliberately
does not assume the global identity `H₀ ≡ 0`; that identity remains the conclusion extracted by
the zero-check into `relBatchedE`. -/
def relZeroCheck (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (ZeroCheckStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.t ∧
    liftShort Φ bound rBound p.2 ∧
    CMlPolynomialEval.eval (hZero Φ m₀ φF b p.2)
      (Vector.ofFn (kroneckerPoint m₀ p.1.seed₀)) = 0 ∧
    CMlPolynomialEval.eval (hAlpha Φ m₁ φF b p.1.rlin p.1.α p.2)
      (Vector.ofFn (kroneckerPoint m₁ p.1.seedα)) = 0 ∧
    bound ≤ p.1.rlin.bound}

/-- `relZeroCheck` extended with the escape branch (`.inr e` requires `e ∈ K.esc`); the input
relation of the sumcheck bridge. -/
def relZeroCheckE (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (ZeroCheckStatement Φ K.TCom F n μ × (LiftedWitness Φ μ n ⊕ E)) :=
  (relZeroCheck Φ m₀ m₁ bound rBound K φF b).withEscape K.esc

/-! ## The Kronecker root-counting step -/

omit [BEq F] [LawfulBEq F] in
/-- If a special-sound family of seed pairs (parameter `D ≥ 2^m`) has, at coordinate `i`, every
seed `ρ` satisfying `H(κ_m(ρ)) = 0` for one fixed multilinear `H`, then `H ≡ 0`. The family
supplies `D ≥ 2^m` distinct seeds at coordinate `i` (`IsSpecialSoundFamily.exists_coord_finset`);
each is a root of the univariate Kronecker restriction of degree `< 2^m`, so that restriction is
zero and injectivity gives `H = 0`
(`LinearMvExtension.multilinear_eq_zero_of_kronecker_roots`). -/
theorem arm_eq_zero_of_family {m D : ℕ} (hm : 2 ^ m ≤ D)
    (fam : Fin (2 * (D - 1) + 1) → (Fin 2 → F))
    (hfam : IsSpecialSoundFamily 2 D fam) (i : Fin 2)
    (H : MvPolynomial.restrictDegree (Fin m) F 1)
    (hroots : ∀ j, MvPolynomial.eval (kroneckerPoint m (fam j i)) H.val = 0) :
    H.val = 0 := by
  obtain ⟨s, hcard, hmem⟩ := hfam.exists_coord_finset i
  refine LinearMvExtension.multilinear_eq_zero_of_kronecker_roots (hm.trans hcard) (fun τ hτ => ?_)
  obtain ⟨j, hj⟩ := hmem τ hτ
  rw [← hj]
  exact hroots j

/-! ## The witness assembler -/

/-- Combine two distinct branch responses into an escape: pass through either branch's `.inr`
escape, or turn a collision of two distinct openings into `K.escOfCollision`. Always returns an
escape (`.inr`); its `relBatchedE`-membership is `collideOrPass_mem_relBatchedE`. -/
def collideOrPass (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (a c : LiftedWitness Φ μ n ⊕ E) : LiftedWitness Φ μ n ⊕ E :=
  match a, c with
  | Sum.inr e, _ => Sum.inr e
  | Sum.inl _, Sum.inr e => Sum.inr e
  | Sum.inl wa, Sum.inl wc => Sum.inr (K.escOfCollision wa wc)

open Classical in
/-- The zero-check witness assembler, passed as the `mkWitness` argument of the generic
`ChallengeRound` extractor:

* if all `2D − 1` branch responses equal branch 0's, return that response (a common opening, or a
  passed-through escape if branch 0 is one);
* otherwise some branch differs from branch 0, and `collideOrPass` produces an escape (a
  pass-through or a weak-binding collision). -/
noncomputable def buildWitnessE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound)) (D : ℕ)
    (_stmt : LiftStatement Φ K.TCom F n μ)
    (_fam : Fin (2 * (D - 1) + 1) → (Fin 2 → F))
    (resp : Fin (2 * (D - 1) + 1) → (LiftedWitness Φ μ n ⊕ E)) :
    LiftedWitness Φ μ n ⊕ E :=
  if h : ∃ j, resp j ≠ resp 0 then collideOrPass Φ bound rBound K (resp h.choose) (resp 0)
  else resp 0


omit [NeZero q] [IsCyclotomic Φ] in
/-- `collideOrPass a c` lands in `relBatchedE` (always as an escape) provided `a ≠ c` and each of
`a`, `c` is either a `K.esc` escape or a short opening of the shared commitment `stmt.t`. -/
theorem collideOrPass_mem_relBatchedE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound)) (φF : ZMod q →+* F) (b : ℕ)
    (stmt : LiftStatement Φ K.TCom F n μ) (a c : LiftedWitness Φ μ n ⊕ E) (hac : a ≠ c)
    (hesc_a : ∀ e, a = Sum.inr e → e ∈ K.esc)
    (hopen_a : ∀ w, a = Sum.inl w → K.com w = stmt.2.1 ∧ liftShort Φ bound rBound w)
    (hesc_c : ∀ e, c = Sum.inr e → e ∈ K.esc)
    (hopen_c : ∀ w, c = Sum.inl w → K.com w = stmt.2.1 ∧ liftShort Φ bound rBound w) :
    (stmt, collideOrPass Φ bound rBound K a c) ∈ relBatchedE Φ m₀ m₁ bound rBound K φF b := by
  rcases a with wa | ea <;> rcases c with wc | ec <;>
    simp only [collideOrPass, relBatchedE, Set.mem_withEscape_inr]
  · -- both openings: a weak-binding collision
    obtain ⟨hca, hsa⟩ := hopen_a wa rfl
    obtain ⟨hcc, hsc⟩ := hopen_c wc rfl
    have hne : wa ≠ wc := fun heq => hac (by rw [heq])
    exact K.collision_mem wa wc hne (by rw [hca, hcc]) hsa hsc
  · exact hesc_c ec rfl
  · exact hesc_a ea rfl
  · exact hesc_a ea rfl

-- `[IsCyclotomic Φ]`/`[NeZero q]` are needed to synthesize the `wTable`/`Rq` instances inside
-- `hZeroML`/`hAlphaML`, but the linter's usage analysis misses instance-synth-only section vars.
set_option linter.unusedSectionVars false in
/-- Correctness of the witness assembler: for any special-sound family of `relZeroCheckE`-accepting
branches, `buildWitnessE` returns a witness in `relBatchedE`. This is the extraction step of the
zero-check's coordinate-wise special soundness. -/
theorem buildWitnessE_mem_relBatchedE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound)) (φF : ZMod q →+* F) (b : ℕ)
    {D : ℕ} (hm₀ : 2 ^ m₀ ≤ D) (hm₁ : 2 ^ m₁ ≤ D)
    (stmt : LiftStatement Φ K.TCom F n μ)
    (fam : Fin (2 * (D - 1) + 1) → (Fin 2 → F))
    (resp : Fin (2 * (D - 1) + 1) → (LiftedWitness Φ μ n ⊕ E))
    (hrel : ∀ j, (zcMapStmt Φ stmt (fam j), resp j) ∈ relZeroCheckE Φ m₀ m₁ bound rBound K φF b)
    (hfam : IsSpecialSoundFamily 2 D fam) :
    (stmt, buildWitnessE Φ bound rBound K D stmt fam resp) ∈
      relBatchedE Φ m₀ m₁ bound rBound K φF b := by
  classical
  -- per-branch facts pulled from `relZeroCheckE` membership
  have hesc : ∀ (j) (e : E), resp j = Sum.inr e → e ∈ K.esc := by
    intro j e hje
    have := hrel j; rw [hje, relZeroCheckE, Set.mem_withEscape_inr] at this; exact this
  have hopen : ∀ (j) (w : LiftedWitness Φ μ n), resp j = Sum.inl w →
      K.com w = stmt.2.1 ∧ liftShort Φ bound rBound w := by
    intro j w hjw
    have := hrel j; rw [hjw, relZeroCheckE, Set.mem_withEscape_inl] at this
    simp only [relZeroCheck, Set.mem_setOf_eq] at this
    exact ⟨this.1, this.2.1⟩
  unfold buildWitnessE
  by_cases h : ∃ j, resp j ≠ resp 0
  · -- some branch differs from branch 0 → `collideOrPass` produces an escape
    rw [dif_pos h]
    exact collideOrPass_mem_relBatchedE Φ m₀ m₁ bound rBound K φF b stmt
      (resp h.choose) (resp 0) h.choose_spec
      (hesc h.choose) (hopen h.choose) (hesc 0) (hopen 0)
  · -- all branches equal branch 0 → common opening (or common escape)
    rw [dif_neg h]
    have hall : ∀ j, resp j = resp 0 := fun j => not_ne_iff.mp (fun hne => h ⟨j, hne⟩)
    rcases hr0 : resp 0 with w0 | e0
    · -- common opening `w0`: both identities vanish by root counting
      obtain ⟨hc0, _⟩ := hopen 0 w0 hr0
      have hbound : bound ≤ stmt.1.bound := by
        have := hrel 0; rw [hr0, relZeroCheckE, Set.mem_withEscape_inl] at this
        simp only [relZeroCheck, Set.mem_setOf_eq] at this
        exact this.2.2.2.2
      simp only [relBatchedE, Set.mem_withEscape_inl, relBatched, Set.mem_setOf_eq]
      refine ⟨hc0, ?_, ?_, hbound⟩
      · -- H₀ ≡ 0. Root counting crosses to the derived Mathlib multilinear view.
        rw [← hZeroML_eq_zero_iff]
        refine arm_eq_zero_of_family hm₀ fam hfam 0 (hZeroML Φ m₀ φF b w0) (fun j => ?_)
        have hj := hrel j; rw [(hall j).trans hr0, relZeroCheckE, Set.mem_withEscape_inl] at hj
        simp only [relZeroCheck, Set.mem_setOf_eq] at hj
        rw [← hZero_eval_eq]
        exact hj.2.2.1
      · -- H_α ≡ 0, crossing through the corresponding evaluation bridge.
        rw [← hAlphaML_eq_zero_iff]
        refine arm_eq_zero_of_family hm₁ fam hfam 1
          (hAlphaML Φ m₁ φF b stmt.1 stmt.2.2 w0) (fun j => ?_)
        have hj := hrel j; rw [(hall j).trans hr0, relZeroCheckE, Set.mem_withEscape_inl] at hj
        simp only [relZeroCheck, Set.mem_setOf_eq] at hj
        rw [← hAlpha_eval_eq]
        exact hj.2.2.2.1
    · -- common escape
      simp only [relBatchedE, Set.mem_withEscape_inr]
      exact hesc 0 e0 hr0

omit [NeZero q] in
/-- Coordinate-wise special soundness of the zero-check (Hachi Figure 5 / Lemma 10). The one-round
seed-pair verifier is coordinate-wise special sound for `zeroCheckStructure`
(`(ℓ, k) = (2, D)`, `D = zeroCheckD m₀ m₁`), reducing `relBatchedE` to `relZeroCheckE`. Assembled
by `ChallengeRound.coordinateWiseSpecialSound_of_mkWitness` from the extraction step
`buildWitnessE_mem_relBatchedE`. -/
theorem zeroCheck_coordinateWiseSpecialSound
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    (zeroCheckVerifier (oSpec := oSpec) Φ (n := n) (μ := μ) (F := F)
        (TCom := K.TCom)).coordinateWiseSpecialSound init impl
      (zeroCheckStructure F m₀ m₁)
      (relBatchedE Φ m₀ m₁ bound rBound K φF b)
      (relZeroCheckE Φ m₀ m₁ bound rBound K φF b) :=
  coordinateWiseSpecialSound_of_mkWitness init impl (by norm_num) (two_le_zeroCheckD m₀ m₁)
    (zeroCheckVerifier Φ) (fun stmt seeds => zcMapStmt Φ stmt seeds) (fun _ _ => rfl)
    (relBatchedE Φ m₀ m₁ bound rBound K φF b) (relZeroCheckE Φ m₀ m₁ bound rBound K φF b)
    (buildWitnessE Φ bound rBound K (zeroCheckD m₀ m₁))
    (fun stmt fam resp hrel hfam =>
      buildWitnessE_mem_relBatchedE Φ m₀ m₁ bound rBound K φF b
        (two_pow_m₀_le_zeroCheckD m₀ m₁) (two_pow_m₁_le_zeroCheckD m₀ m₁)
        stmt fam resp hrel hfam)

/-- The zero-check packaged as a `CWSSPackage` (Hachi Figure 5 / Lemma 10): the one-round seed-pair
verifier with the `(ℓ, k) = (2, D)` structure, reducing `relBatchedE` to `relZeroCheckE`. -/
noncomputable def zeroCheckPackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    CWSSPackage init impl
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (ZeroCheckStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (pSpecZeroCheck F) where
  verifier := zeroCheckVerifier (oSpec := oSpec) Φ
  struct := zeroCheckStructure F m₀ m₁
  relIn := relBatchedE Φ m₀ m₁ bound rBound K φF b
  relOut := relZeroCheckE Φ m₀ m₁ bound rBound K φF b
  isPure := ⟨fun stmt tr => zcMapStmt Φ stmt (tr.challenges ⟨0, rfl⟩), fun _ _ => rfl⟩
  isCWSS := zeroCheck_coordinateWiseSpecialSound Φ m₀ m₁ bound rBound init impl K φF b

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
