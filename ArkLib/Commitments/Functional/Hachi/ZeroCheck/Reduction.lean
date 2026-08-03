/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Batch
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
  # Zero-check — Hachi Figure 5 / Lemma 10

  A sequence of scalar challenge rounds reducing the batched polynomial identities
  `H₀ ≡ 0 ∧ H_α ≡ 0` (`relBatchedE`, `ZeroCheck/Batch.lean`) to evaluations at direct points; the
  two
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

  This formalization instead draws the coordinates of `τ₀` and `τα` in sequence. Every scalar
  round has two distinct accepting children, producing a path-dependent complete binary
  evaluation tree. A multilinear polynomial of individual degree at most one that vanishes at
  every leaf of such a tree is zero. The public zero-test is stated for CompPoly's computable
  polynomials; Mathlib polynomials occur only inside its algebraic proof.

  ## Coordinate-wise special soundness

  `nestedZeroCheck_coordinateWiseSpecialSound` extracts from the complete binary transcript tree:

  1. Some branch carries an escape `.inr e`: pass it through.
  2. Two branches carry distinct short openings of the shared `t`: return the weak-binding escape
     `K.escOfCollision` (`K.collision_mem`, Hachi Remark 2 / Lemma 7; the `liftShort` conjunct of
     `relNestedZeroCheck` supplies the required shortness).
  3. All branches share one opening `w̃`: the first `m₀` levels and an `m₁`-level suffix give
     distinct CompPoly evaluation trees for `H₀` and `Hα`; the nested-tree zero-test yields both
     polynomial identities, hence membership in `relBatchedE` via `.inl w̃`.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly CPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec
open CoordinateWise

/-! ## Wire format and CWSS structure -/

/-! ### Nested scalar-round wire format -/

/-- A flat sequence of `r` scalar verifier challenges. -/
@[reducible] def pSpecNestedScalar (F : Type) (r : ℕ) : ProtocolSpec r :=
  ⟨fun _ => .V_to_P, fun _ => F⟩

/-- One scalar verifier challenge for each coordinate of `τ₀`, followed by one for each
coordinate of `τα`.  There are no prover-message rounds between challenges: ArkLib's
transcript-tree syntax supports consecutive verifier rounds directly. -/
@[reducible] def pSpecNestedZeroCheck (F : Type) (m₀ m₁ : ℕ) : ProtocolSpec (m₀ + m₁) :=
  pSpecNestedScalar F (m₀ + m₁)

instance instSampleableTypeChallengePSpecNestedZeroCheck
    {F : Type} [SampleableType F] {m₀ m₁ : ℕ} :
    ∀ i, SampleableType ((pSpecNestedZeroCheck F m₀ m₁).Challenge i) := by
  intro i
  change SampleableType F
  infer_instance

/-- Binary special-soundness shape for the zero-check: every scalar verifier round has
one coordinate and soundness parameter two, hence exactly two pairwise-distinct children. -/
@[reducible] def nestedZeroCheckStructure (F : Type) (m₀ m₁ : ℕ) :
    CWSSStructure (pSpecNestedZeroCheck F m₀ m₁) :=
  CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)

/-- Forget transcript-tree bookkeeping and retain its path-dependent scalar challenge labels as a
CompPoly binary evaluation tree. -/
theorem nestedRemainingDepth_last (r : ℕ) : r - (Fin.last r).val = 0 := by
  simp only [Fin.val_last, Nat.sub_self]

theorem nestedRemainingDepth_succ {r : ℕ} (m : Fin r) :
    r - m.castSucc.val = (r - m.succ.val) + 1 := by
  simp only [Fin.val_castSucc, Fin.val_succ]
  omega

def nestedTreeToEvaluationTree (F : Type) (r : ℕ) :
    {i : Fin (r + 1)} →
      ChallengeTree (pSpecNestedScalar F r)
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).arity i →
        CMlPolynomialEval.BinaryEvaluationTree F (r - i.val)
  | _, .leaf => (nestedRemainingDepth_last r).symm ▸
      (CMlPolynomialEval.BinaryEvaluationTree.leaf :
        CMlPolynomialEval.BinaryEvaluationTree F 0)
  | _, .msgNode _ h _ _ => nomatch h
  | _, .chalNode m _ challenges children =>
      (nestedRemainingDepth_succ m).symm ▸
        .node challenges (fun j => nestedTreeToEvaluationTree F r (children j))

/-- The suffix of a full scalar-round transcript beginning at round `i`. -/
def nestedTranscriptSuffix {F : Type} {r : ℕ} (i : Fin (r + 1))
    (tr : (pSpecNestedScalar F r).FullTranscript) : Fin (r - i.val) → F :=
  fun j => tr ⟨i.val + j, by omega⟩

/-- Extending a scalar transcript along a leaf path preserves every entry already present in its
prefix. -/
theorem nestedLeafPath_transcript_prefix {F : Type} {r : ℕ} {i : Fin (r + 1)}
    {arity : (pSpecNestedScalar F r).ChallengeIdx → ℕ}
    {tree : ChallengeTree (pSpecNestedScalar F r) arity i}
    (path : ChallengeTree.LeafPath tree) (pre : Transcript i (pSpecNestedScalar F r))
    (j : Fin i.val) :
    path.transcript pre ⟨j.val, by omega⟩ = pre ⟨j.val, j.isLt⟩ := by
  induction path with
  | leaf => rfl
  | msg path ih =>
      rename_i m h message child
      change Direction.V_to_P = Direction.P_to_V at h
      contradiction
  | chal challenge path ih =>
      rename_i m h challenges children
      rw [ChallengeTree.LeafPath.transcript]
      let j' : Fin m.succ.val := ⟨j.val, by
        simp only [Fin.val_castSucc, Fin.val_succ] at j ⊢
        omega⟩
      convert ih (pre.concat (challenges challenge)) j' using 1 ;
        simp [j', Transcript.concat, Fin.snoc]
      rfl

/-- If an evaluation function vanishes on every transcript below a scalar challenge tree, it
vanishes on the corresponding CompPoly evaluation tree. -/
theorem nestedTreeToEvaluationTree_vanishes {F : Type} [Zero F] {r : ℕ} :
    {i : Fin (r + 1)} →
      (tree : ChallengeTree (pSpecNestedScalar F r)
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).arity i) →
      (pre : Transcript i (pSpecNestedScalar F r)) →
      (evalAt : (Fin (r - i.val) → F) → F) →
      (∀ path : ChallengeTree.LeafPath tree,
        evalAt (nestedTranscriptSuffix i (path.transcript pre)) = 0) →
      (nestedTreeToEvaluationTree F r tree).Vanishes evalAt
  | _, .leaf, pre, evalAt, h => by
      simp only [nestedTreeToEvaluationTree,
        CMlPolynomialEval.BinaryEvaluationTree.vanishes_cast,
        CMlPolynomialEval.BinaryEvaluationTree.Vanishes]
      convert h .leaf using 1
      congr 1
      funext i
      exact (Fin.cast (nestedRemainingDepth_last r) i).elim0
  | _, .msgNode _ h _ _, _, _, _ => nomatch h
  | _, .chalNode m hm challenges children, pre, evalAt, h => by
      simp only [nestedTreeToEvaluationTree,
        CMlPolynomialEval.BinaryEvaluationTree.vanishes_cast,
        CMlPolynomialEval.BinaryEvaluationTree.Vanishes]
      intro j
      apply nestedTreeToEvaluationTree_vanishes (children j) (pre.concat (challenges j))
      intro path
      convert h (ChallengeTree.LeafPath.chal j path) using 1
      congr 1
      funext i
      let i' := Fin.cast (nestedRemainingDepth_succ m) i
      change (Fin.cons (challenges j)
          (nestedTranscriptSuffix m.succ (path.transcript (pre.concat (challenges j)))) :
          Fin ((r - m.succ.val) + 1) → F) i' = _
      by_cases hz : i'.val = 0
      · have hi' : i' = 0 := Fin.ext hz
        let izero : Fin (r - m.castSucc.val) := ⟨0, by
          simp only [Fin.val_castSucc]
          omega⟩
        have hi : i = izero := by
          apply Fin.ext
          simpa [i', izero] using hz
        rw [hi]
        rw [hi']
        simp only [Fin.cons_zero, nestedTranscriptSuffix,
          ChallengeTree.LeafPath.transcript]
        simp only [izero, Fin.val_mk, Nat.add_zero]
        symm
        have hp := nestedLeafPath_transcript_prefix path (pre.concat (challenges j))
          ⟨m.val, by simp only [Fin.val_succ]; omega⟩
        convert hp using 1
        · congr 1
        · rw [show (⟨m.val, by simp only [Fin.val_succ]; omega⟩ : Fin m.succ.val) =
            Fin.last m.val by apply Fin.ext; rfl]
          simp [Transcript.concat, Fin.snoc]
      · let k : Fin (r - m.succ.val) := ⟨i'.val - 1, by
          have := i'.isLt
          simp only [Fin.val_succ] at this ⊢
          omega⟩
        have hi' : i' = k.succ := by
          apply Fin.ext
          simp only [Fin.val_succ, k]
          omega
        rw [hi', Fin.cons_succ]
        simp only [nestedTranscriptSuffix, ChallengeTree.LeafPath.transcript]
        congr 1
        apply Fin.ext
        simp only [Fin.val_mk]
        have hcast : i'.val = i.val := rfl
        have hval : i.val = k.val + 1 := by
          have := congrArg Fin.val hi'
          simp only [Fin.val_succ] at this
          omega
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega

/-- Convert a structured transcript tree to a binary evaluation tree together with its sibling
distinctness certificate. Keeping the certificate in a subtype makes the round-index casts
proof-irrelevant to downstream extraction. -/
def nestedStructuredTreeToEvaluationTree (F : Type) (r : ℕ) :
    {i : Fin (r + 1)} →
      (tree : ChallengeTree (pSpecNestedScalar F r)
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).arity i) →
      tree.IsStructured
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).toShape →
      {tree : CMlPolynomialEval.BinaryEvaluationTree F (r - i.val) // tree.IsDistinct}
  | _, .leaf, _ => by
      exact (show 0 = r - r by omega) ▸
        ⟨(CMlPolynomialEval.BinaryEvaluationTree.leaf :
          CMlPolynomialEval.BinaryEvaluationTree F 0), trivial⟩
  | _, .msgNode _ h _ _, _ => nomatch h
  | _, .chalNode m _ challenges children, h => by
      have hFamily : IsSpecialSoundFamily 1 2
          (fun j => (Equiv.funUnique (Fin 1) F).symm (challenges j)) := h.1
      have hVectors := (isSpecialSoundFamily_one_iff_injective _).mp hFamily
      have hChallenges : Function.Injective challenges := by
        intro a b hab
        apply hVectors
        exact congrArg (Equiv.funUnique (Fin 1) F).symm hab
      let childTrees := fun j =>
        nestedStructuredTreeToEvaluationTree F r (children j) (h.2 j)
      exact (show r - m.val = (r - m.succ.val) + 1 by
        simp only [Fin.val_succ]
        omega) ▸ ⟨.node challenges (fun j => (childTrees j).1),
          hChallenges, fun j => (childTrees j).2⟩

/-- Structured scalar challenge trees convert to sibling-distinct CompPoly evaluation trees. -/
theorem nestedTreeToEvaluationTree_isDistinct (F : Type) (r : ℕ) :
    {i : Fin (r + 1)} →
      (tree : ChallengeTree (pSpecNestedScalar F r)
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).arity i) →
      tree.IsStructured
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).toShape →
      (nestedTreeToEvaluationTree F r tree).IsDistinct
  | _, .leaf, _ => by
      simp only [nestedTreeToEvaluationTree,
        CMlPolynomialEval.BinaryEvaluationTree.isDistinct_cast]
      trivial
  | _, .msgNode _ h _ _, _ => nomatch h
  | _, .chalNode _ _ challenges children, h => by
      simp only [nestedTreeToEvaluationTree,
        CMlPolynomialEval.BinaryEvaluationTree.isDistinct_cast,
        CMlPolynomialEval.BinaryEvaluationTree.IsDistinct]
      have hFamily : IsSpecialSoundFamily 1 2
          (fun j => (Equiv.funUnique (Fin 1) F).symm (challenges j)) := h.1
      have hVectors := (isSpecialSoundFamily_one_iff_injective _).mp hFamily
      refine ⟨?_, fun j => nestedTreeToEvaluationTree_isDistinct F r (children j) (h.2 j)⟩
      intro a b hab
      apply hVectors
      exact congrArg (Equiv.funUnique (Fin 1) F).symm hab

variable {F : Type} {m₀ m₁ : ℕ}

/-- Read all scalar challenges from a completed zero-check transcript. -/
def nestedZeroCheckChallenges
    (tr : (pSpecNestedZeroCheck F m₀ m₁).FullTranscript) : Fin (m₀ + m₁) → F :=
  fun i => tr i

/-- The first `m₀` transcript challenges, assembled as the direct point `τ₀`. -/
def nestedZeroCheckTauZero
    (tr : (pSpecNestedZeroCheck F m₀ m₁).FullTranscript) : Fin m₀ → F :=
  fun i => nestedZeroCheckChallenges tr (Fin.castAdd m₁ i)

/-- The final `m₁` transcript challenges, assembled as the direct point `τα`. -/
def nestedZeroCheckTauAlpha
    (tr : (pSpecNestedZeroCheck F m₀ m₁).FullTranscript) : Fin m₁ → F :=
  fun i => nestedZeroCheckChallenges tr (Fin.natAdd m₀ i)

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound rBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-! ### Scalar-round protocol -/

/-- Extend the lift statement by the direct evaluation points assembled from the
scalar-round transcript. -/
def nestedZcMapStmt {TCom : Type} (stmt : LiftStatement Φ TCom F n μ)
    (τ₀ : Fin m₀ → F) (τα : Fin m₁ → F) :
    NestedZeroCheckStatement Φ TCom F n μ m₀ m₁ :=
  ⟨stmt.1, stmt.2.1, stmt.2.2, τ₀, τα⟩

/-- Figure-5 verifier: read `m₀ + m₁` consecutive scalar challenges, split them into
the direct points `τ₀` and `τα`, and append those points to the statement. -/
def nestedZeroCheckVerifier {TCom : Type} :
    Verifier oSpec (LiftStatement Φ TCom F n μ)
      (NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) (pSpecNestedZeroCheck F m₀ m₁) where
  verify := fun stmt tr => pure (nestedZcMapStmt Φ m₀ m₁ stmt
    (nestedZeroCheckTauZero tr) (nestedZeroCheckTauAlpha tr))

/-- Figure-5 honest prover. Since all rounds are verifier challenges, its state is the
input statement/witness together with the scalar prefix received so far. -/
def nestedZeroCheckProver {TCom : Type} :
    Prover oSpec (LiftStatement Φ TCom F n μ) (LiftedWitness Φ μ n)
      (NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) (LiftedWitness Φ μ n)
      (pSpecNestedZeroCheck F m₀ m₁) where
  PrvState i := (LiftStatement Φ TCom F n μ × LiftedWitness Φ μ n) × (Fin i → F)
  input := fun stmtWit => ⟨stmtWit, fun i => i.elim0⟩
  sendMessage := fun ⟨_, h⟩ => nomatch h
  receiveChallenge := fun _ st => pure fun c => ⟨st.1, Fin.snoc st.2 c⟩
  output := fun ⟨⟨stmt, wit⟩, challenges⟩ => pure
    (nestedZcMapStmt Φ m₀ m₁ stmt
      (fun i => challenges (Fin.castAdd m₁ i))
      (fun i => challenges (Fin.natAdd m₀ i)), wit)

/-- Figure-5 point relation. The commitment opening is short and the two computable
batching polynomials vanish at the direct points carried by the statement. -/
def relNestedZeroCheck
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.t ∧
    liftShort Φ bound rBound p.2 ∧
    CMlPolynomialEval.eval (hZero Φ m₀ φF b p.2) (Vector.ofFn p.1.τ₀) = 0 ∧
    CMlPolynomialEval.eval
        (hAlpha Φ m₁ φF b p.1.rlin p.1.α p.2) (Vector.ofFn p.1.τα) = 0 ∧
    bound ≤ p.1.rlin.bound}

/-- Escape-threaded Figure-5 point relation. -/
def relNestedZeroCheckE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁ ×
      (LiftedWitness Φ μ n ⊕ E)) :=
  (relNestedZeroCheck Φ m₀ m₁ bound rBound K φF b).withEscape K.esc

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
/-- Witness assembler for the nested scalar-round extractor.

Responses are indexed by an arbitrary nonempty leaf type, so the generic transcript-tree adapter
can use dependent leaf paths directly instead of first numbering them. If two selected responses
differ, return the usual weak-binding escape; otherwise retain their common response. -/
noncomputable def buildNestedWitnessE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (_stmt : LiftStatement Φ K.TCom F n μ) {I : Type} (base : I)
    (resp : I → (LiftedWitness Φ μ n ⊕ E)) :
    LiftedWitness Φ μ n ⊕ E :=
  if h : ∃ j, resp j ≠ resp base then
    collideOrPass Φ bound rBound K (resp h.choose) (resp base)
  else resp base


omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
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

-- The batching polynomials carried by the projected trees require the cyclotomic instances;
-- Lean's unused-section-variable analysis does not see those instance-synthesis dependencies.
set_option linter.unusedSectionVars false in
/-- Correctness core of the nested-tree witness assembler.

The transcript-tree adapter supplies one binary evaluation tree for the first `m₀` challenge
levels and one for the final `m₁` levels below a fixed first-stage path.  In the common-opening
case, their leaf evaluations vanish and the point-1 nested zero tests make both computable
batching polynomials identically zero.  A differing leaf response instead yields the existing
weak-binding escape. -/
theorem buildNestedWitnessE_mem_relBatchedE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) (stmt : LiftStatement Φ K.TCom F n μ)
    {I : Type} (base : I) (resp : I → (LiftedWitness Φ μ n ⊕ E))
    (tree₀ : CMlPolynomialEval.BinaryEvaluationTree F m₀)
    (treeα : CMlPolynomialEval.BinaryEvaluationTree F m₁)
    (hDistinct₀ : tree₀.IsDistinct) (hDistinctα : treeα.IsDistinct)
    (hesc : ∀ j e, resp j = Sum.inr e → e ∈ K.esc)
    (hopen : ∀ j w, resp j = Sum.inl w →
      K.com w = stmt.2.1 ∧ liftShort Φ bound rBound w)
    (hVanishes₀ : ∀ w, (∀ j, resp j = Sum.inl w) →
      tree₀.PolynomialVanishes (hZero Φ m₀ φF b w))
    (hVanishesα : ∀ w, (∀ j, resp j = Sum.inl w) →
      treeα.PolynomialVanishes (hAlpha Φ m₁ φF b stmt.1 stmt.2.2 w))
    (hBound : ∀ w, (∀ j, resp j = Sum.inl w) → bound ≤ stmt.1.bound) :
    (stmt, buildNestedWitnessE Φ bound rBound K stmt base resp) ∈
      relBatchedE Φ m₀ m₁ bound rBound K φF b := by
  classical
  unfold buildNestedWitnessE
  by_cases h : ∃ j, resp j ≠ resp base
  · rw [dif_pos h]
    exact collideOrPass_mem_relBatchedE Φ m₀ m₁ bound rBound K φF b stmt
      (resp h.choose) (resp base) h.choose_spec
      (hesc h.choose) (hopen h.choose) (hesc base) (hopen base)
  · rw [dif_neg h]
    have hall : ∀ j, resp j = resp base := fun j => not_ne_iff.mp (fun hne => h ⟨j, hne⟩)
    rcases hr0 : resp base with w0 | e0
    · have hallOpening : ∀ j, resp j = Sum.inl w0 := fun j => (hall j).trans hr0
      have hCom := (hopen base w0 hr0).1
      simp only [relBatchedE, Set.mem_withEscape_inl, relBatched, Set.mem_setOf_eq]
      exact ⟨hCom,
        hZero_eq_zero_of_binaryEvaluationTree Φ m₀ φF b w0 tree₀ hDistinct₀
          (hVanishes₀ w0 hallOpening),
        hAlpha_eq_zero_of_binaryEvaluationTree Φ m₁ φF b stmt.1 stmt.2.2 w0 treeα
          hDistinctα (hVanishesα w0 hallOpening),
        hBound w0 hallOpening⟩
    · simp only [relBatchedE, Set.mem_withEscape_inr]
      exact hesc base e0 hr0

/-! ## Nested-tree extractor -/

/-- The canonical all-left leaf, used only as the comparison base for collision extraction. -/
def nestedLeftPath {r : ℕ} :
    {i : Fin (r + 1)} →
      (tree : ChallengeTree (pSpecNestedScalar F r)
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).arity i) →
      ChallengeTree.LeafPath tree
  | _, .leaf => .leaf
  | _, .msgNode _ h _ _ => nomatch h
  | _, .chalNode _ _ _ children => .chal 0 (nestedLeftPath (children 0))

/-- Classically select an output-relation witness for a leaf, with an arbitrary nonempty fallback
outside accepting trees. -/
noncomputable def nestedPathResponse
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) (stmt : LiftStatement Φ K.TCom F n μ)
    {arity : (pSpecNestedZeroCheck F m₀ m₁).ChallengeIdx → ℕ}
    (tree : ChallengeTree (pSpecNestedZeroCheck F m₀ m₁) arity 0)
    (path : ChallengeTree.LeafPath tree) : LiftedWitness Φ μ n ⊕ E := by
  classical
  exact if h : ∃ w, (nestedZcMapStmt Φ m₀ m₁ stmt
      (nestedZeroCheckTauZero path.fullTranscript)
      (nestedZeroCheckTauAlpha path.fullTranscript), w) ∈
        relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b then
    h.choose
  else Classical.ofNonempty

/-- Tree-based extractor for the scalar-round zero-check. -/
noncomputable def nestedZeroCheckExtractor
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Extractor.TreeBased (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (pSpecNestedZeroCheck F m₀ m₁) (nestedZeroCheckStructure F m₀ m₁).arity :=
  fun stmt tree => buildNestedWitnessE Φ bound rBound K stmt (nestedLeftPath tree)
    (nestedPathResponse Φ m₀ m₁ bound rBound K φF b stmt tree)

omit [NeZero q] in
/-- Coordinate-wise special soundness of the nested scalar-round zero-check. -/
theorem nestedZeroCheck_coordinateWiseSpecialSound
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    (nestedZeroCheckVerifier (oSpec := oSpec) Φ (n := n) (μ := μ) (F := F)
        (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom)).coordinateWiseSpecialSound init impl
      (nestedZeroCheckStructure F m₀ m₁)
      (relBatchedE Φ m₀ m₁ bound rBound K φF b)
      (relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b) := by
  classical
  refine ⟨nestedZeroCheckExtractor Φ m₀ m₁ bound rBound K φF b, ?_⟩
  intro stmt tree hStruct hAcc
  let resp := nestedPathResponse Φ m₀ m₁ bound rBound K φF b stmt tree
  have hmem : ∀ path : ChallengeTree.LeafPath tree, ∃ w,
      (nestedZcMapStmt Φ m₀ m₁ stmt
        (nestedZeroCheckTauZero path.fullTranscript)
        (nestedZeroCheckTauAlpha path.fullTranscript), w) ∈
          relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b := by
    intro path
    apply (Set.mem_language_iff _ _).1
    apply Verifier.mem_of_pure_accepting init impl
      (nestedZeroCheckVerifier (oSpec := oSpec) (n := n) (μ := μ) (F := F)
        (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom) Φ) stmt path.fullTranscript
      (relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b).language
      (nestedZcMapStmt Φ m₀ m₁ stmt
        (nestedZeroCheckTauZero path.fullTranscript)
        (nestedZeroCheckTauAlpha path.fullTranscript))
    · rfl
    · exact hAcc _ path.mem_fullTranscripts
  have hrel : ∀ path : ChallengeTree.LeafPath tree,
      (nestedZcMapStmt Φ m₀ m₁ stmt
        (nestedZeroCheckTauZero path.fullTranscript)
        (nestedZeroCheckTauAlpha path.fullTranscript), resp path) ∈
          relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b := by
    intro path
    simp only [resp, nestedPathResponse]
    rw [dif_pos (hmem path)]
    exact (hmem path).choose_spec
  let fullTree : CMlPolynomialEval.BinaryEvaluationTree F (m₀ + m₁) := by
    simpa using nestedTreeToEvaluationTree F (m₀ + m₁) tree
  have hFullDistinct : fullTree.IsDistinct := by
    simpa [fullTree] using nestedTreeToEvaluationTree_isDistinct F (m₀ + m₁) tree hStruct
  let tree₀ := fullTree.take m₀ (by omega)
  have hDepthα : m₀ + m₁ - m₀ = m₁ := by omega
  let treeα : CMlPolynomialEval.BinaryEvaluationTree F m₁ :=
    hDepthα ▸ fullTree.dropLeft m₀ (by omega)
  apply buildNestedWitnessE_mem_relBatchedE Φ m₀ m₁ bound rBound K φF b stmt
    (nestedLeftPath tree) resp tree₀ treeα
  · exact fullTree.take_isDistinct m₀ (by omega) hFullDistinct
  · simp only [treeα, CMlPolynomialEval.BinaryEvaluationTree.isDistinct_cast]
    exact fullTree.dropLeft_isDistinct m₀ (by omega) hFullDistinct
  · intro path e hpe
    have hp := hrel path
    rw [hpe, relNestedZeroCheckE, Set.mem_withEscape_inr] at hp
    exact hp
  · intro path w hpw
    have hp := hrel path
    rw [hpw, relNestedZeroCheckE, Set.mem_withEscape_inl] at hp
    simp only [relNestedZeroCheck, Set.mem_setOf_eq] at hp
    exact ⟨hp.1, hp.2.1⟩
  · intro w hall
    apply fullTree.take_vanishes m₀ (by omega)
    apply nestedTreeToEvaluationTree_vanishes tree default
    intro path
    have hp := hrel path
    rw [hall path, relNestedZeroCheckE, Set.mem_withEscape_inl] at hp
    simp only [relNestedZeroCheck, Set.mem_setOf_eq] at hp
    convert hp.2.2.1 using 1
    congr 2
    funext i
    unfold CMlPolynomialEval.BinaryEvaluationTree.pointPrefix nestedTranscriptSuffix
      nestedZeroCheckTauZero nestedZeroCheckChallenges ChallengeTree.LeafPath.fullTranscript
    congr 1
    apply Fin.ext
    simp only [Fin.val_zero, Nat.zero_add, Fin.val_mk, Fin.val_castLE, Fin.val_castAdd]
  · intro w hall
    simp only [treeα, CMlPolynomialEval.BinaryEvaluationTree.PolynomialVanishes,
      CMlPolynomialEval.BinaryEvaluationTree.vanishes_cast]
    apply fullTree.dropLeft_vanishes m₀ (by omega)
    apply nestedTreeToEvaluationTree_vanishes tree default
    intro path
    have hp := hrel path
    rw [hall path, relNestedZeroCheckE, Set.mem_withEscape_inl] at hp
    simp only [relNestedZeroCheck, Set.mem_setOf_eq] at hp
    convert hp.2.2.2.1 using 1
    congr 2
    funext i
    unfold CMlPolynomialEval.BinaryEvaluationTree.pointSuffix nestedTranscriptSuffix
      nestedZeroCheckTauAlpha nestedZeroCheckChallenges ChallengeTree.LeafPath.fullTranscript
    congr 1
    apply Fin.ext
    simp only [Fin.val_zero, Nat.zero_add, Fin.val_natAdd, Fin.val_mk, Fin.val_cast]
  · intro w hall
    have hp := hrel (nestedLeftPath tree)
    rw [hall (nestedLeftPath tree), relNestedZeroCheckE, Set.mem_withEscape_inl] at hp
    simp only [relNestedZeroCheck, Set.mem_setOf_eq] at hp
    exact hp.2.2.2.2

/-- The nested scalar-round zero-check bundled for sequential composition. -/
noncomputable def nestedZeroCheckPackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    CWSSPackage init impl
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁) (LiftedWitness Φ μ n ⊕ E)
      (pSpecNestedZeroCheck F m₀ m₁) where
  verifier := nestedZeroCheckVerifier (oSpec := oSpec) (n := n) (μ := μ) (F := F)
    (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom) Φ
  struct := nestedZeroCheckStructure F m₀ m₁
  relIn := relBatchedE Φ m₀ m₁ bound rBound K φF b
  relOut := relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b
  isPure := ⟨fun stmt tr => nestedZcMapStmt Φ m₀ m₁ stmt
    (nestedZeroCheckTauZero tr) (nestedZeroCheckTauAlpha tr), fun _ _ => rfl⟩
  isCWSS := nestedZeroCheck_coordinateWiseSpecialSound Φ m₀ m₁ bound rBound init impl K φF b

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
