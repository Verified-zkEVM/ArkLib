/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
module

public import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Batch
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
  # Zero-check — Hachi Figure 5 / Lemma 10

  A sequence of scalar challenge rounds reducing the batched polynomial identities
  `H₀ ≡ 0 ∧ H_α ≡ 0` (`relBatched`, `ZeroCheck/Batch.lean`) to evaluations at direct points; the
  two evaluation claims then seed the sumcheck (`Sumcheck/Bridge.lean`). Stated over the lifted
  witness `LiftedWitness Φ μ n` and a generic commitment `LiftCom`.

  ## Deviation from the paper's Lemma 10

  A coordinate-wise star of accepting transcripts does not by itself certify the polynomial
  identity `H₀ ≡ 0` deterministically. This gap in [NOZ26]'s argument establishes neither an
  attack nor a knowledge-soundness theorem for Figure 5. The identity-testing argument has two
  distinct issues (full analysis in `docs/kb/audits/noz26-zero-check-lemma10.md`):

  * *Shape.* `SS(S, ℓ, k)` is star-shaped by definition, so a coordinate-wise family only certifies
    that a multilinear `H` vanishes on the axis cross through the family's center — which for two
    or more variables does not imply `H ≡ 0`
    (`MvPolynomial.exists_nonzero_vanishing_on_axis_cross`), and putting more points on the
    same arms does not help. Under the lemma's own `ℓ = 2` reading the arms carry arbitrary distinct
    challenge *vectors* rather than collinear points, so the axis cross does not apply directly;
    there the objection is a dimension count: when `D < 2 ^ m₀`, `D` points cannot pin down
    that space of multilinears. This dimension-count argument is not formalized here.
  * *Degree.* Lemma 10's `D = max (2 * d) (2 * b - 1)` is a degree in `α` (Lemma 9) and in the
    witness value `w̃(u, ℓ)` respectively; neither is a degree in a coordinate of `τ`. In `τ` both
    batching polynomials are multilinear, so two distinct labels per coordinate suffice. The
    printed lemma thus over-asks in `D` and under-asks in tree shape.

  For a fixed nonzero `H₀` of total degree at most `m₀`, chosen before an independent uniform
  point `τ₀`, Schwartz–Zippel bounds `Pr[H₀(τ₀) = 0]` by `m₀ / |F|`. The analogous estimate
  holds for a fixed nonzero `H_α` of total degree at most `m₁` before its own independent
  uniform point. Their sum `(m₀ + m₁) / |F|` is a conditional identity-testing estimate, not
  a protocol knowledge-error theorem. A prior commitment alone does not establish polynomial
  fixing for the abstract `LiftCom`. The actual protocol's fixing/binding argument, escape
  reduction and knowledge bridge remain open. The certificate below instead gives the
  deterministic structured-tree guarantee composed by `CWSSPackage`.

  ## Scalar-round protocol

  `pSpecNestedZeroCheck` contains `m₀ + m₁` consecutive scalar verifier-challenge rounds and
  no prover-message rounds. `nestedZeroCheckVerifier` splits their transcript into the direct
  points `τ₀` and `τα` and appends these points to the statement.

  The certificate uses a complete sibling-distinct binary transcript tree with `m₀ + m₁`
  levels. Its first `m₀` levels certify `H₀ ≡ 0`, and its last `m₁` levels certify `H_α ≡ 0`
  when all valid leaf responses share one opening. Distinct valid openings instead establish the
  escape event.

  ## Coordinate-wise special soundness

  `nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` reads the complete binary transcript tree
  and lands in one of two cases:

  1. Two valid leaf responses give distinct short openings of the shared commitment `t`.
     Their `liftShort` conjuncts place the pair in `K.Collision`, establishing the escape event
     `nestedZeroCheckEsc`. This is an abstract collision event, not an algorithm producing a
     collision or an unconditional Module-SIS conclusion. The latter requires a concrete
     commitment instantiation and a reduction. `LiftCom` itself assumes no binding property.
  2. All valid leaf responses share one opening `w̃`.
     `H₀` is read through the first `m₀` levels of the *one*
     evaluation tree and `H_α` through its last `m₁` levels
     (`NestedEvaluationTree.eq_zero_of_vanishes_comp`), yielding both polynomial identities, hence
     `relBatched` membership.

  The extractor is executable: `ChallengeTree.LeafWitnesses` supplies an `Option` candidate output
  witness at every leaf, and `nestedZeroCheckExtractor` returns the all-left entry without
  searching the output relation; the certificate proves that lookup correct for *every* valid leaf
  witnessing. Classical choice is confined to the proof, where it assembles a total response family
  from validity witnesses in order to invoke the evaluation-tree argument. Tree size:
  `nestedZeroCheck_numLeaves`/`_lt`.

  ## Knowledge-error reference

  [FMN24] Lemma 2.31 gives the numeric term `μ * ℓ * (k - 1) / |S|`. For these scalar rounds,
  `μ = m₀ + m₁`, `ℓ = 1`, `k = 2`, hence the candidate is `(m₀ + m₁) / |F|`, matching the
  Schwartz–Zippel term numerically. This is not a proved knowledge bound here: tree acquisition,
  the actual `2 ^ (m₀ + m₁)` leaf-growth bound, efficient extraction and escape-producing
  reductions remain obligations. The printed growth condition must not replace the actual leaf
  bound in this binary case. [NOZ26] Lemma 4 prints a different formula; under the intended
  accepting-tree CWSS reading it cannot be used as a general knowledge bound. See
  `docs/kb/audits/noz26-zero-check-lemma10.md` for the primary-source comparison and counterexample.

  ## Where the norm sits

  `relNestedZeroCheck` explicitly requires `liftShort`. Two distinct valid openings of the
  same commitment therefore form a `K.Collision`: both satisfy its shortness index. For a
  concrete Ajtai commitment, short openings provide a bound on their difference; arbitrary
  long openings have no guaranteed short-difference bound.

  The batching bridge derives `liftShort` from `H₀ ≡ 0` under its arity, base and bound
  hypotheses (`hZero_eq_zero_imp_liftShort`); `relBatched` has no shortness conjunct.
  For an admissible digit base `bDig` (`1 < bDig ≤ q / 2`), the encoding itself bounds each
  quotient digit by `⌊bDig/2⌋` (`rhoDigits_valMinAbs_natAbs_le`). The point relation supplies
  shortness explicitly: a single evaluation `H₀(τ₀) = 0` does not in general imply `H₀ ≡ 0`.

  ## Source correspondence

  `relNestedZeroCheck` is the point relation used in the scalar-round repair of [NOZ26] Figure 5.
  `nestedZeroCheckEsc` records the binding alternative, and
  `nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` supplies the replacement for Lemma 10.
  A Module-SIS interpretation requires a concrete commitment instantiation and collision
  reduction, as in [NOZ26] Lemma 7 / Remark 2. These declarations remain parametric in
  `LiftCom` and do not supply that reduction or a hardness bound.

  ## Parameter comparison

  Concretely, at [NOZ26]'s `ℓ = 30` parameters (Fig. 9) the `H₀` table has `(μ + n·δ) * deg φ`
  entries, `δ = clog_b q`. The digit widening touches only the quotient block: at `q ≈ 2 ^ 32` and
  `deg φ = 2 ^ 10` it grows from `n·d ≈ 2 ^ 12.3` to `n·δ·d ≤ 2 ^ 17.3` (`δ ≤ 32`, maximal at
  `b = 2`), adding `≲ 0.25%` to the `≈ 2 ^ 26` that `μ·d` contributes. The widened table can
  require `m₀ = 27` if it crosses the `2 ^ 26` cap. If `m₀ = 26` and `m₁ = 3` (five rows),
  the tree has `2 ^ 29` leaves, against the `2 * D - 1 = 4095` of the printed Lemma 10's
  `SS(F, 2, D)` family at `D = max (2 * d) (2 * b - 1) = 2048`: roughly `2 ^ 17` times as many.
  CWSS leaf counts multiply across rounds.

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments:
      Towards Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

@[expose] public section

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

/-! ### Size of the transcript tree

`CWSSStructure` carries no size bound, so `coordinateWiseSpecialSound` alone cannot tell a usable
construction from one whose family is exponential in the witness length. The two facts below
record the
size, with two caveats on what they establish:

* `nestedZeroCheck_numLeaves` counts the leaves of the *adapter's* `NestedEvaluationTree`. The
  quantity the extractor consumes is the number of `ChallengeTree.LeafPath`s of the structured
  transcript tree; that the two agree is evident from the adapter but is not formalized.
* `nestedZeroCheck_numLeaves_lt` is arithmetic on naturals: minimality of `m₀`, `m₁` enters as its
  hypotheses rather than being enforced, since `hμn` and `hn` bound the arities from below only.

Only `2 ^ m₀ + 2 ^ m₁ - 1` leaves are *used* (`H₀` needs one accepting continuation per
`τ₀`-prefix, `H_α` one complete `m₁`-subtree), while `ChallengeTree.IsStructured` demands the
complete tree. A knowledge conversion must bound the actual leaf count by a polynomial in the
security parameter; the probability and execution obligations in the module overview remain open. -/

/-- The evaluation tree the adapter produces has exactly `2 ^ (m₀ + m₁)` leaves: `m₀ + m₁` challenge
rounds, two pairwise-distinct children each. -/
theorem nestedZeroCheck_numLeaves {F : Type} {m₀ m₁ : ℕ}
    (tree : NestedEvaluationTree F 2 (m₀ + m₁)) : tree.numLeaves = 2 ^ (m₀ + m₁) :=
  tree.numLeaves_eq_pow

/-- With the two arities chosen *minimally* for their pins — `2 ^ m₀ < 2 * A` for
`A := (μ + n·δ) * deg φ` (the `H₀` table size, cf. `hμn`) and `2 ^ m₁ < 2 * B` for `B := n` (the row
count, cf. `hn`) — the leaf count is below `4 * A * B`, hence polynomial in the witness dimensions.
Both hypotheses are assumptions on the instantiation; see the caveats above. -/
theorem nestedZeroCheck_numLeaves_lt {m₀ m₁ A B : ℕ}
    (hm₀ : 2 ^ m₀ < 2 * A) (hm₁ : 2 ^ m₁ < 2 * B) : 2 ^ (m₀ + m₁) < 4 * A * B := by
  calc 2 ^ (m₀ + m₁) = 2 ^ m₀ * 2 ^ m₁ := pow_add 2 m₀ m₁
    _ < 2 * A * (2 * B) := Nat.mul_lt_mul_of_lt_of_lt hm₀ hm₁
    _ = 4 * A * B := by ring

/-- Forget transcript-tree bookkeeping and retain its path-dependent scalar challenge labels as a
binary evaluation tree.

The two depth equations below are the only arithmetic in this file: ArkLib's `ChallengeTree` is
indexed by the *current round*, so an adapter must convert "rounds remaining" into a depth. The
zero test itself needs no depth arithmetic — `NestedEvaluationTree.eq_zero_of_vanishes_comp` reads
each polynomial through a window of levels instead of projecting the tree. -/
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
        NestedEvaluationTree F 2 (r - i.val)
  | _, .leaf =>
      (nestedRemainingDepth_last r).symm ▸ (NestedEvaluationTree.leaf : NestedEvaluationTree F 2 0)
  | _, .msgNode _ h _ _ => nomatch h
  | _, .chalNode m _ challenges children =>
      (nestedRemainingDepth_succ m).symm ▸
        .node challenges (fun j => nestedTreeToEvaluationTree F r (children j))

/-- The suffix of a full scalar-round transcript beginning at round `i`. -/
def nestedTranscriptSuffix {F : Type} {r : ℕ} (i : Fin (r + 1))
    (tr : (pSpecNestedScalar F r).FullTranscript) : Fin (r - i.val) → F :=
  fun j => tr ⟨i.val + j, by omega⟩

@[simp]
theorem nestedTranscriptSuffix_zero {F : Type} {r : ℕ}
    (tr : (pSpecNestedScalar F r).FullTranscript) :
    nestedTranscriptSuffix (0 : Fin (r + 1)) tr = tr := by
  funext i
  unfold nestedTranscriptSuffix
  congr 1
  apply Fin.ext
  simp only [Fin.val_zero, Nat.zero_add]

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
      convert ih (pre.concat (challenges challenge)) j' using 1
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
      simp only [nestedTreeToEvaluationTree, NestedEvaluationTree.vanishes_cast,
        NestedEvaluationTree.Vanishes]
      convert h .leaf using 1
      congr 1
      funext i
      exact (Fin.cast (nestedRemainingDepth_last r) i).elim0
  | _, .msgNode _ h _ _, _, _, _ => nomatch h
  | _, .chalNode m hm challenges children, pre, evalAt, h => by
      simp only [nestedTreeToEvaluationTree, NestedEvaluationTree.vanishes_cast,
        NestedEvaluationTree.Vanishes]
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
        let jm : Fin m.succ.val := Fin.last m.val
        have hp := nestedLeafPath_transcript_prefix path (pre.concat (challenges j)) jm
        have hidx :
            (⟨m.castSucc.val, by omega⟩ : Fin r) = ⟨jm.val, by omega⟩ := by
          apply Fin.ext
          simp only [Fin.val_castSucc, jm, Fin.val_last]
        rw [hidx, hp]
        simp only [Transcript.concat, Fin.snoc, Fin.val_succ, Fin.val_last,
          lt_self_iff_false, ↓reduceDIte, take_Type, jm]
        exact eq_of_heq (cast_heq _ _).symm
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
        have hcast : i'.val = i.val := rfl
        have hval : i.val = k.val + 1 := by
          have := congrArg Fin.val hi'
          simp only [Fin.val_succ] at this
          omega
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega

/-- Structured scalar challenge trees convert to sibling-distinct CompPoly evaluation trees. -/
theorem nestedTreeToEvaluationTree_isDistinct (F : Type) (r : ℕ) :
    {i : Fin (r + 1)} →
      (tree : ChallengeTree (pSpecNestedScalar F r)
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).arity i) →
      tree.IsStructured
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).toShape →
      (nestedTreeToEvaluationTree F r tree).IsDistinct
  | _, .leaf, _ => by
      simp only [nestedTreeToEvaluationTree, NestedEvaluationTree.isDistinct_cast]
      trivial
  | _, .msgNode _ h _ _, _ => nomatch h
  | _, .chalNode _ _ challenges children, h => by
      simp only [nestedTreeToEvaluationTree, NestedEvaluationTree.isDistinct_cast,
        NestedEvaluationTree.IsDistinct]
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
variable (m₀ m₁ : ℕ) (bound bDig : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-! ### Scalar-round protocol -/

/-- Extend the lift statement by the direct evaluation points assembled from the
scalar-round transcript. -/
def nestedZcMapStmt {TCom : Type} (stmt : LiftStatement Φ TCom F n μ)
    (τ₀ : Fin m₀ → F) (τα : Fin m₁ → F) :
  NestedZeroCheckStatement Φ TCom F n μ m₀ m₁ :=
  ⟨stmt.1, stmt.2.1, stmt.2.2, τ₀, τα⟩

/-- Scalar-round verifier: read `m₀ + m₁` consecutive scalar challenges, split them into
the direct points `τ₀` and `τα`, and append those points to the statement. -/
def nestedZeroCheckVerifier {TCom : Type} :
    Verifier oSpec (LiftStatement Φ TCom F n μ)
      (NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) (pSpecNestedZeroCheck F m₀ m₁) where
  verify := fun stmt tr => pure (nestedZcMapStmt Φ m₀ m₁ stmt
    (nestedZeroCheckTauZero tr) (nestedZeroCheckTauAlpha tr))

/-- The nested scalar-round verifier's purity as executable data.  Sequential composition runs
this verdict at its seam, so the package stores a `PureForm` rather than recovering a function
from a propositional purity witness. -/
def nestedZeroCheckVerifierPureForm {TCom : Type} :
    (nestedZeroCheckVerifier (oSpec := oSpec) Φ (n := n) (μ := μ) (F := F)
      (m₀ := m₀) (m₁ := m₁) (TCom := TCom)).PureForm where
  verify := fun stmt tr => nestedZcMapStmt Φ m₀ m₁ stmt
    (nestedZeroCheckTauZero tr) (nestedZeroCheckTauAlpha tr)
  verify_eq := fun _ _ => rfl

/-- Honest scalar-round prover. Since all rounds are verifier challenges, its state is the
input statement/witness together with the scalar prefix received so far. The stage is generic in
the witness type — it only transports whatever the commitment's openings are.

It is consumed by `nestedZeroCheckReduction`, the protocol object this link's completeness is
stated about; the `castAdd`/`natAdd` split below is deliberately the same one
`nestedZeroCheckVerifier` performs on the transcript, which is what makes the two agree. -/
def nestedZeroCheckProver {TCom Wit : Type} :
    Prover oSpec (LiftStatement Φ TCom F n μ) Wit
      (NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) Wit
      (pSpecNestedZeroCheck F m₀ m₁) where
  PrvState i := (LiftStatement Φ TCom F n μ × Wit) × (Fin i → F)
  input := fun stmtWit => ⟨stmtWit, fun i => i.elim0⟩
  sendMessage := fun ⟨_, h⟩ => nomatch h
  receiveChallenge := fun _ st => pure fun c => ⟨st.1, Fin.snoc st.2 c⟩
  output := fun ⟨⟨stmt, wit⟩, challenges⟩ => pure
    (nestedZcMapStmt Φ m₀ m₁ stmt
      (fun i => challenges (Fin.castAdd m₁ i))
      (fun i => challenges (Fin.natAdd m₀ i)), wit)

/-- The computable scalar-round zero-check protocol, pairing `nestedZeroCheckProver` with
`nestedZeroCheckVerifier`. Its verifier is also used by `nestedZeroCheckPackage`. -/
def nestedZeroCheckReduction {TCom Wit : Type} :
    Reduction oSpec (LiftStatement Φ TCom F n μ) Wit
      (NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) Wit
      (pSpecNestedZeroCheck F m₀ m₁) where
  prover := nestedZeroCheckProver Φ m₀ m₁
  verifier := nestedZeroCheckVerifier Φ m₀ m₁

/-- An opening of the statement's commitment satisfying `liftShort`, with both batching
polynomials zero at the statement's evaluation points and `bound ≤ stmt.rlin.bound`.

The shortness conjunct ensures that distinct valid openings of the same commitment form a
`K.Collision`. This relation asserts evaluations at the statement's points, not zero-polynomial
identities. -/
def relNestedZeroCheck (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.t ∧
    liftShort Φ bound bDig p.2 ∧
    CMlPolynomialEval.eval (hZero Φ m₀ φF b p.2) (Vector.ofFn p.1.τ₀) = 0 ∧
    CMlPolynomialEval.eval
        (hAlpha Φ m₁ φF b p.1.rlin p.1.α p.2) (Vector.ofFn p.1.τα) = 0 ∧
    bound ≤ p.1.rlin.bound}

/-- The canonical all-left leaf: the extractor's output branch, and the comparison base of the
collision case. -/
def nestedLeftPath {r : ℕ} :
    {i : Fin (r + 1)} →
      (tree : ChallengeTree (pSpecNestedScalar F r)
        (CWSSStructure.ofSpecialSound (fun _ => 2) (fun _ => by omega)).arity i) →
      ChallengeTree.LeafPath tree
  | _, .leaf => .leaf
  | _, .msgNode _ h _ _ => nomatch h
  | _, .chalNode _ _ _ children => .chal 0 (nestedLeftPath (children 0))

/-- Tree-based extractor for the scalar-round zero-check: directly return the caller-supplied
output witness at the canonical all-left leaf. It neither searches the output relation nor
branches on acceptance. -/
def nestedZeroCheckExtractor {TCom : Type} :
    Extractor.TreeBased (LiftStatement Φ TCom F n μ) (LiftedWitness Φ μ n)
      (LiftedWitness Φ μ n) (pSpecNestedZeroCheck F m₀ m₁)
      (nestedZeroCheckStructure F m₀ m₁).arity :=
  fun _ tree leafWits => leafWits (nestedLeftPath tree)

/-! ## The weak-binding escape event -/

/-- The tree admits a valid response at every leaf, with two responses forming a `K.Collision`.
Every response satisfies `relNestedZeroCheck`, so both colliding responses open the statement's
shared commitment and satisfy its shortness condition.

This is an existential event on the statement and tree, not an algorithm producing a collision
or a bound on that algorithm's cost. -/
def nestedZeroCheckEsc (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ) :
    ChallengeTree.EscapeEvent (LiftStatement Φ K.TCom F n μ)
      (pSpecNestedZeroCheck F m₀ m₁) (nestedZeroCheckStructure F m₀ m₁).arity :=
  fun stmt tree =>
    ∃ resp : ChallengeTree.LeafPath tree → LiftedWitness Φ μ n,
      (∀ path, (nestedZcMapStmt Φ m₀ m₁ stmt
          (nestedZeroCheckTauZero path.fullTranscript)
          (nestedZeroCheckTauAlpha path.fullTranscript), resp path) ∈
        relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b) ∧
      ∃ p p', (resp p, resp p') ∈ K.Collision

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- **Correctness core of the nested-tree assembly.**

Either two leaves carry distinct openings — and then, both being short openings of the shared
commitment `t`, they are a member of `K.Collision` and the escape event fires — or every leaf
carries one opening `w̃`, and the single evaluation tree of depth `m₀ + m₁` reads `H₀` through its
first `m₀` levels (`Fin.castAdd`) and `H_α` through its last `m₁` (`Fin.natAdd`), so both
computable batching polynomials vanish identically and `w̃ ∈ relBatched`.

Every conjunct the collision side needs is supplied by `relNestedZeroCheck` itself: commitment
agreement and `liftShort` for each leaf. -/
theorem nestedAssembly_escape_or_mem_relBatched
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ) (stmt : LiftStatement Φ K.TCom F n μ)
    {arity : (pSpecNestedZeroCheck F m₀ m₁).ChallengeIdx → ℕ}
    (tree : ChallengeTree (pSpecNestedZeroCheck F m₀ m₁) arity 0)
    (resp : ChallengeTree.LeafPath tree → LiftedWitness Φ μ n)
    (base : ChallengeTree.LeafPath tree)
    (hrel : ∀ path, (nestedZcMapStmt Φ m₀ m₁ stmt
        (nestedZeroCheckTauZero path.fullTranscript)
        (nestedZeroCheckTauAlpha path.fullTranscript), resp path) ∈
      relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b)
    (evTree : NestedEvaluationTree F 2 (m₀ + m₁)) (hDistinct : evTree.IsDistinct)
    (hVanishes₀ : (∀ path, resp path = resp base) →
      CMlPolynomialEval.PolynomialVanishes evTree (hZero Φ m₀ φF b (resp base)) (Fin.castAdd m₁))
    (hVanishesα : (∀ path, resp path = resp base) →
      CMlPolynomialEval.PolynomialVanishes evTree
        (hAlpha Φ m₁ φF b stmt.1 stmt.2.2 (resp base)) (Fin.natAdd m₀)) :
    (∃ resp' : ChallengeTree.LeafPath tree → LiftedWitness Φ μ n,
        (∀ path, (nestedZcMapStmt Φ m₀ m₁ stmt
            (nestedZeroCheckTauZero path.fullTranscript)
            (nestedZeroCheckTauAlpha path.fullTranscript), resp' path) ∈
          relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b) ∧
        ∃ p p', (resp' p, resp' p') ∈ K.Collision) ∨
      (stmt, resp base) ∈ relBatched Φ m₀ m₁ bound bDig K φF b := by
  classical
  let : Decidable (∃ p, resp p ≠ resp base) := Classical.propDecidable _
  by_cases hcol : ∃ p, resp p ≠ resp base
  · -- two leaves disagree: their openings are a short collision of the shared `t`
    obtain ⟨p, hp⟩ := hcol
    refine Or.inl ⟨resp, hrel, p, base, hp, ?_, (hrel p).2.1, (hrel base).2.1⟩
    exact (hrel p).1.trans (hrel base).1.symm
  · -- all leaves share one opening: the tree zero test gives both identities
    push Not at hcol
    refine Or.inr ⟨(hrel base).1, ?_, ?_, (hrel base).2.2.2.2⟩
    · exact hZero_eq_zero_of_evaluationTree Φ m₀ (le_refl 2) φF b (resp base) evTree hDistinct
        (hVanishes₀ hcol)
    · exact hAlpha_eq_zero_of_evaluationTree Φ m₁ (le_refl 2) φF b stmt.1 stmt.2.2 (resp base)
        evTree hDistinct (hVanishesα hcol)

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- Coordinate-wise special soundness at `nestedZeroCheckExtractor`, with `nestedZeroCheckEsc`
as the escape event. The extraction argument uses two windows of one depth-`m₀ + m₁`
evaluation tree.

`nestedZeroCheck_numLeaves` and `nestedZeroCheck_numLeaves_lt` separately bound the
evaluation-tree adapter's leaf count.
This theorem bounds neither tree acquisition nor extraction time. -/
theorem nestedZeroCheck_coordinateWiseSpecialSoundWithEscape
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (nestedZeroCheckStructure F m₀ m₁)
      (nestedZeroCheckEsc Φ m₀ m₁ bound bDig K φF b)
      (relBatched Φ m₀ m₁ bound bDig K φF b)
      (relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b)
      (nestedZeroCheckVerifier (oSpec := oSpec) Φ (n := n) (μ := μ) (F := F)
        (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom))
      (nestedZeroCheckExtractor (Φ := Φ) (n := n) (μ := μ) (F := F) (m₀ := m₀) (m₁ := m₁)
        (TCom := K.TCom)) := by
  classical
  intro stmt tree hStruct hAcc
  by_cases hEsc : nestedZeroCheckEsc Φ m₀ m₁ bound bDig K φF b stmt tree
  · exact Or.inl hEsc
  · refine Or.inr ?_
    intro leafWits hValid
    let pureForm := nestedZeroCheckVerifierPureForm (oSpec := oSpec) Φ
      (n := n) (μ := μ) (F := F) (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom)
    have hne : (support init).Nonempty :=
      Verifier.support_init_nonempty_of_accepting hAcc (nestedLeftPath tree)
    have hValidPure : ∀ path : ChallengeTree.LeafPath tree, ∃ w,
        leafWits path = some w ∧
          (pureForm.verify stmt path.fullTranscript, w) ∈
            relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b :=
      (ChallengeTree.LeafWitnesses.isValid_iff_pure init impl pureForm.verify pureForm.verify_eq
        hne (relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b) stmt leafWits).mp hValid
    let resp : ChallengeTree.LeafPath tree → LiftedWitness Φ μ n :=
      fun path => (hValidPure path).choose
    have hrel : ∀ path : ChallengeTree.LeafPath tree,
        (nestedZcMapStmt Φ m₀ m₁ stmt
          (nestedZeroCheckTauZero path.fullTranscript)
          (nestedZeroCheckTauAlpha path.fullTranscript), resp path) ∈
            relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b := by
      intro path
      simpa [pureForm, nestedZeroCheckVerifierPureForm, resp] using
        (hValidPure path).choose_spec.2
    have hLeft : leafWits (nestedLeftPath tree) = some (resp (nestedLeftPath tree)) := by
      simpa [resp] using (hValidPure (nestedLeftPath tree)).choose_spec.1
    let evTree := nestedTreeToEvaluationTree F (m₀ + m₁) tree
    have hDistinct : evTree.IsDistinct :=
      nestedTreeToEvaluationTree_isDistinct F (m₀ + m₁) tree hStruct
    have hVanishes₀ : (∀ path, resp path = resp (nestedLeftPath tree)) →
        CMlPolynomialEval.PolynomialVanishes evTree (hZero Φ m₀ φF b (resp (nestedLeftPath tree)))
          (Fin.castAdd m₁) := by
      -- `H₀` reads the first `m₀` levels of the one tree.
      intro hall
      simp only [evTree, CMlPolynomialEval.PolynomialVanishes]
      apply nestedTreeToEvaluationTree_vanishes tree default
      intro path
      have hp := hrel path
      rw [hall path] at hp
      convert hp.2.2.1 using 1
      congr 2
      simp only [ChallengeTree.LeafPath.fullTranscript, nestedTranscriptSuffix_zero]
      funext i
      rfl
    have hVanishesα : (∀ path, resp path = resp (nestedLeftPath tree)) →
        CMlPolynomialEval.PolynomialVanishes evTree
          (hAlpha Φ m₁ φF b stmt.1 stmt.2.2 (resp (nestedLeftPath tree))) (Fin.natAdd m₀) := by
      -- `H_α` reads the last `m₁` levels of the same tree.
      intro hall
      simp only [evTree, CMlPolynomialEval.PolynomialVanishes]
      apply nestedTreeToEvaluationTree_vanishes tree default
      intro path
      have hp := hrel path
      rw [hall path] at hp
      convert hp.2.2.2.1 using 1
      congr 2
      simp only [ChallengeTree.LeafPath.fullTranscript, nestedTranscriptSuffix_zero]
      funext i
      rfl
    rcases nestedAssembly_escape_or_mem_relBatched Φ m₀ m₁ bound bDig K φF b stmt tree resp
      (nestedLeftPath tree) hrel evTree hDistinct hVanishes₀ hVanishesα with hEsc' | hBatched
    · exact (hEsc hEsc').elim
    · refine ⟨resp (nestedLeftPath tree), ?_, hBatched⟩
      simpa [nestedZeroCheckExtractor] using hLeft

/-- The nested scalar-round zero-check bundled for sequential composition, in the **escape-aware**
corner of the package lattice: the verifier is `pure (…)` and never fails, so it is a valid left
factor, while the weak-binding case needs the `esc` field.

The verifier is taken from `nestedZeroCheckReduction` rather than restated, so this certificate is
by construction a statement about the same protocol whose completeness is proved in
`ZeroCheck/Completeness.lean`. -/
def nestedZeroCheckPackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ) :
    EscapeCWSSPackage init impl
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁) (LiftedWitness Φ μ n)
      (pSpecNestedZeroCheck F m₀ m₁) where
  verifier := (nestedZeroCheckReduction (oSpec := oSpec) (n := n) (μ := μ) (F := F)
    (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom) (Wit := LiftedWitness Φ μ n) Φ).verifier
  struct := nestedZeroCheckStructure F m₀ m₁
  relIn := relBatched Φ m₀ m₁ bound bDig K φF b
  relOut := relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b
  isPure := nestedZeroCheckVerifierPureForm (oSpec := oSpec) Φ
    (n := n) (μ := μ) (F := F) (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom)
  esc := nestedZeroCheckEsc Φ m₀ m₁ bound bDig K φF b
  extractor := nestedZeroCheckExtractor (Φ := Φ) (n := n) (μ := μ) (F := F)
    (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom)
  isCWSS := nestedZeroCheck_coordinateWiseSpecialSoundWithEscape Φ m₀ m₁ bound bDig
    init impl K φF b

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
