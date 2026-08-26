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
  `H₀ ≡ 0 ∧ H_α ≡ 0` (`relBatched`, `ZeroCheck/Batch.lean`) to evaluations at direct points; the
  two
  evaluation claims then seed the sumcheck (`Sumcheck/Bridge.lean`). It is stated over the lifted
  witness `LiftedWitness Φ μ n` and the weak-binding `LiftCom`, and composes into the §4.3 opening
  chain (`Composition.lean`).

  ## Deviation from the paper's Lemma 10

  What fails in [NOZ26] is not Figure 5 but its proof: the attempt to certify the polynomial
  identity `H₀ ≡ 0` *deterministically*, from a coordinate-wise star of accepting transcripts. Two
  things go wrong at once (full analysis in `docs/kb/audits/noz26-zero-check-lemma10.md`):

  * *Shape.* `SS(S, ℓ, k)` is star-shaped by definition, so a coordinate-wise family only certifies
    that a multilinear `H` vanishes on the axis cross through the family's center — which for two
    or more variables does not imply `H ≡ 0`
    (`MvPolynomial.exists_nonzero_vanishing_on_axis_cross`), and putting more points on the
    same arms does not help. Under the lemma's own `ℓ = 2` reading the arms carry arbitrary distinct
    challenge *vectors* rather than collinear points, so the axis cross does not apply directly;
    there the objection is a dimension count — `D` points cannot pin down the `2 ^ m₀`-dimensional
    space of multilinears — which is *not* formalized here.
  * *Degree.* Lemma 10's `D = max (2 * d) (2 * b - 1)` is a degree in `α` (Lemma 9) and in the
    witness value `w̃(u, ℓ)` respectively; neither is a degree in a coordinate of `τ`. In `τ` both
    batching polynomials are multilinear, so two distinct labels per coordinate suffice. The
    printed lemma thus over-asks in `D` and under-asks in tree shape.

  Since `w̃` is committed before `τ` is drawn, the *protocol* is fine: Schwartz–Zippel gives
  knowledge error `≈ (m₀ + m₁) / |F|` for Figure 5 exactly as printed. That argument is
  probabilistic, so it does not fit the coordinate-wise special-soundness framework this chain
  composes in ([FMN24], `CWSSPackage`), which is why the repair below is stated instead.

  ## What the repair changes, and what it does not

  This formalization draws the coordinates of `τ₀` and `τα` as `m₀ + m₁` consecutive scalar
  rounds. Since **no prover message separates them** (`pSpecNestedScalar` has no `P_to_V` round),
  the *interactive* protocol is unchanged: the verifier map, the prover, and the uniform
  distribution on `F^{m₀ + m₁}` are the same as Figure 5's. What changes is the shape of transcript
  tree the extractor is handed — a path-dependent complete binary tree instead of a star — plus,
  under Fiat–Shamir, the requirement that the challenge coordinates be hashed *sequentially* rather
  than drawn from one atomic hash call.

  Path dependence is more than is needed here (a product grid of challenge vectors in the single
  original round would do, and is obtainable by rewinding a one-round prover). Round splitting is
  what lets `SS(S, ℓ, k)` and [FMN24] Lemma 4 be reused verbatim; expressing a product-shaped
  family instead would need a new soundness notion and new composition theorems.

  ## Coordinate-wise special soundness

  `nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` reads the complete binary transcript tree
  and lands in one of two cases:

  1. Two leaves carry **distinct** openings of the shared commitment `t`. Both are short (the
     `liftShort` conjunct of `relNestedZeroCheck`), so the pair is a member of `LiftCom.Collision`
     and the escape event `nestedZeroCheckEsc` fires — a Module-SIS break of the fixed key by
     [NOZ26] Lemma 7 / Remark 2. Weak binding is **not** a field of `LiftCom` and not an extractor
     output: it is an event on `(statement, tree)`, which is what keeps it from being trivially
     satisfiable (a compressing commitment's collision set is never empty).
  2. All leaves carry one opening `w̃`: `H₀` is read through the first `m₀` levels of the *one*
     evaluation tree and `H_α` through its last `m₁` levels
     (`NestedEvaluationTree.eq_zero_of_vanishes_comp`), yielding both polynomial identities, hence
     `relBatched` membership.

  This is a repaired scalar-round CWSS route rather than the paper's printed star extraction. Its
  complete tree has `2 ^ (m₀ + m₁)` leaves, and Fiat–Shamir must hash its coordinates sequentially.
  The extractor itself is executable: `ChallengeTree.LeafWitnesses` supplies an `Option` candidate
  output witness at every leaf, and `nestedZeroCheckExtractor` returns the all-left entry without
  searching the output relation. The certificate proves this lookup correct for *every* valid leaf
  witnessing. Classical choice is confined to the proof, where it assembles a total response family
  from validity witnesses in order to invoke the evaluation-tree argument. Tree size:
  `nestedZeroCheck_numLeaves`/`_lt`.

  ## Where the norm sits

  `relNestedZeroCheck` carries `liftShort` because that predicate is the commitment's *shortness
  index*: `LiftCom.Collision` is defined on pairs of distinct **short** openings, which is what an
  Ajtai-style scheme's binding actually gives — a collision of two long openings is no Module-SIS
  solution. So the conjunct is what makes the escape event sound, not a range assumption smuggled
  in ahead of its proof.

  The range claim proper — `RhoShort`, the `‖ρ‖∞ ≤ b − 1` half — is still **derived**, at the
  batching bridge, from `H₀ ≡ 0` (`hZero_eq_zero_imp_liftShort`), and `relBatched` remains
  norm-free. That separation is what this seam has to preserve, because it genuinely cannot
  recover the range identity: a single evaluation `H₀(τ₀) = 0` never implies `H₀ ≡ 0`.

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

/-! ### Size of the transcript tree

`CWSSStructure` carries no size bound, so `coordinateWiseSpecialSound` alone cannot tell a usable
repair from one whose family is exponential in the witness length. The two facts below record the
size, but note what they do and do not establish.

* `nestedZeroCheck_numLeaves` counts the leaves of the *adapter's* `NestedEvaluationTree`. The
quantity the extractor actually consumes is the number of `ChallengeTree.LeafPath`s of the
structured transcript tree; that the two agree is evident from the adapter but is **not
formalized**.
* `nestedZeroCheck_numLeaves_lt` is arithmetic on naturals. Minimality of `m₀`, `m₁` enters as its
  hypotheses and is **not enforced** anywhere in this development: `hμn` and `hn` bound the arities
  from below only, so an instantiation with oversized `m₀` satisfies every theorem here while
  blowing up the tree.

Concretely, at [NOZ26]'s `ℓ = 30` parameters (Fig. 9) the `H₀` table has `(μ + n) * deg φ ≈ 2 ^ 26`
entries, so `m₀ = 26`, and `rlinRows = 5` rows gives `m₁ = 3`: about `2 ^ 29` transcripts, against
the `2 * D - 1 = 4095` of the printed Lemma 10's `SS(F, 2, D)` family at
`D = max (2 * d) (2 * b - 1) = 2048`. Polynomial in the witness dimensions, but roughly `2 ^ 17`
times the paper's family — and since CWSS leaf counts multiply across rounds, that factor is what
the composed §4.3 chain (`Composition.lean`) inherits; no aggregate bound is stated there.

Only `2 ^ m₀ + 2 ^ m₁ - 1` leaves are *used* (`H₀` needs one accepting continuation per
`τ₀`-prefix, `H_α` one complete `m₁`-subtree), while `ChallengeTree.IsStructured` demands the
complete tree. For [FMN24] Lemma 4 to convert coordinate-wise special soundness into knowledge
soundness one needs `K = poly(λ)`; that lemma is not formalized in ArkLib, so nothing below is
connected to a knowledge-error statement. -/

/-- The evaluation tree the adapter produces has exactly `2 ^ (m₀ + m₁)` leaves: `m₀ + m₁` challenge
rounds, two pairwise-distinct children each. -/
theorem nestedZeroCheck_numLeaves {F : Type} {m₀ m₁ : ℕ}
    (tree : NestedEvaluationTree F 2 (m₀ + m₁)) : tree.numLeaves = 2 ^ (m₀ + m₁) :=
  tree.numLeaves_eq_pow

/-- With the two arities chosen *minimally* for their pins — `2 ^ m₀ < 2 * A` for
`A := (μ + n) * deg φ` (the `H₀` table size, cf. `hμn`) and `2 ^ m₁ < 2 * B` for `B := n` (the row
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
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ)
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

/-- The nested scalar-round verifier's purity as executable data.  Sequential composition runs
this verdict at its seam, so the package stores a `PureForm` rather than recovering a function
from a propositional purity witness. -/
def nestedZeroCheckVerifierPureForm {TCom : Type} :
    (nestedZeroCheckVerifier (oSpec := oSpec) Φ (n := n) (μ := μ) (F := F)
      (m₀ := m₀) (m₁ := m₁) (TCom := TCom)).PureForm where
  verify := fun stmt tr => nestedZcMapStmt Φ m₀ m₁ stmt
    (nestedZeroCheckTauZero tr) (nestedZeroCheckTauAlpha tr)
  verify_eq := fun _ _ => rfl

/-- Figure-5 honest prover. Since all rounds are verifier challenges, its state is the
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

/-- The Figure-5 zero-check **protocol**: the honest prover paired with the verifier.

This is the primary object of the link, and it is deliberately computable — it is what an honest
execution runs, what completeness is stated about (`ZeroCheck/Completeness.lean`), and what the
extraction rail consumes. The soundness certificate `nestedZeroCheckPackage` is a statement
*about* it: that package's `verifier` field is defined as this reduction's verifier, so the two
security directions cannot drift apart onto different verifiers. The certificate stays
`noncomputable` because it carries an extractor; nothing of that leaks into the protocol. -/
def nestedZeroCheckReduction {TCom Wit : Type} :
    Reduction oSpec (LiftStatement Φ TCom F n μ) Wit
      (NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) Wit
      (pSpecNestedZeroCheck F m₀ m₁) where
  prover := nestedZeroCheckProver Φ m₀ m₁
  verifier := nestedZeroCheckVerifier Φ m₀ m₁

/-- Figure-5 point relation: an opening of `t` at which the two computable batching polynomials
vanish at the direct points carried by the statement.

The `liftShort` conjunct is the commitment's **shortness index**, not a range assumption smuggled
in: it is what makes a pair of colliding branch openings a member of `LiftCom.Collision`, hence a
Module-SIS break under [NOZ26] Lemma 7 / Remark 2. Its `RhoShort` half — the range claim Lemma 10
exists to establish — is still *derived*, at the batching bridge, from `H₀ ≡ 0`
(`hZero_eq_zero_imp_liftShort`); it is never assumed here. What this seam genuinely cannot
recover, and does not pretend to, is the range identity itself: a single evaluation
`H₀(τ₀) = 0` never implies `H₀ ≡ 0`
(`MvPolynomial.exists_nonzero_vanishing_on_axis_cross`). -/
def relNestedZeroCheck (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Set (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.t ∧
    liftShort Φ bound ρBound p.2 ∧
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

/-- **The zero-check's escape event** (the weak-binding case of the corrected Lemma 10): the tree
admits per-leaf `relNestedZeroCheck`-responses among which two are **distinct short openings** of
the statement's commitment `t` — a member of `LiftCom.Collision`, hence a Module-SIS break of the
fixed key by [NOZ26] Lemma 7.

Against the `ChallengeTree.EscapeEvent` contract: the collision conjunct is an unconditional break
at *every* `(statement, tree)`; it mentions neither the extractor, nor acceptance, nor the
sampling; and the responses are pinned to the **output** relation, which is what keeps the event
tight — it cannot fire on trees where all leaves share one opening, which is exactly where
extraction succeeds. Both openings automatically open `t`: `relNestedZeroCheck`'s first conjunct
pins `K.com w = t` and every leaf's output statement carries the same `t`. -/
def nestedZeroCheckEsc (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    ChallengeTree.EscapeEvent (LiftStatement Φ K.TCom F n μ)
      (pSpecNestedZeroCheck F m₀ m₁) (nestedZeroCheckStructure F m₀ m₁).arity :=
  fun stmt tree =>
    ∃ resp : ChallengeTree.LeafPath tree → LiftedWitness Φ μ n,
      (∀ path, (nestedZcMapStmt Φ m₀ m₁ stmt
          (nestedZeroCheckTauZero path.fullTranscript)
          (nestedZeroCheckTauAlpha path.fullTranscript), resp path) ∈
        relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b) ∧
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
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (stmt : LiftStatement Φ K.TCom F n μ)
    {arity : (pSpecNestedZeroCheck F m₀ m₁).ChallengeIdx → ℕ}
    (tree : ChallengeTree (pSpecNestedZeroCheck F m₀ m₁) arity 0)
    (resp : ChallengeTree.LeafPath tree → LiftedWitness Φ μ n)
    (base : ChallengeTree.LeafPath tree)
    (hrel : ∀ path, (nestedZcMapStmt Φ m₀ m₁ stmt
        (nestedZeroCheckTauZero path.fullTranscript)
        (nestedZeroCheckTauAlpha path.fullTranscript), resp path) ∈
      relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b)
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
          relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b) ∧
        ∃ p p', (resp' p, resp' p') ∈ K.Collision) ∨
      (stmt, resp base) ∈ relBatched Φ m₀ m₁ bound ρBound K φF b := by
  classical
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
/-- **Escape-threaded coordinate-wise special soundness of the nested scalar-round zero-check**
(the corrected Hachi Lemma 10), at the named extractor `nestedZeroCheckExtractor`.

The weak-binding failure mode is the escape disjunct `nestedZeroCheckEsc`; the extraction side is
the evaluation-tree zero test through the two windows of one depth-`m₀ + m₁` tree. Tree size is
machine-checked by `nestedZeroCheck_numLeaves`/`_lt`. -/
theorem nestedZeroCheck_coordinateWiseSpecialSoundWithEscape
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (nestedZeroCheckStructure F m₀ m₁)
      (nestedZeroCheckEsc Φ m₀ m₁ bound ρBound K φF b)
      (relBatched Φ m₀ m₁ bound ρBound K φF b)
      (relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b)
      (nestedZeroCheckVerifier (oSpec := oSpec) Φ (n := n) (μ := μ) (F := F)
        (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom))
      (nestedZeroCheckExtractor (Φ := Φ) (n := n) (μ := μ) (F := F) (m₀ := m₀) (m₁ := m₁)
        (TCom := K.TCom)) := by
  classical
  intro stmt tree hStruct hAcc
  by_cases hEsc : nestedZeroCheckEsc Φ m₀ m₁ bound ρBound K φF b stmt tree
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
            relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b :=
      (ChallengeTree.LeafWitnesses.isValid_iff_pure init impl pureForm.verify pureForm.verify_eq
        hne (relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b) stmt leafWits).mp hValid
    let resp : ChallengeTree.LeafPath tree → LiftedWitness Φ μ n :=
      fun path => (hValidPure path).choose
    have hrel : ∀ path : ChallengeTree.LeafPath tree,
        (nestedZcMapStmt Φ m₀ m₁ stmt
          (nestedZeroCheckTauZero path.fullTranscript)
          (nestedZeroCheckTauAlpha path.fullTranscript), resp path) ∈
            relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b := by
      intro path
      simpa [pureForm, nestedZeroCheckVerifierPureForm, resp] using
        (hValidPure path).choose_spec.2
    have hLeft : leafWits (nestedLeftPath tree) = some (resp (nestedLeftPath tree)) := by
      simpa [resp] using (hValidPure (nestedLeftPath tree)).choose_spec.1
    let evTree : NestedEvaluationTree F 2 (m₀ + m₁) := by
      simpa using nestedTreeToEvaluationTree F (m₀ + m₁) tree
    have hDistinct : evTree.IsDistinct := by
      simpa [evTree] using nestedTreeToEvaluationTree_isDistinct F (m₀ + m₁) tree hStruct
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
      funext i
      simp only [Function.comp_apply, nestedTranscriptSuffix,
        ChallengeTree.LeafPath.fullTranscript]
      congr 1
      apply Fin.ext
      simp only [Fin.val_zero, Nat.zero_add, Fin.val_castAdd]
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
      funext i
      simp only [Function.comp_apply, nestedTranscriptSuffix,
        ChallengeTree.LeafPath.fullTranscript]
      congr 1
      apply Fin.ext
      simp only [Fin.val_zero, Nat.zero_add, Fin.val_natAdd]
    rcases nestedAssembly_escape_or_mem_relBatched Φ m₀ m₁ bound ρBound K φF b stmt tree resp
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
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    EscapeCWSSPackage init impl
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁) (LiftedWitness Φ μ n)
      (pSpecNestedZeroCheck F m₀ m₁) where
  verifier := (nestedZeroCheckReduction (oSpec := oSpec) (n := n) (μ := μ) (F := F)
    (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom) (Wit := LiftedWitness Φ μ n) Φ).verifier
  struct := nestedZeroCheckStructure F m₀ m₁
  relIn := relBatched Φ m₀ m₁ bound ρBound K φF b
  relOut := relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b
  isPure := nestedZeroCheckVerifierPureForm (oSpec := oSpec) Φ
    (n := n) (μ := μ) (F := F) (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom)
  esc := nestedZeroCheckEsc Φ m₀ m₁ bound ρBound K φF b
  extractor := nestedZeroCheckExtractor (Φ := Φ) (n := n) (μ := μ) (F := F)
    (m₀ := m₀) (m₁ := m₁) (TCom := K.TCom)
  isCWSS := nestedZeroCheck_coordinateWiseSpecialSoundWithEscape Φ m₀ m₁ bound ρBound
    init impl K φF b

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
