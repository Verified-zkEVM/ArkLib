/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Bridge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
  # Paired sumcheck rounds — Hachi Figure 6 / Lemma 11 — skeleton

  The sumcheck loop of Hachi §4.3: `m₀` rounds, each reducing the pair of
  partial-hypercube-sum claims (`roundRel i`, `ZeroCheck/Constraints.lean`) by one variable.

  ## Paired rounds

  Figure 7 runs the `H₀`- and `H_α`-sumchecks with **shared challenges**: each round's message
  is the *pair* of univariate round polynomials `(g_i^{(0)}, g_i^{(α)})` (degrees
  `roundDegZero b = 2b` resp. `roundDegAlpha = 2`), followed by one scalar challenge
  `a_i ← F` — the `pSpecScalar (RoundMsg F b) F` wire format.

  ## Guarded round verifiers

  The round check `g_i(0) + g_i(1) = target_{i−1}` (for both components) reads the *previous*
  target, which the next round's statement **drops** — so it cannot live in the output relation,
  and a pure-with-dummy convention destroys extractability (all siblings of a tree node share
  the message `g_i`, so a failed check would collapse every branch onto the same dummy). The
  round verifier is therefore **guarded**: `failure` on a failed check, which is
  exactly the paper's "valid transcripts" premise for Lemma 11.

  ## Per-round soundness (Lemma 11) and the loop

  Per-round CWSS at `k = max (2b) 2 + 1` (plain special soundness, `scalarStructure`): the
  branches of a tree node share the message pair; either two branch witnesses differ (the
  weak-binding **escape event** `roundEsc`, pointing at `LiftCom.Collision`) or the shared `w̃`
  makes
  `T ↦ ∑_{x} H(prefix, T, x) − g_i(T)` a degree-`≤ deg` polynomial with `deg + 1` distinct
  roots, hence zero; evaluating at `0, 1` and summing, the **guard's** `g_i(0) + g_i(1) =
  target_{i−1}` recovers the previous round's claim. (The guard fact is available to the round's
  own extraction: acceptance probability `1` on a guarded verifier forces `check = true`.)

  The loop is composed by **recursion over the binary guarded append**
  (`roundsChain count = roundsChain (count−1) ▷ roundPackage (count−1)`, base = the identity
  package), so the only composition machinery it consumes is `Guarded.lean`'s skeleton.

The loop's recursion pins the relation seams (`roundsChain_relIn` / `roundsChain_relOut`); the
  composed escape event is assembled by `ChallengeTree.EscapeEvent.append`.

  **Sorried**: the per-round extraction algorithm `roundExtractor` and the CWSS theorem
  `round_coordinateWiseSpecialSoundWithEscape` (Lemma 11).

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

section Wire

variable (F : Type) [Field F] (b : ℕ)

/-- A round message: the pair of univariate round polynomials `(g_i^{(0)}, g_i^{(α)})`, degree-
bounded by the pins (`roundDegZero b = 2b`, `roundDegAlpha = 2`). -/
@[reducible] def RoundMsg : Type :=
  ↥(Polynomial.degreeLE F (roundDegZero b : ℕ)) × ↥(Polynomial.degreeLE F (roundDegAlpha : ℕ))

/-- The concatenated wire format of `count` paired sumcheck rounds (each round is
`pSpecScalar (RoundMsg F b) F`: one message pair, one scalar challenge). -/
def roundsSpec : (count : ℕ) → ProtocolSpec (2 * count)
  | 0 => !p[]
  | count + 1 => roundsSpec count ++ₚ pSpecScalar (RoundMsg F b) F

/-- Challenges of the concatenated rounds are sampleable (by recursion over the append
instance, applied by name — the append instance does not fire automatically on the
equation-compiled `roundsSpec`). -/
instance roundsSpecSampleable [SampleableType F] :
    ∀ (count : ℕ) (i : (roundsSpec F b count).ChallengeIdx),
      SampleableType ((roundsSpec F b count).Challenge i)
  | 0, i => Fin.elim0 i.1
  | count + 1, i =>
    letI := roundsSpecSampleable count
    ProtocolSpec.instSampleableTypeChallengeAppend
      (pSpec₁ := roundsSpec F b count) (pSpec₂ := pSpecScalar (RoundMsg F b) F) i

end Wire

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [DecidableEq F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The round check ([NOZ26] Figure 6): both round polynomials sum to the current targets over
`{0, 1}`. `Bool`-valued so the guarded-verifier witness is definitional. -/
def roundCheck {TCom : Type} {i : ℕ} (stmt : RoundStatement Φ TCom F n μ i)
    (g : RoundMsg F b) : Bool :=
  decide (g.1.1.eval 0 + g.1.1.eval 1 = stmt.target₀) &&
    decide (g.2.1.eval 0 + g.2.1.eval 1 = stmt.targetα)

/-- The `i`-th round's **guarded** verifier ([NOZ26] Figure 6): on a passing check, extend the
challenge prefix by `a_i` and replace the targets by `(g_i^{(0)}(a_i), g_i^{(α)}(a_i))`;
otherwise `failure` (see the module docstring for why the check cannot live in the output
relation). -/
def roundVerifier {TCom : Type} (i : ℕ) :
    Verifier oSpec (RoundStatement Φ TCom F n μ i) (RoundStatement Φ TCom F n μ (i + 1))
      (pSpecScalar (RoundMsg F b) F) where
  verify := fun stmt tr =>
    if roundCheck Φ b stmt (tr.messages ⟨0, rfl⟩) then
      pure ⟨stmt.zc, Fin.snoc stmt.challenges (tr.challenges ⟨1, rfl⟩),
        (tr.messages ⟨0, rfl⟩).1.1.eval (tr.challenges ⟨1, rfl⟩),
        (tr.messages ⟨0, rfl⟩).2.1.eval (tr.challenges ⟨1, rfl⟩)⟩
    else failure

omit [NeZero q] [IsCyclotomic Φ] in
/-- **The round verifier's guardedness as data** (`Verifier.GuardedForm`): the guard is
`roundCheck` and the verdict is the extended-prefix / re-targeted statement, so `verify_eq` is
`rfl`.

The round package carries this instead of a `Verifier.IsGuarded` instance, because a composed chain
must *run* the left verdict at the seam to know which statement to extract the right factor at (and
the composed escape event must name it too); reading either off the `IsGuarded` existential would
cost `Classical.choice`. -/
def roundVerifierGuardedForm {TCom : Type} (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ b (n := n) (μ := μ) (TCom := TCom)
      (F := F) i).GuardedForm where
  check := fun stmt tr => roundCheck Φ b stmt (tr.messages ⟨0, rfl⟩)
  out := fun stmt tr =>
    ⟨stmt.zc, Fin.snoc stmt.challenges (tr.challenges ⟨1, rfl⟩),
     (tr.messages ⟨0, rfl⟩).1.1.eval (tr.challenges ⟨1, rfl⟩),
     (tr.messages ⟨0, rfl⟩).2.1.eval (tr.challenges ⟨1, rfl⟩)⟩
  verify_eq := fun _ _ => rfl

omit [NeZero q] [IsCyclotomic Φ] in
/-- The round verifier is guarded — definitionally, by `roundCheck`. -/
theorem roundVerifier_isGuarded {TCom : Type} (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ b (n := n) (μ := μ) (TCom := TCom)
      (F := F) i).IsGuarded :=
  ⟨fun stmt tr => roundCheck Φ b stmt (tr.messages ⟨0, rfl⟩),
   fun stmt tr =>
     ⟨stmt.zc, Fin.snoc stmt.challenges (tr.challenges ⟨1, rfl⟩),
      (tr.messages ⟨0, rfl⟩).1.1.eval (tr.challenges ⟨1, rfl⟩),
      (tr.messages ⟨0, rfl⟩).2.1.eval (tr.challenges ⟨1, rfl⟩)⟩,
   fun _ _ => rfl⟩

/-- The `i`-th round's honest prover skeleton ([NOZ26] Figure 6; completeness out of scope): the
round-polynomial pair is the parameter `computeG` (honestly: the partial hypercube sums of the
two sumcheck polynomials in the free variable), and the output witness carries `w̃` forward. -/
def roundProver {TCom : Type} (i : ℕ)
    (computeG : RoundStatement Φ TCom F n μ i → LiftedWitness Φ μ n → RoundMsg F b) :
    Prover oSpec (RoundStatement Φ TCom F n μ i) (LiftedWitness Φ μ n)
      (RoundStatement Φ TCom F n μ (i + 1)) (LiftedWitness Φ μ n)
      (pSpecScalar (RoundMsg F b) F) where
  PrvState
    | 0 => RoundStatement Φ TCom F n μ i × LiftedWitness Φ μ n
    | 1 => RoundStatement Φ TCom F n μ i × LiftedWitness Φ μ n
    | 2 => (RoundStatement Φ TCom F n μ i × LiftedWitness Φ μ n) × F
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeG st.1 st.2, st)
    | ⟨1, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, wit⟩, c⟩ =>
    pure (⟨stmt.zc, Fin.snoc stmt.challenges c,
      (computeG stmt wit).1.1.eval c, (computeG stmt wit).2.1.eval c⟩, wit)

variable [SampleableType F]

/-- Validity `2 ≤ k` of the round's soundness parameter `k = max (2b) 2 + 1`, named once so that the
extractor, the escape event and the certificate below are pinned to the *same* structure (and hence
the same arity). -/
theorem round_two_le_k : 2 ≤ max (roundDegZero b) roundDegAlpha + 1 := by
  have := Nat.le_max_right (roundDegZero b) roundDegAlpha
  unfold roundDegAlpha at *; omega

/-- **The Lemma 11 per-round escape event**: the tree's own message pair and challenge family admit
per-branch `roundRel (i+1)`-responses — at the branch's *guard output* statement, since the round
verifier replaces the targets rather than extending the statement, hence the `…OfValid` form — among
which two are **distinct short openings of the shared commitment** `stmt.zc.t`, i.e. a member of
`LiftCom.Collision` and so a Module-SIS break of the fixed key by [NOZ26] Lemma 7.

Against the escape-event contract (`ChallengeTree.EscapeEvent`): the collision conjunct is an
unconditional break at every `(statement, tree)`, and the event reads only the statement and the
tree (via `ScalarRound`'s readers), with responses pinned to the **output** relation, which keeps
it tight. It does mention the guard's output map, which is plain data — the same map the composed
`ChallengeTree.EscapeEvent.append` uses. -/
def roundEsc
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (i : ℕ) :
    ChallengeTree.EscapeEvent (RoundStatement Φ K.TCom F n μ i) (pSpecScalar (RoundMsg F b) F)
      (CWSSStructure.toShape
        (scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b))).arity :=
  ScalarRound.escEventScalarOfValid (round_two_le_k b)
    (fun stmt g fam j w =>
      (⟨stmt.zc, Fin.snoc stmt.challenges (fam j), g.1.1.eval (fam j), g.2.1.eval (fam j)⟩, w) ∈
        roundRel Φ m₀ m₁ bound ρBound K φF b (i + 1))
    (fun _ _ _ resp => ∃ j j', (resp j, resp j') ∈ K.Collision)

/-- **The Lemma 11 per-round extraction algorithm.**

**Sorried** — this def is the extraction *algorithm* itself (the case split of the proof plan on
`round_coordinateWiseSpecialSoundWithEscape`, ultimately the guarded scalar-round engine's
`ScalarRound.treeExtractorScalar`).

No `noncomputable` marker: the gap here is the missing algorithm, not an architectural obstruction,
so the marker set stays a record of *computability* debt only. Until the `sorry` is filled the
generated code panics when run. -/
def roundExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (i : ℕ) :
    Extractor.TreeBased (RoundStatement Φ K.TCom F n μ i) (LiftedWitness Φ μ n)
      (LiftedWitness Φ μ n) (pSpecScalar (RoundMsg F b) F)
      (CWSSStructure.toShape
        (scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b))).arity :=
  sorry

/-- **Hachi Lemma 11 (skeleton): per-round CWSS of the paired sumcheck round at
`k = max (2b) 2 + 1`, at the named `roundExtractor`** (the named form is deliberate — see
`Verifier.treeSpecialSoundWith`; closing this gap means filling the extractor and this
specification about it).

**Sorried.** Extraction plan (Lemma 11, case-faithful): the `k` accepting branches of a
tree node share the message pair `(g^{(0)}, g^{(α)})` and carry pairwise-distinct challenges
(`scalarStructure`'s injective family); if two branch openings differ, `roundEsc` fires (take the
left disjunct); otherwise the shared `w̃` makes both defect polynomials
`T ↦ hypercubeSum H (i+1) (snoc prefix T) − g(T)` (degrees `≤ 2b` resp. `≤ 2`) vanish at `k`
distinct points, hence identically; evaluating at `0, 1`, summing, and using the **guard fact**
`roundCheck = true` (available from acceptance on a guarded verifier) recovers the round-`i`
claims. Assembled via a guarded variant of the scalar-round machinery, whose guard fact comes from
`Verifier.not_accepting_of_failure` refuting the rejecting branch.

**TODO (reuse `Sumcheck/Structured`):** this round should be the existing structured sum-check
round (`ArkLib/ProofSystem/Sumcheck/Structured`) rather than the bespoke `roundVerifier` above —
its CWSS discharged by the (to-be-built, wire-format-generic / guarded) analog of the scalar-round
engine applied to `Structured.roundOracleVerifier`, with the round relations read off
`Structured.sumcheckConsistencyProp` / `computeRoundPoly`. The verifier wiring is left `sorry` for
now pending that reconciliation (see the `Sumcheck/Basic.lean` umbrella). -/
theorem round_coordinateWiseSpecialSoundWithEscape
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (i : ℕ) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b))
      (roundEsc Φ m₀ m₁ bound ρBound b K φF i)
      (roundRel Φ m₀ m₁ bound ρBound K φF b i)
      (roundRel Φ m₀ m₁ bound ρBound K φF b (i + 1))
      (roundVerifier (oSpec := oSpec) Φ b (TCom := K.TCom) i)
      (roundExtractor Φ bound ρBound b K φF i) := by
  sorry

/-- The `i`-th paired sumcheck round as a guarded `EscapeGCWSSPackage`: the guarded round
verifier with the `k = max (2b) 2 + 1` plain-special-soundness structure, reducing the round-`i`
seam to the round-`(i+1)` seam, with the weak-binding event `roundEsc` as its one escape-specific
field. Certificate: the sorried `round_coordinateWiseSpecialSoundWithEscape` (Lemma 11). -/
def roundPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (i : ℕ) :
    EscapeGCWSSPackage init impl
      (RoundStatement Φ K.TCom F n μ i) (LiftedWitness Φ μ n)
      (RoundStatement Φ K.TCom F n μ (i + 1)) (LiftedWitness Φ μ n)
      (pSpecScalar (RoundMsg F b) F) where
  verifier := roundVerifier (oSpec := oSpec) Φ b (TCom := K.TCom) i
  struct := scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b)
  relIn := roundRel Φ m₀ m₁ bound ρBound K φF b i
  relOut := roundRel Φ m₀ m₁ bound ρBound K φF b (i + 1)
  esc := roundEsc Φ m₀ m₁ bound ρBound b K φF i
  isGuarded := roundVerifierGuardedForm Φ b i
  extractor := roundExtractor Φ bound ρBound b K φF i
  isCWSS := round_coordinateWiseSpecialSoundWithEscape Φ m₀ m₁ bound ρBound b init impl K φF i

/-- The empty round loop has no challenges. -/
instance : IsEmpty (roundsSpec F b 0).ChallengeIdx := ⟨fun i => Fin.elim0 i.1⟩

/-- **The purity data of the round loop's base case** (`Verifier.GuardedForm`'s pure sibling): the
zero-round identity package at the head of `roundsChainAux` is a `ReduceClaim` head at
`mapStmt := id`, so its verdict is the input statement itself and `verify_eq` is `rfl`.

The recursion's base package carries this rather than a `Verifier.IsPure` instance, for the reason
every link in the chain does: the composed extractor must *run* the left verdict at the seam, and
reading it off the `IsPure` existential would cost `Classical.choice`. -/
def roundsBaseVerifierPureForm {TCom : Type} :
    (ReduceClaim.verifier oSpec
      (id : RoundStatement Φ TCom F n μ 0 → RoundStatement Φ TCom F n μ 0)).PureForm where
  verify := fun stmt _ => stmt
  verify_eq := fun _ _ => rfl

/-- **The composed sumcheck loop, with its seam invariant** (Hachi Figure 7's round phase):
`count` paired rounds chained by recursion over the binary guarded append (base case: the
zero-round identity package), together with the proofs that the composite's `relIn`/`relOut`
are the round-`0`/round-`count` seam relations — the recursion's seams are definitional only
*per instance*, not for an open `count`, so the invariant must ride along.

Only the relation seams need pinning; the composite's event is whatever the recursion built — a
nested disjunction of the per-round `roundEsc`s, each at its own subtree. -/
def roundsChainAux (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    (count : ℕ) →
      { P : EscapeGCWSSPackage init impl
          (RoundStatement Φ K.TCom F n μ 0) (LiftedWitness Φ μ n)
          (RoundStatement Φ K.TCom F n μ count) (LiftedWitness Φ μ n)
          (roundsSpec F b count) //
        P.relIn = roundRel Φ m₀ m₁ bound ρBound K φF b 0 ∧
        P.relOut = roundRel Φ m₀ m₁ bound ρBound K φF b count }
  | 0 =>
    ⟨EscapeCWSSPackage.toGuarded
      { verifier := ReduceClaim.verifier oSpec id
        struct := CWSSStructure.ofIsEmpty
        relIn := roundRel Φ m₀ m₁ bound ρBound K φF b 0
        relOut := roundRel Φ m₀ m₁ bound ρBound K φF b 0
        esc := fun _ _ => False
        isPure := roundsBaseVerifierPureForm Φ
        extractor := ReduceClaim.treeExtractor (fun _ w => w) CWSSStructure.ofIsEmpty
        isCWSS := Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _
          (ReduceClaim.verifier_coordinateWiseSpecialSoundWith
            (relIn := roundRel Φ m₀ m₁ bound ρBound K φF b 0)
            (relOut := roundRel Φ m₀ m₁ bound ρBound K φF b 0)
            (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
            (fun _ _ h => h)) },
     rfl, rfl⟩
  | count + 1 =>
    let prev := roundsChainAux init impl K φF count
    ⟨prev.1.append (roundPackage Φ m₀ m₁ bound ρBound b init impl K φF count) prev.2.2,
     prev.2.1, rfl⟩

/-- **The composed sumcheck loop** (Hachi Figure 7's round phase), from the round-`0` seam
(installed by the sumcheck bridge) to the round-`count` seam (consumed by the final-evaluation
step). Instantiated at `count := m₀` in the composition. -/
def roundsChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (count : ℕ) :
    EscapeGCWSSPackage init impl
      (RoundStatement Φ K.TCom F n μ 0) (LiftedWitness Φ μ n)
      (RoundStatement Φ K.TCom F n μ count) (LiftedWitness Φ μ n)
      (roundsSpec F b count) :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF count).1

/-- The loop's input seam is the round-`0` relation (the seam pin for composing after the
sumcheck bridge). -/
theorem roundsChain_relIn (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (count : ℕ) :
    (roundsChain Φ m₀ m₁ bound ρBound b init impl K φF count).relIn =
      roundRel Φ m₀ m₁ bound ρBound K φF b 0 :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF count).2.1

/-- The loop's output seam is the round-`count` relation (the seam pin for composing with the
final-evaluation step). -/
theorem roundsChain_relOut (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (count : ℕ) :
    (roundsChain Φ m₀ m₁ bound ρBound b init impl K φF count).relOut =
      roundRel Φ m₀ m₁ bound ρBound K φF b count :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF count).2.2

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
