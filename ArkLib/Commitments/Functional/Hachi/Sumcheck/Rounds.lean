/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas, Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Bridge
import ArkLib.Commitments.Functional.Hachi.Sumcheck.RoundPoly
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded
import CompPoly.Univariate.Linear

/-!
  # Paired sumcheck rounds — Hachi Figure 6 / Lemma 11

  The sumcheck loop of Hachi §4.3: `m₀` rounds, each reducing the pair of
  partial-hypercube-sum claims (`nestedRoundRel i`, `ZeroCheck/Constraints.lean`) by one variable.

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
  package), so the only composition machinery it consumes is `Guarded.lean`'s guarded append —
  itself proven, including the escape-threaded form this loop instantiates.
  The loop's recursion pins the relation seams (`roundsChain_relIn` / `roundsChain_relOut`); the
  composed escape event is assembled by `ChallengeTree.EscapeEvent.append`.

  **Status**: Lemma 11 (`round_coordinateWiseSpecialSoundWithEscape`) and its named extractor
  `roundExtractor` are **proven and axiom-clean** (as is the whole `roundsChain`), on top of the
  generic guarded scalar-round engine
  `ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar_guarded` and the
  round-polynomial layer of `Sumcheck/RoundPoly.lean`. Two side conditions ride along and are
  genuinely load-bearing, both discussed at the theorem: `i < m₀` (a round needs a free cube
  coordinate to split on) and `0 < b` (the range summand's `2b` degree pin degenerates at `b = 0`).
  The honest prover `roundProver` is a skeleton: its round message is the parameter `computeG`,
  which the (not yet written) completeness layer has to supply — see `Sumcheck/Basic.lean`.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

section Wire

variable (F : Type) [Field F] (b : ℕ)

/-- A round message: the pair of computable univariate round polynomials
`(g_i^{(0)}, g_i^{(α)})`, degree-bounded by the R8 pins (`roundDegZero b = 2b`,
`roundDegAlpha = 2`). `CPolynomial.degreeLE_toPoly` connects each component to Mathlib's
`Polynomial.degreeLE` when a proof needs the Mathlib API. -/
@[reducible] def RoundMsg : Type :=
  ↥(CPolynomial.degreeLE (R := F) (roundDegZero b : ℕ)) ×
    ↥(CPolynomial.degreeLE (R := F) (roundDegAlpha : ℕ))

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
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The round check ([NOZ26] Figure 6): both round polynomials sum to the current targets over
`{0, 1}`. `Bool`-valued (design G3) so the guarded-verifier witness is definitional, and phrased
with `==` — the same `[BEq F] [LawfulBEq F]` idiom as `finalCheck` (`Sumcheck/FinalEval.lean`), so
that unpacking a guard fact is `beq_iff_eq` at every guarded seam of the folder. -/
def roundCheck {TCom : Type} {i : ℕ}
    (stmt : NestedRoundStatement Φ TCom F n μ m₀ m₁ i)
    (g : RoundMsg F b) : Bool :=
  (g.1.1.eval 0 + g.1.1.eval 1 == stmt.target₀) &&
    (g.2.1.eval 0 + g.2.1.eval 1 == stmt.targetα)

/-- The `i`-th round's **output map** ([NOZ26] Figure 6): extend the challenge prefix by `a_i` and
replace the two targets by the round polynomials' values there. Named once, so that the verifier,
its guard witness, the escape event and the extractor are all pinned to the *same* map (the
guarded scalar-round engine takes it as the `out` parameter). -/
def roundOut {TCom : Type} {i : ℕ}
    (stmt : NestedRoundStatement Φ TCom F n μ m₀ m₁ i) (g : RoundMsg F b) (a : F) :
    NestedRoundStatement Φ TCom F n μ m₀ m₁ (i + 1) :=
  ⟨stmt.zc, Fin.snoc stmt.challenges a, g.1.1.eval a, g.2.1.eval a⟩

/-- The `i`-th round's **guarded** verifier ([NOZ26] Figure 6): on a passing check, apply
`roundOut`; otherwise `failure` (see the module docstring for why the check cannot live in the
output relation). -/
def roundVerifier {TCom : Type} (i : ℕ) :
    Verifier oSpec (NestedRoundStatement Φ TCom F n μ m₀ m₁ i)
      (NestedRoundStatement Φ TCom F n μ m₀ m₁ (i + 1))
      (pSpecScalar (RoundMsg F b) F) where
  verify := fun stmt tr =>
    if roundCheck Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩) then
      pure (roundOut Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩))
    else failure

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The round verifier is guarded **with** the round check and `roundOut` — definitionally. This is
the form the guarded scalar-round engine consumes. -/
theorem roundVerifier_isGuardedWith {TCom : Type} (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ m₀ m₁ b (n := n) (μ := μ) (TCom := TCom)
      (F := F) i).IsGuardedWith
      (fun stmt tr => roundCheck Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩))
      (fun stmt tr =>
        roundOut Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩)) :=
  fun _ _ => rfl

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The round verifier is guarded — definitionally, by `roundCheck`. -/
theorem roundVerifier_isGuarded {TCom : Type} (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ m₀ m₁ b (n := n) (μ := μ) (TCom := TCom)
      (F := F) i).IsGuarded :=
  ⟨_, _, roundVerifier_isGuardedWith Φ m₀ m₁ b i⟩

/-- The `i`-th round's honest prover skeleton ([NOZ26] Figure 6; completeness out of scope): the
round-polynomial pair is the parameter `computeG` (honestly: the partial hypercube sums of the
two sumcheck polynomials in the free variable), and the output witness carries `w̃` forward. -/
def roundProver {TCom Wit : Type} (i : ℕ)
    (computeG : NestedRoundStatement Φ TCom F n μ m₀ m₁ i → Wit → RoundMsg F b) :
    Prover oSpec (NestedRoundStatement Φ TCom F n μ m₀ m₁ i) Wit
      (NestedRoundStatement Φ TCom F n μ m₀ m₁ (i + 1)) Wit
      (pSpecScalar (RoundMsg F b) F) where
  PrvState
    | 0 => NestedRoundStatement Φ TCom F n μ m₀ m₁ i × Wit
    | 1 => NestedRoundStatement Φ TCom F n μ m₀ m₁ i × Wit
    | 2 => (NestedRoundStatement Φ TCom F n μ m₀ m₁ i × Wit) × F
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
    ChallengeTree.EscapeEvent (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ i)
      (pSpecScalar (RoundMsg F b) F)
      (CWSSStructure.toShape
        (scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b))).arity :=
  ScalarRound.escEventScalarOfValid (round_two_le_k b)
    (fun stmt g fam j w =>
      (roundOut Φ m₀ m₁ b stmt g (fam j), w) ∈
        nestedRoundRel Φ m₀ m₁ bound ρBound K φF b (i + 1))
    (fun _ _ _ resp => ∃ j j', (resp j, resp j') ∈ K.Collision)

/-- **The Lemma 11 per-round extraction algorithm**: the guarded scalar-round tree extractor at the
round's own output map, assembling the `k` per-branch openings by **taking the first one**.

That trivial-looking assembler is the whole of the paper's extraction: on a structured accepting
tree the `k` branch openings either disagree — and then the escape event `roundEsc` fires, since
two distinct short openings of the shared `stmt.zc.t` are a `LiftCom.Collision` — or they are all
the *same* `w̃`, and it is `w̃` (read off any branch) that satisfies the round-`i` claim. The work
is in the certificate `round_coordinateWiseSpecialSoundWithEscape`, not in the algorithm. -/
noncomputable def roundExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (i : ℕ) :
    Extractor.TreeBased (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ i) (LiftedWitness Φ μ n)
      (pSpecScalar (RoundMsg F b) F)
      (CWSSStructure.toShape
        (scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b))).arity :=
  ScalarRound.treeExtractorScalarOfValid (round_two_le_k b)
    (fun stmt g a => roundOut Φ m₀ m₁ b stmt g a)
    (nestedRoundRel Φ m₀ m₁ bound ρBound K φF b (i + 1))
    (fun _ _ _ resp => resp ⟨0, Nat.succ_pos _⟩)

omit [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [IsCyclotomic Φ]
  [BEq F] [LawfulBEq F] [SampleableType F] in
/-- **The interpolation kernel of Lemma 11.** Two univariate polynomials of degree `≤ D` that agree
at `k > D` pairwise-distinct points are equal. This is what upgrades "the partial cube sum agrees
with the prover's round polynomial at the `k` sibling challenges" into "it agrees with it
everywhere", and in particular at `0` and `1` — the two points the round guard reads. -/
theorem eq_of_agree_on_injective_family {k D : ℕ} {P Q : Polynomial F}
    (hP : P.degree ≤ (D : WithBot ℕ)) (hQ : Q.degree ≤ (D : WithBot ℕ)) (hDk : D < k)
    {fam : Fin k → F} (hinj : Function.Injective fam)
    (h : ∀ j, P.eval (fam j) = Q.eval (fam j)) : P = Q :=
  Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q hinj h <| by
    have h₁ := Polynomial.natDegree_le_iff_degree_le.mpr hP
    have h₂ := Polynomial.natDegree_le_iff_degree_le.mpr hQ
    rw [Fintype.card_fin]
    omega

omit [NeZero q] [SampleableType F] in
/-- **Hachi Lemma 11: per-round CWSS of the paired sumcheck round at `k = max (2b) 2 + 1`, at the
named `roundExtractor`** (the named form is deliberate — see `Verifier.treeSpecialSoundWith`).

Extraction (Lemma 11, case-faithful): the `k` accepting branches of a tree node share the message
pair `(g^{(0)}, g^{(α)})` and carry pairwise-distinct challenges (`scalarStructure`'s injective
family, `ScalarRound.injective_of_nodeOk`). If two branch openings differ, `roundEsc` fires — both
open the *same* commitment `stmt.zc.t` (the round verifier copies `zc` through) and both are
`liftShort`, so the pair is a `LiftCom.Collision`, hence a Module-SIS break by [NOZ26] Lemma 7.
Otherwise all branches carry one shared `w̃`, and then for each of the two summands the partial cube
sum in the free coordinate is an honest univariate — `roundPoly`, of degree `≤ 2b` resp. `≤ 2`
(`roundPoly_degree_le_sumcheckPolyZero` / `…Alpha`) — agreeing with the prover's degree-matched
`g` at `k > deg` distinct points, hence equal to it as a polynomial
(`eq_of_agree_on_injective_family`). Evaluating at `0` and `1`, summing via the cube split
`hypercubeSum_succ`, and using the **guard fact** `roundCheck = true` (delivered to `hmk` by the
guarded engine, from acceptance of every branch) recovers the round-`i` claims. All the tree
plumbing is the generic
`ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar_guarded`.

**The `i < m₀` hypothesis is necessary, not bookkeeping.** The final step above splits the
round-`i` cube sum as `hypercubeSum H i cs = hypercubeSum H (i+1) (snoc cs 0) +
hypercubeSum H (i+1) (snoc cs 1)`, which needs a free coordinate to split on. For `m₀ ≤ i` there
is none: `hypercubeSum` has saturated (`hypercubeSum_of_le`, `ZeroCheck/Constraints.lean`), both
sides of the defect are constant in the challenge, and the guard delivers
`2·hypercubeSum H i cs = target` where the round-`i` claim asks for `hypercubeSum H i cs = target`.
So the statement is *false* without the hypothesis, over any `F` of characteristic `≠ 2` and with
a nonzero target. The loop only ever instantiates rounds `0, …, m₀ − 1`, so nothing is lost;
`roundsChainAux` threads the corresponding `count ≤ m₀`.

**`0 < b` is likewise load-bearing**, and only on the range side: the round message's `g^{(0)}`
component is pinned to degree `≤ roundDegZero b = 2b`, and at `b = 0` the range factor
`P_0(v) = v` is degree `1 > 0`, so the summand would overflow its own pin
(`degreeOf_sumcheckPolyZero` carries the same hypothesis). Every instantiation has `b ≥ 2` (the
decomposition base; `b = 16` at the paper's parameters). -/
theorem round_coordinateWiseSpecialSoundWithEscape
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) (i : ℕ) (hi : i < m₀) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b))
      (roundEsc Φ m₀ m₁ bound ρBound b K φF i)
      (nestedRoundRel Φ m₀ m₁ bound ρBound K φF b i)
      (nestedRoundRel Φ m₀ m₁ bound ρBound K φF b (i + 1))
      (roundVerifier (oSpec := oSpec) Φ m₀ m₁ b (TCom := K.TCom) i)
      (roundExtractor Φ m₀ m₁ bound ρBound b K φF i) := by
  classical
  -- A round exists only when a cube coordinate is left to fold, so `m₀` is a successor.
  obtain ⟨M, rfl⟩ : ∃ M, m₀ = M + 1 := ⟨m₀ - 1, by omega⟩
  refine ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar_guarded
    init impl (round_two_le_k b) _
    (fun stmt g _ => roundCheck Φ (M + 1) m₁ b stmt g)
    (fun stmt g a => roundOut Φ (M + 1) m₁ b stmt g a)
    (roundVerifier_isGuardedWith Φ (M + 1) m₁ b i) _ _ _ _ ?_
  intro s g fam resp hcheck hresp hinj
  -- The index of the branch the assembler reads, and its opening.
  set z : Fin (max (roundDegZero b) roundDegAlpha + 1) := ⟨0, Nat.succ_pos _⟩ with hz
  by_cases hall : ∀ j, resp j = resp z
  case neg =>
    -- Two branches open the shared commitment `s.zc.t` differently: a short collision.
    refine Or.inl ?_
    push Not at hall
    obtain ⟨j, hj⟩ := hall
    exact ⟨j, z, hj, ((hresp j).1).trans ((hresp z).1).symm, (hresp j).2.1, (hresp z).2.1⟩
  case pos =>
  -- The guard fact, unpacked once: both round polynomials sum to the round-`i` targets on `{0,1}`.
  have hguard := hcheck z
  simp only [roundCheck, Bool.and_eq_true, beq_iff_eq] at hguard
  refine Or.inr ⟨(hresp z).1, (hresp z).2.1, ?_, ?_, (hresp z).2.2.2.2⟩
  · -- The range sumcheck claim.
    have hdefect : roundPoly (sumcheckPolyZero Φ (M + 1) φF b s.zc.τ₀ (resp z))
        ⟨i, hi⟩ s.challenges = (g.1.1).toPoly := by
      refine eq_of_agree_on_injective_family
        (roundPoly_degree_le_sumcheckPolyZero Φ hb φF s.zc.τ₀ (resp z) ⟨i, hi⟩ s.challenges)
        (Polynomial.mem_degreeLE.mp (CPolynomial.degreeLE_toPoly.mp g.1.2))
        (Nat.lt_succ_of_le (le_max_left _ _)) hinj fun j => ?_
      rw [roundPoly_eval, ← CPolynomial.eval_toPoly]
      have h := (hresp j).2.2.1
      rw [hall j] at h
      exact h
    have key : hypercubeSum (M + 1) (sumcheckPolyZero Φ (M + 1) φF b s.zc.τ₀ (resp z))
        ((⟨i, hi⟩ : Fin (M + 1)) : ℕ) s.challenges = s.target₀ := by
      rw [hypercubeSum_succ, ← roundPoly_eval, ← roundPoly_eval, hdefect,
        ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]
      exact hguard.1
    exact key
  · -- The linear sumcheck claim, at the `roundDegAlpha = 2` pin.
    have hdefect : roundPoly
        (sumcheckPolyAlpha Φ (M + 1) m₁ φF b s.zc.rlin s.zc.α s.zc.τα (resp z))
        ⟨i, hi⟩ s.challenges = (g.2.1).toPoly := by
      refine eq_of_agree_on_injective_family
        (roundPoly_degree_le_sumcheckPolyAlpha Φ φF b s.zc.rlin s.zc.α m₁ s.zc.τα
          (resp z) ⟨i, hi⟩ s.challenges)
        (Polynomial.mem_degreeLE.mp (CPolynomial.degreeLE_toPoly.mp g.2.2))
        (Nat.lt_succ_of_le (le_max_right _ _)) hinj fun j => ?_
      rw [roundPoly_eval, ← CPolynomial.eval_toPoly]
      have h := (hresp j).2.2.2.1
      rw [hall j] at h
      exact h
    have key : hypercubeSum (M + 1)
        (sumcheckPolyAlpha Φ (M + 1) m₁ φF b s.zc.rlin s.zc.α s.zc.τα (resp z))
        ((⟨i, hi⟩ : Fin (M + 1)) : ℕ) s.challenges = s.targetα := by
      rw [hypercubeSum_succ, ← roundPoly_eval, ← roundPoly_eval, hdefect,
        ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]
      exact hguard.2
    exact key

/-- The `i`-th paired sumcheck round as a guarded `EscapeGCWSSPackage`: the guarded round verifier
with the `k = max (2b) 2 + 1` plain-special-soundness structure, reducing the round-`i` seam to the
round-`(i+1)` seam, with the weak-binding event `roundEsc` as its one escape-specific field.
Certificate: `round_coordinateWiseSpecialSoundWithEscape` (Lemma 11), whence the `i < m₀` and
`0 < b` hypotheses — a round only reduces a claim while a free cube coordinate remains, and the
range summand only respects its `2b` degree pin for a nondegenerate base. -/
noncomputable def roundPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) (i : ℕ) (hi : i < m₀) :
    EscapeGCWSSPackage init impl
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ i) (LiftedWitness Φ μ n)
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ (i + 1)) (LiftedWitness Φ μ n)
      (pSpecScalar (RoundMsg F b) F) where
  verifier := roundVerifier (oSpec := oSpec) Φ m₀ m₁ b (TCom := K.TCom) i
  struct := scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b)
  relIn := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b i
  relOut := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b (i + 1)
  esc := roundEsc Φ m₀ m₁ bound ρBound b K φF i
  isGuarded := roundVerifier_isGuarded Φ m₀ m₁ b i
  extractor := roundExtractor Φ m₀ m₁ bound ρBound b K φF i
  isCWSS :=
    round_coordinateWiseSpecialSoundWithEscape Φ m₀ m₁ bound ρBound b init impl K φF hb i hi

/-- The empty round loop has no challenges. -/
instance : IsEmpty (roundsSpec F b 0).ChallengeIdx := ⟨fun i => Fin.elim0 i.1⟩

/-- **The composed sumcheck loop, with its seam invariant** (Hachi Figure 7's round phase):
`count` paired rounds chained by recursion over the binary guarded append (base case: the
zero-round identity package), together with the proofs that the composite's `relIn`/`relOut`
are the round-`0`/round-`count` seam relations — the recursion's seams are definitional only
*per instance*, not for an open `count`, so the invariant must ride along.

Only the relation seams need pinning; the composite's event is whatever the recursion built — a
nested disjunction of the per-round `roundEsc`s, each at its own subtree. -/
noncomputable def roundsChainAux (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) :
    (count : ℕ) → count ≤ m₀ →
      { P : EscapeGCWSSPackage init impl
          (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ 0) (LiftedWitness Φ μ n)
          (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ count) (LiftedWitness Φ μ n)
          (roundsSpec F b count) //
        P.relIn = nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0 ∧
        P.relOut = nestedRoundRel Φ m₀ m₁ bound ρBound K φF b count }
  | 0, _ =>
    ⟨EscapeCWSSPackage.toGuarded
      { verifier := ReduceClaim.verifier oSpec id
        struct := CWSSStructure.ofIsEmpty
        relIn := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0
        relOut := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0
        esc := fun _ _ => False
        isPure := ⟨fun stmt _ => stmt, fun _ _ => rfl⟩
        extractor := ReduceClaim.treeExtractor (mapStmt := id)
          (nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0) (fun _ w => w)
          CWSSStructure.ofIsEmpty
        isCWSS := Verifier.coordinateWiseSpecialSoundWith.withEscape init impl _
          (ReduceClaim.verifier_coordinateWiseSpecialSoundWith
            (relIn := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0)
            (relOut := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0)
            (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
            (fun _ _ h => h)) },
     rfl, rfl⟩
  | count + 1, hcount =>
    let prev := roundsChainAux init impl K φF hb count (by omega)
    ⟨prev.1.append
      (roundPackage Φ m₀ m₁ bound ρBound b init impl K φF hb count (by omega)) prev.2.2,
     prev.2.1, rfl⟩

/-- **The composed sumcheck loop** (Hachi Figure 7's round phase), from the round-`0` seam
(installed by the sumcheck bridge) to the round-`count` seam (consumed by the final-evaluation
step). Instantiated at `count := m₀` in the composition, where `hcount` is `le_rfl`. -/
noncomputable def roundsChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) (count : ℕ) (hcount : count ≤ m₀) :
    EscapeGCWSSPackage init impl
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ 0) (LiftedWitness Φ μ n)
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ count) (LiftedWitness Φ μ n)
      (roundsSpec F b count) :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF hb count hcount).1

omit [NeZero q] in
/-- The loop's input seam is the round-`0` relation (the seam pin for composing after the
sumcheck bridge). -/
theorem roundsChain_relIn (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) (count : ℕ) (hcount : count ≤ m₀) :
    (roundsChain Φ m₀ m₁ bound ρBound b init impl K φF hb count hcount).relIn =
      nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0 :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF hb count hcount).2.1

omit [NeZero q] in
/-- The loop's output seam is the round-`count` relation (the seam pin for composing with the
final-evaluation step). -/
theorem roundsChain_relOut (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) (count : ℕ) (hcount : count ≤ m₀) :
    (roundsChain Φ m₀ m₁ bound ρBound b init impl K φF hb count hcount).relOut =
      nestedRoundRel Φ m₀ m₁ bound ρBound K φF b count :=
  (roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF hb count hcount).2.2

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
