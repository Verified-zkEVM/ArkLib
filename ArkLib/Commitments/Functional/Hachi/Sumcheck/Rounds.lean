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
  # Paired sumcheck rounds

  The sumcheck loop of Hachi §4.3: `m₀` rounds, each reducing the pair of
  partial-hypercube-sum claims (`nestedRoundRel i`, `ZeroCheck/Constraints.lean`) by one
  variable.

  The two sumchecks (for `H₀` and `H_α`) run with shared challenges: each round's message is
  the pair of univariate round polynomials `(g_i^{(0)}, g_i^{(α)})` (degrees
  `roundDegZero b = 2b` resp. `roundDegAlpha = 2`), followed by one scalar challenge
  `a_i ← F` — the `pSpecScalar (RoundMsg F b) F` wire format.

  The round check `g_i(0) + g_i(1) = target_{i−1}` (for both components) reads the previous
  target, which the next round's statement drops, so it cannot live in the output relation.
  The round verifier is therefore *guarded*: it returns `failure` on a failed check rather
  than a dummy output. (A dummy output would collapse all siblings of a challenge-tree node
  — which share the message `g_i` — onto the same statement and destroy extractability.)

  Soundness is per-round coordinate-wise special soundness at `k = max (2b) 2 + 1`
  (`round_coordinateWiseSpecialSoundWithEscape`): the branches of a tree node share the
  message pair, so either two branch witnesses differ — two distinct short openings of the
  same commitment, the escape event `roundEsc` — or all branches share one witness, whose
  partial sums agree with the round polynomials at `k` distinct challenges and hence
  everywhere; evaluating at `0` and `1` and using the round check recovers the previous
  round's claim. The computable extractor reads the designated branch opening from the
  supplied valid leaf witnessing.

  The loop `roundsChain` composes the rounds by recursion over the binary guarded append, and
  **re-pins the relation seams definitionally** — `roundsChain_relIn` / `roundsChain_relOut`
  hold by `rfl`, so the loop composes with the universal `▷`.
  The honest prover `roundProver` is a skeleton parameterized by the round-message function
  `computeG`; `Sumcheck/Completeness.lean` instantiates it at `honestComputeG` (the computable
  partial hypercube sums of `Sumcheck/RoundPoly.lean`) and proves one round's perfect
  completeness.

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
`(g_i^{(0)}, g_i^{(α)})`, of degree `≤ roundDegZero b = 2b` resp. `≤ roundDegAlpha = 2`.
`CPolynomial.degreeLE_toPoly` connects each component to Mathlib's `Polynomial.degreeLE`
when a proof needs the Mathlib API. -/
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
variable {n μ : ℕ} {F : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ) (b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The round check: both round polynomials sum to the current targets over `{0, 1}`.
`Bool`-valued and phrased with `==` (as `finalCheck` in `Sumcheck/FinalEval.lean`), so a
passed check unpacks with `beq_iff_eq`. -/
def roundCheck {TCom : Type} {i : ℕ}
    (stmt : NestedRoundStatement Φ TCom F n μ m₀ m₁ i)
    (g : RoundMsg F b) : Bool :=
  (g.1.1.eval 0 + g.1.1.eval 1 == stmt.target₀) &&
    (g.2.1.eval 0 + g.2.1.eval 1 == stmt.targetα)

/-- The `i`-th round's output map: extend the challenge prefix by `a_i` and replace the two
targets by the round polynomials' values there. Named once so that the verifier, its guard
witness, the escape event and the extractor all refer to the same map. -/
def roundOut {TCom : Type} {i : ℕ}
    (stmt : NestedRoundStatement Φ TCom F n μ m₀ m₁ i) (g : RoundMsg F b) (a : F) :
    NestedRoundStatement Φ TCom F n μ m₀ m₁ (i + 1) :=
  ⟨stmt.zc, Fin.snoc stmt.challenges a, g.1.1.eval a, g.2.1.eval a⟩

/-- The `i`-th round's verifier: on a passing `roundCheck`, apply `roundOut`; otherwise
`failure`. -/
def roundVerifier {TCom : Type} (i : ℕ) :
    Verifier oSpec (NestedRoundStatement Φ TCom F n μ m₀ m₁ i)
      (NestedRoundStatement Φ TCom F n μ m₀ m₁ (i + 1))
      (pSpecScalar (RoundMsg F b) F) where
  verify := fun stmt tr =>
    if roundCheck Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩) then
      pure (roundOut Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩) (tr.challenges ⟨1, rfl⟩))
    else failure

omit [NeZero q] [IsCyclotomic Φ] in
/-- The round verifier's guardedness as computable data (`Verifier.GuardedForm`): the guard is
`roundCheck` and the verdict is the extended-prefix / re-targeted statement, so `verify_eq` is
`rfl`.

The round package carries this instead of a `Verifier.IsGuarded` instance, because a composed chain
must *run* the left verdict at the seam to know which statement to extract the right factor at (and
the composed escape event must name it too); reading either off the `IsGuarded` existential would
cost `Classical.choice`. -/
def roundVerifierGuardedForm {TCom : Type} (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ m₀ m₁ b (n := n) (μ := μ) (TCom := TCom)
      (F := F) i).GuardedForm where
  check := fun stmt tr => roundCheck Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩)
  out := fun stmt tr => roundOut Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩)
    (tr.challenges ⟨1, rfl⟩)
  verify_eq := fun _ _ => rfl

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The round verifier is guarded **with** the round check and `roundOut` — definitionally. This is
the form the guarded scalar-round engine consumes. -/
theorem roundVerifier_isGuardedWith {TCom : Type} (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ m₀ m₁ b (n := n) (μ := μ) (TCom := TCom)
      (F := F) i).IsGuardedWith
      (fun stmt tr => roundCheck Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩))
      (fun stmt tr => roundOut Φ m₀ m₁ b stmt (tr.messages ⟨0, rfl⟩)
        (tr.challenges ⟨1, rfl⟩)) :=
  fun _ _ => rfl

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The round verifier is guarded — definitionally, by `roundCheck`. -/
theorem roundVerifier_isGuarded {TCom : Type} (i : ℕ) :
    (roundVerifier (oSpec := oSpec) Φ m₀ m₁ b (n := n) (μ := μ) (TCom := TCom)
      (F := F) i).IsGuarded :=
  ⟨_, _, roundVerifier_isGuardedWith Φ m₀ m₁ b i⟩

/-- The `i`-th round's honest prover skeleton: the round-polynomial pair is computed by the
parameter `computeG` (honestly `honestComputeG`, `Sumcheck/Completeness.lean`: the computable
partial hypercube sums of the two sumcheck polynomials in the free variable), and the witness is
carried through unchanged. -/
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

/-- The round's soundness parameter `k = max (2b) 2 + 1` is at least `2`. Named once so that
the extractor, the escape event and the soundness theorem below share the same structure (and
hence the same arity). -/
theorem round_two_le_k : 2 ≤ max (roundDegZero b) roundDegAlpha + 1 := by
  have := Nat.le_max_right (roundDegZero b) roundDegAlpha
  unfold roundDegAlpha at *; omega

/-- The per-round escape event: the tree's message pair and challenge family admit per-branch
responses for the round-`(i+1)` relation, two of which are distinct short openings of the
shared commitment `stmt.zc.t` — a `LiftCom.Collision`, and hence a Module-SIS break of the
commitment key. Responses are taken at the branch's guard-output statement (the `…OfValid`
form), since the round verifier replaces the targets rather than extending the statement. -/
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

/-- The per-round extraction algorithm reads the first branch's opening from the supplied valid
leaf witnessing at `roundOut`. On an accepting tree the `k` branch openings either disagree —
then `roundEsc` fires — or all agree, so that branch's opening satisfies the round-`i` claim;
the work is in `round_coordinateWiseSpecialSoundWithEscape`, not here. -/
def roundExtractor
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (i : ℕ) :
    Extractor.TreeBased (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ i) (LiftedWitness Φ μ n)
      (LiftedWitness Φ μ n) (pSpecScalar (RoundMsg F b) F)
      (CWSSStructure.toShape
        (scalarStructure (max (roundDegZero b) roundDegAlpha + 1) (round_two_le_k b))).arity :=
  ScalarRound.treeExtractorScalarOfValid (round_two_le_k b)
    (fun _ _ _ resp => resp ⟨0, Nat.succ_pos _⟩)

/-- Per-round coordinate-wise special soundness of the paired sumcheck round at
`k = max (2b) 2 + 1`, with computable extractor `roundExtractor` and escape event `roundEsc`.

The `k` accepting branches of a tree node share the message pair `(g^{(0)}, g^{(α)})` and
carry pairwise-distinct challenges. If two branch openings differ, both open the same
commitment `stmt.zc.t` and both are short, so the pair is a `LiftCom.Collision` and
`roundEsc` fires. Otherwise all branches share one opening `w̃`; for each summand the partial
cube sum in the free coordinate is a univariate of degree `≤ 2b` resp. `≤ 2`
(`roundPoly_degree_le_sumcheckPolyZero` / `…Alpha`) agreeing with the degree-matched `g` at
`k > deg` distinct points, hence equal to it as a polynomial. Evaluating at `0` and `1`,
splitting the cube (`hypercubeSum_succ`) and using the round check recovers the round-`i`
claims. The tree plumbing is the generic
`ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar_guarded`.

Both side conditions are necessary:

* `i < m₀` — the last step splits the round-`i` cube sum on a free coordinate. For `m₀ ≤ i`
  there is none: the sum has saturated (`hypercubeSum_of_le`) and the check only yields
  `2 · hypercubeSum = target` where the claim asks for `hypercubeSum = target`, so the
  statement fails over any `F` of characteristic `≠ 2`. The loop only instantiates rounds
  `0, …, m₀ − 1` (`roundsChainAux` threads the corresponding `count ≤ m₀`).
* `0 < b` — the `g^{(0)}` component is bounded by degree `roundDegZero b = 2b`, but at
  `b = 0` the range factor `P_0(v) = v` has degree `1`, overflowing the bound
  (`degreeOf_sumcheckPolyZero` carries the same hypothesis). Every instantiation has
  `b ≥ 2`. -/
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
  obtain ⟨M, rfl⟩ : ∃ M, m₀ = M + 1 := ⟨m₀ - 1, by omega⟩
  refine ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar_guarded
    init impl (round_two_le_k b) _
    (fun stmt g _ => roundCheck Φ (M + 1) m₁ b stmt g)
    (fun stmt g a => roundOut Φ (M + 1) m₁ b stmt g a)
    (roundVerifier_isGuardedWith Φ (M + 1) m₁ b i) _ _ _ _ ?_
  intro s g fam resp hcheck hresp hinj
  set z : Fin (max (roundDegZero b) roundDegAlpha + 1) := ⟨0, Nat.succ_pos _⟩ with hz
  by_cases hall : ∀ j, resp j = resp z
  case neg =>
    refine Or.inl ?_
    push Not at hall
    obtain ⟨j, hj⟩ := hall
    exact ⟨j, z, hj, ((hresp j).1).trans ((hresp z).1).symm, (hresp j).2.1, (hresp z).2.1⟩
  case pos =>
  have hguard := hcheck z
  simp only [roundCheck, Bool.and_eq_true, beq_iff_eq] at hguard
  refine Or.inr ⟨(hresp z).1, (hresp z).2.1, ?_, ?_, (hresp z).2.2.2.2⟩
  · have hdefect : roundPoly (sumcheckPolyZero Φ (M + 1) φF b s.zc.τ₀ (resp z))
        ⟨i, hi⟩ s.challenges = (g.1.1).toPoly := by
      refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj (fun j => ?_) ?_
      · rw [roundPoly_eval, ← CPolynomial.eval_toPoly]
        have h := (hresp j).2.2.1
        rw [hall j] at h
        exact h
      · have h₁ := Polynomial.natDegree_le_iff_degree_le.mpr
          (roundPoly_degree_le_sumcheckPolyZero Φ hb φF s.zc.τ₀ (resp z) ⟨i, hi⟩ s.challenges)
        have h₂ := Polynomial.natDegree_le_iff_degree_le.mpr
          (Polynomial.mem_degreeLE.mp (CPolynomial.degreeLE_toPoly.mp g.1.2))
        rw [Fintype.card_fin]
        omega
    have key : hypercubeSum (M + 1) (sumcheckPolyZero Φ (M + 1) φF b s.zc.τ₀ (resp z))
        ((⟨i, hi⟩ : Fin (M + 1)) : ℕ) s.challenges = s.target₀ := by
      rw [hypercubeSum_succ, ← roundPoly_eval, ← roundPoly_eval, hdefect,
        ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]
      exact hguard.1
    exact key
  · have hdefect : roundPoly
        (sumcheckPolyAlpha Φ (M + 1) m₁ φF b s.zc.rlin s.zc.α s.zc.τα (resp z))
        ⟨i, hi⟩ s.challenges = (g.2.1).toPoly := by
      refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj (fun j => ?_) ?_
      · rw [roundPoly_eval, ← CPolynomial.eval_toPoly]
        have h := (hresp j).2.2.2.1
        rw [hall j] at h
        exact h
      · have h₁ := Polynomial.natDegree_le_iff_degree_le.mpr
          (roundPoly_degree_le_sumcheckPolyAlpha Φ φF b s.zc.rlin s.zc.α m₁ s.zc.τα
            (resp z) ⟨i, hi⟩ s.challenges)
        have h₂ := Polynomial.natDegree_le_iff_degree_le.mpr
          (Polynomial.mem_degreeLE.mp (CPolynomial.degreeLE_toPoly.mp g.2.2))
        rw [Fintype.card_fin]
        omega
    have key : hypercubeSum (M + 1)
        (sumcheckPolyAlpha Φ (M + 1) m₁ φF b s.zc.rlin s.zc.α s.zc.τα (resp z))
        ((⟨i, hi⟩ : Fin (M + 1)) : ℕ) s.challenges = s.targetα := by
      rw [hypercubeSum_succ, ← roundPoly_eval, ← roundPoly_eval, hdefect,
        ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]
      exact hguard.2
    exact key

/-- The `i`-th paired sumcheck round as a guarded `EscapeGCWSSPackage`: the guarded round
verifier with the `k = max (2b) 2 + 1` special-soundness structure, reducing the round-`i`
relation to the round-`(i+1)` relation, with escape event `roundEsc`. The `i < m₀` and
`0 < b` hypotheses come from `round_coordinateWiseSpecialSoundWithEscape`. -/
def roundPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
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
  isGuarded := roundVerifierGuardedForm Φ m₀ m₁ b i
  extractor := roundExtractor Φ m₀ m₁ bound ρBound b K φF i
  isCWSS :=
    round_coordinateWiseSpecialSoundWithEscape Φ m₀ m₁ bound ρBound b init impl K φF hb i hi

/-- The empty round loop has no challenges. -/
instance : IsEmpty (roundsSpec F b 0).ChallengeIdx := ⟨fun i => Fin.elim0 i.1⟩

/-- The computable purity data of the round loop's base case (`Verifier.GuardedForm`'s pure
sibling): the zero-round identity package at the head of `roundsChainAux` is a `ReduceClaim`
head at `mapStmt := id`, so its verdict is the input statement itself and `verify_eq` is `rfl`.

The recursion's base package carries this rather than a `Verifier.IsPure` instance, for the reason
every link in the chain does: the composed extractor must *run* the left verdict at the seam, and
reading it off the `IsPure` existential would cost `Classical.choice`. -/
def roundsBaseVerifierPureForm {TCom : Type} :
    (ReduceClaim.verifier oSpec
      (id : NestedRoundStatement Φ TCom F n μ m₀ m₁ 0 →
        NestedRoundStatement Φ TCom F n μ m₀ m₁ 0)).PureForm where
  verify := fun stmt _ => stmt
  verify_eq := fun _ _ => rfl

/-- The composed sumcheck loop together with its relation invariant: `count` paired rounds
chained by recursion over the binary guarded append (base case: the zero-round identity
package), bundled with proofs that the composite's `relIn`/`relOut` are the round-`0` and
round-`count` relations. The invariant must ride along because the recursion's endpoints are
definitional only per instance, not for an open `count`. The composite's escape event is
whatever the recursion built — a nested disjunction of the per-round `roundEsc`s. -/
def roundsChainAux (init : ProbComp σ)
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
        isPure := roundsBaseVerifierPureForm Φ m₀ m₁
        extractor := ReduceClaim.treeExtractor (fun _ w => w) CWSSStructure.ofIsEmpty
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

/-- The composed sumcheck loop, from the round-`0` relation (installed by the sumcheck
bridge) to the round-`count` relation (consumed by the final-evaluation step). Instantiated
at `count := m₀` in the composition.

The recursion's own relation fields are stuck terms for an open `count`, so this wrapper
**re-pins them definitionally** to the round-`0`/round-`count` seam relations, transporting the
certificate along the recursion invariant once and for all. Downstream compositions can then
discharge both seams by `rfl`, i.e. compose with the universal `▷` instead of the explicit
`appendEscapeGuarded`/`appendGuarded` at a named seam lemma. -/
def roundsChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) (count : ℕ) (hcount : count ≤ m₀) :
    EscapeGCWSSPackage init impl
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ 0) (LiftedWitness Φ μ n)
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ count) (LiftedWitness Φ μ n)
      (roundsSpec F b count) :=
  let aux := roundsChainAux Φ m₀ m₁ bound ρBound b init impl K φF hb count hcount
  { aux.1 with
    relIn := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0
    relOut := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b count
    isCWSS := by have h := aux.1.isCWSS; rw [aux.2.1, aux.2.2] at h; exact h }

/-- The loop's input relation is the round-`0` relation (used when composing after the
sumcheck bridge) — definitional, by the re-pinning in `roundsChain`. -/
theorem roundsChain_relIn (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) (count : ℕ) (hcount : count ≤ m₀) :
    (roundsChain Φ m₀ m₁ bound ρBound b init impl K φF hb count hcount).relIn =
      nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0 :=
  rfl

/-- The loop's output relation is the round-`count` relation (used when composing with the
final-evaluation step) — definitional, by the re-pinning in `roundsChain`. -/
theorem roundsChain_relOut (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (hb : 0 < b) (count : ℕ) (hcount : count ≤ m₀) :
    (roundsChain Φ m₀ m₁ bound ρBound b init impl K φF hb count hcount).relOut =
      nestedRoundRel Φ m₀ m₁ bound ρBound K φF b count :=
  rfl

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
