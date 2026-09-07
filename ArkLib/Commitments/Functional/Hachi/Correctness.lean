/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.HonestChain
import ArkLib.Commitments.Functional.Hachi.EndPiece.Basic

/-!
# Nonrecursive Hachi: the terminal reveal-and-check and perfect correctness

One complete, **nonrecursive** Hachi opening run:

```
commitment input → relPolyEval → bridge → QuadEval → R^lin → lift → batching
  → zero-check → sumcheck → relWEvalClaim → reveal-and-check → acceptRejectRel
```

Instead of recursing on `relWEvalClaim`, the chain is closed by a non-succinct `SendWitness`-style
**terminal base case**: the prover sends the final `LiftedWitness` in the clear, and the verifier
decides the *entire* `relWEvalClaim` predicate on it — running `endPieceCheck`, the same decision
procedure the soundness-side `endPiece` (`EndPiece/Reduction.lean`) guards on, with the reflection
lemma `endPieceCheck_eq_true_iff`. This is a genuine terminal verifier — it can reject — so the
composition is a complete executable commitment opening, at the cost of a witness-sized final
message.

Composed completeness statements go through the generic `Reduction.append_completeness`, which this
repository admits; each link's own completeness is axiom-clean.

## Main definitions

* `pSpecTerminal`: the terminal wire format — `pSpecEndPiece` at the `LiftedWitness`, named for
  the scheme plumbing.
* `nonrecursiveTerminalReduction` / `…_perfectCompleteness`: the reveal-and-check reduction from
  `relWEvalClaim` to `acceptRejectRel`. Its verifier returns `endPieceCheck` as its Boolean
  verdict — the `Commitment.Scheme` interface fixes the `Proof` shape to a `Bool` output — where
  `EndPiece/`'s guarded `endPieceVerifier` *guards* on that same check;
  `terminalVerifier_verify_eq_endPieceCheck` keeps the two directions of the closing link on one
  decision procedure.
* `relCommitInput` / `commitInputReduction` / `…_perfectCompleteness`: the zero-round head that
  converts the commitment API's claim (an honest commitment plus a truthful evaluation claim) into
  `relPolyEvalMsgShort`, with the relation step
  `mem_relPolyEvalMsgShort_of_relCommitInput` (and `mem_relPolyEval_of_relCommitInput` as its
  forgetful corollary). The `MsgShort` conjunct is the `ℓ∞` bound `⌊b/2⌋` on the balanced
  committer's message decomposition — the only extra invariant the honest-`z` shortness bound
  needs, and hence the reason the folded-witness digit count `τ` can be chosen from
  `2ʳ·ω·⌊b/2⌋` instead of from `q`.
* `nonrecursiveOpeningReduction`, `hachiNonrecursiveOpening` and their completeness: the honest
  chain through the sumcheck (`completeThroughSumcheckReduction`) closed by the terminal base
  case, with the input adapter in front — the complete opening protocol, from `relCommitInput` to
  `acceptRejectRel`.
* `hachiNonrecursive`: Hachi as a `Commitment.Scheme` with that opening and the honest committer
  `commit`. Its `τ` (folded-witness digit count) and `zBound` are **independent parameters**: the
  message and inner digit counts stay `δ = ⌈log_b q⌉`, while `τ` is constrained only by
  `hcap : zBound ≤ balancedDigitCapacity P.b τ` and `hzb : 2ʳ·ω·⌊b/2⌋ ≤ zBound`. At the `ℓ = 30`
  parameters, where `τ = 5` (`Params.lean`), that is `τ = 5 < δ = 8`, and
  `q ≤ 16⁵` is nowhere assumed — it is false.
* `hachiNonrecursive_perfectCorrectness`: `Commitment.perfectCorrectness` for it, through the
  generic bridge `Commitment.perfectCorrectness_of_opening_perfectCompleteness`
  (`Commitments/Functional/Basic.lean`). `Concrete.lean` instantiates all of this at the Ajtai
  lift commitment.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open RingSwitching RingSwitching.Lift
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

/-! ## The terminal reveal-and-check protocol -/

section Terminal

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ : ℕ) (bound bDig b : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The terminal wire format: a single `P_to_V` message revealing the final `LiftedWitness`
in the clear — the end-piece wire format (`pSpecEndPiece`), named at the `LiftedWitness` for the
scheme plumbing. Non-succinct by design — this is the nonrecursive base case. -/
@[reducible] def pSpecTerminal (Φ : CyclotomicModulus (ZMod q)) (μ n : ℕ) : ProtocolSpec 1 :=
  pSpecEndPiece (LiftedWitness Φ μ n)

/-- Challenges of the terminal step are (vacuously) `VCVCompatible` — there are none. -/
instance : ∀ i, VCVCompatible ((pSpecTerminal Φ μ n).Challenge i) :=
  fun i => isEmptyElim i

variable (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig)) (φF : ZMod q →+* F)

/-- The terminal honest prover: sends its `LiftedWitness` in the clear, and outputs the very
verdict the verifier will reach on it (so prover and verifier agree on the output statement). -/
def terminalProver [BEq K.TCom] :
    Prover oSpec (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n) Bool Unit
      (pSpecTerminal Φ μ n) where
  PrvState
    | 0 => WEvalStatement K.TCom F m₀ × LiftedWitness Φ μ n
    | 1 => WEvalStatement K.TCom F m₀ × LiftedWitness Φ μ n
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (st.2, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun st => pure (endPieceCheck Φ m₀ bound bDig b K φF st.1 st.2, ())

/-- The terminal verifier: decides the full `relWEvalClaim` predicate on the revealed witness
and returns the verdict — `endPieceCheck`, the very check the guarded soundness verifier
`endPieceVerifier` guards on (`terminalVerifier_verify_eq_endPieceCheck`). A genuine terminal
verifier — `false` on any failed conjunct. -/
def terminalVerifier [BEq K.TCom] :
    Verifier oSpec (WEvalStatement K.TCom F m₀) Bool (pSpecTerminal Φ μ n) where
  verify := fun stmt tr => pure (endPieceCheck Φ m₀ bound bDig b K φF stmt (tr 0))

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- **One decision procedure for the closing link**: the terminal verifier's Boolean verdict is
`endPieceCheck` — literally the guard of the soundness-side `endPieceVerifier`
(`endPieceVerifierGuardedForm`). The completeness direction (this file) and the CWSS certificate
(`EndPiece/Reduction.lean`) therefore cannot drift onto different checks. Holds by `rfl`. -/
@[simp] theorem terminalVerifier_verify_eq_endPieceCheck [BEq K.TCom]
    (stmt : WEvalStatement K.TCom F m₀) (tr : (pSpecTerminal Φ μ n).FullTranscript) :
    (terminalVerifier (oSpec := oSpec) Φ m₀ bound bDig b K φF).verify stmt tr
      = pure ((endPieceVerifierGuardedForm (oSpec := oSpec)
          Φ m₀ bound bDig b K φF).check stmt tr) :=
  rfl

/-- **The nonrecursive terminal reduction** (reveal-and-check): the prover reveals the final
`LiftedWitness`, the verifier decides `relWEvalClaim` on it. This closes the Hachi chain without
recursion. -/
def nonrecursiveTerminalReduction [BEq K.TCom] :
    Reduction oSpec (WEvalStatement K.TCom F m₀) (LiftedWitness Φ μ n) Bool Unit
      (pSpecTerminal Φ μ n) where
  prover := terminalProver Φ m₀ bound bDig b K φF
  verifier := terminalVerifier Φ m₀ bound bDig b K φF

omit [NeZero q] [IsCyclotomic Φ] [LawfulBEq F] in
/-- The terminal reduction's honest run, in closed form: one pure message round and a pure
verifier collapse to a single successful outcome carrying the verdict on both sides. -/
theorem nonrecursiveTerminalReduction_run [BEq K.TCom]
    (stmt : WEvalStatement K.TCom F m₀) (wit : LiftedWitness Φ μ n) :
    (nonrecursiveTerminalReduction (oSpec := oSpec) Φ m₀ bound bDig b K φF).run stmt wit =
      pure ((show (pSpecTerminal Φ μ n).FullTranscript from
          ProtocolSpec.Transcript.concat (m := 0) wit
            (default : (pSpecTerminal Φ μ n).Transcript 0),
        endPieceCheck Φ m₀ bound bDig b K φF stmt wit, ()),
        endPieceCheck Φ m₀ bound bDig b K φF stmt wit) := rfl

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Perfect completeness of the terminal reveal-and-check**, from `relWEvalClaim` to
`acceptRejectRel`, error `0`: on a witness satisfying the relation the check passes by the
reflection lemma, and prover and verifier output the same verdict by construction. -/
theorem nonrecursiveTerminalReduction_perfectCompleteness [BEq K.TCom] [LawfulBEq K.TCom]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (nonrecursiveTerminalReduction (oSpec := oSpec) Φ m₀ bound bDig b
        K φF).perfectCompleteness init impl
      (relWEvalClaim Φ m₀ bound bDig b K φF) acceptRejectRel := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt wit hIn x hx
  rw [nonrecursiveTerminalReduction_run, OptionT.run_pure, support_pure,
    Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨_, rfl, ?_, rfl⟩
  simp only [acceptRejectRel, Set.mem_singleton_iff, Prod.mk.injEq, and_true]
  exact (endPieceCheck_eq_true_iff Φ m₀ bound bDig b K φF stmt wit).mpr hIn

end Terminal

/-! ## The complete nonrecursive opening reduction

`completeThroughSumcheckReduction` carries `relPolyEval` to the evaluation claim
`relWEvalClaim`; the terminal reveal-and-check closes it to `acceptRejectRel`. The append below
is therefore a complete protocol from the polynomial-evaluation relation to a Boolean verdict —
the `Proof` shape the commitment interface consumes, up to the zero-round input adapter. -/

section NonrecursiveOpening

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits zBound m r M m₁ : Nat}
  {ω : ℕ}
variable {F : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] [SampleableType F]

local notation "μ₀" => rlinCols innerRows messageDigits innerDigits zDigits m r
local notation "n₀" => rlinRows innerRows outerRows dRows

/-- The wire format of the honest chain through the sumcheck — the protocol spec of
`completeThroughSumcheckReduction`, named. -/
@[reducible] def throughSumcheckSpec (TCom : Type) (bZero : ℕ) :=
  (((!p[] : ProtocolSpec 0) ++ₚ
    (CoordinateWise.SingleRound.pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r ++ₚ
      ((!p[] : ProtocolSpec 0) ++ₚ
        (pSpecScalar TCom F ++ₚ
          ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F (M + 1) m₁))))) ++ₚ
    sumcheckSpec F bZero (M + 1))

/-- The wire format of the nonrecursive opening: the chain through the sumcheck, then the
terminal reveal. -/
@[reducible] def nonrecursiveOpeningSpec (TCom : Type) (bZero : ℕ) :=
  throughSumcheckSpec (F := F) (dRows := dRows) (M := M) (m₁ := m₁) (ω := ω) (r := r)
    Φ TCom bZero ++ₚ pSpecTerminal Φ μ₀ n₀

/-- Sampleability of the nonrecursive opening's wire format: the chain's own instance appended
to the terminal step's (which has no challenges), assembled explicitly for the same reason
`throughSumcheckSpecSampleable` is — the generic append instance does not fire reliably through
a deeply nested `ProtocolSpec`. -/
@[reducible] instance nonrecursiveOpeningSpecSampleable {TCom : Type} (bZero : ℕ)
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)] :
    ∀ i, SampleableType
      ((nonrecursiveOpeningSpec (F := F) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (zDigits := zDigits)
        (m := m) (r := r) (M := M) (m₁ := m₁) (ω := ω) Φ TCom bZero).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (h₁ := throughSumcheckSpecSampleable Φ bZero) (h₂ := inferInstance)

/-- Sampleability of the full scheme-level wire format (a zero-round adapter in front of the
nonrecursive opening), assembled explicitly like the instances above. -/
@[reducible] instance schemeSpecSampleable {TCom : Type} (bZero : ℕ)
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)] :
    ∀ i, SampleableType
      (((!p[] : ProtocolSpec 0) ++ₚ
        nonrecursiveOpeningSpec (F := F) (innerRows := innerRows)
          (messageDigits := messageDigits) (outerRows := outerRows)
          (innerDigits := innerDigits) (dRows := dRows) (zDigits := zDigits)
          (m := m) (r := r) (M := M) (m₁ := m₁) (ω := ω) Φ TCom bZero).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
    (h₂ := nonrecursiveOpeningSpecSampleable Φ bZero)

/-- **The nonrecursive opening reduction**: the honest Hachi chain through the sumcheck
(`completeThroughSumcheckReduction`) closed by the terminal reveal-and-check. From the
polynomial-evaluation relation to a Boolean verdict; no recursion adapter is involved. -/
def nonrecursiveOpeningReduction (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero)) [DecidableEq K.TCom]
    (hd : 0 < Φ.φ.natDegree) (hbZero : 0 < P.bZero) (φF : ZMod q →+* F) :
    Reduction oSpec
      (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      Bool Unit
      (nonrecursiveOpeningSpec (F := F) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (zDigits := zDigits)
        (m := m) (r := r) (M := M) (m₁ := m₁) (ω := ω) Φ K.TCom P.bZero) :=
  (completeThroughSumcheckReduction (oSpec := oSpec) (F := F) (ω := ω) (M := M) (m₁ := m₁)
      Φ P pp hqm hcap K hd hbZero φF).append
    (nonrecursiveTerminalReduction (oSpec := oSpec) Φ (M + 1) P.γ P.bZero P.bZero K φF)

omit [DecidableEq F] in
/-- **Perfect completeness of the nonrecursive opening**, from `relPolyEval` to
`acceptRejectRel`, error `0`. The hypotheses are exactly those of
`completeThroughSumcheckReduction_perfectCompleteness`; the terminal link needs nothing.

Depends on the admitted `Reduction.append_completeness` through the append; the terminal link
itself is axiom-clean. -/
theorem nonrecursiveOpeningReduction_perfectCompleteness
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)]
    (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (hmul : Rq.HasMulLInftyBound Φ) (hzb : 2 ^ r * ω * (P.b / 2) ≤ zBound)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hd : 0 < Φ.φ.natDegree)
    (hbZero : 0 < P.bZero)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero)) [DecidableEq K.TCom]
    (φF : ZMod q →+* F) (hμn : (μ₀ + n₀ * rhoDigitCount q P.bZero) * Φ.φ.natDegree ≤ 2 ^ (M + 1))
    (hZeroγ : P.bZero - 1 ≤ P.γ)
    {βSq κ : ℕ} :
    (nonrecursiveOpeningReduction (oSpec := oSpec) (F := F) (ω := ω) (M := M) (m₁ := m₁)
      Φ P pp hqm hcap K hd hbZero φF).perfectCompleteness init impl
      (relPolyEvalMsgShort Φ pp (P.b : ZMod q) βSq P.γ κ (P.b / 2))
      acceptRejectRel :=
  Reduction.append_perfectCompleteness _ _
    (completeThroughSumcheckReduction_perfectCompleteness (zDigits := zDigits) (ω := ω)
      (M := M) (m₁ := m₁) (βSq := βSq) (κ := κ)
      Φ P init impl pp hqm hcap hmul hzb hmd hτ hd hbZero K φF hμn hZeroγ)
    (nonrecursiveTerminalReduction_perfectCompleteness Φ (M + 1) P.γ P.bZero P.bZero K φF
      init impl)

end NonrecursiveOpening

/-! ## The commitment-input adapter

The commitment API opens on the statement `Commitment × (x : Query) × Response` with witness
`Data × Decommitment`; the Hachi chain starts at `PolyEvalStatement × QuadEvalWitness` and
`relPolyEval`. The zero-round `ReduceClaim` head below converts: the evaluation query splits
into the low/high point halves, the claimed response becomes the claimed evaluation, the
commitment passes through, and the decommitment (the honest balanced decompositions) becomes the
honest weak opening at the trivial challenge. The honest direction
(`mem_relPolyEval_of_relCommitInput`) is all correctness needs
(`ReduceClaim.reduction_completeness_of_imp`); no reverse implication is required. -/

section InputAdapter

/-- Upstreamable `Vector` helper: `take`/`drop` at the split point recover the vector. -/
private theorem Vector.cast_take_append_cast_drop {γ : Type*} {r m : ℕ}
    (v : Vector γ (r + m)) :
    (v.take r).cast (by omega) ++ (v.drop r).cast (by omega) = v := by
  ext i hi
  simp only [Vector.getElem_append, Vector.getElem_cast, Vector.getElem_take,
    Vector.getElem_drop]
  split
  · rfl
  · congr 1; omega

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows outerRows dRows m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable (b : ℕ)

/-- The commitment API's input statement: the commitment, the evaluation query, and the claimed
response — `Commitment × (q : O.Query) × O.Response q` at the multilinear evaluation oracle. -/
@[reducible] def CommitInputStatement (q : ℕ) [Fact (Nat.Prime q)] [BEq (ZMod q)]
    [LawfulBEq (ZMod q)] (α outerRows m r : ℕ) : Type :=
  Commitment 𝓜(q, α) outerRows ×
    (_x : Vector (Rq 𝓜(q, α)) (r + m)) × Rq 𝓜(q, α)

/-- The commitment API's input witness: the committed polynomial and the decommitment. -/
@[reducible] def CommitInputWitness (b q : ℕ) [Fact (Nat.Prime q)] [BEq (ZMod q)]
    [LawfulBEq (ZMod q)] (α innerRows m r : ℕ) : Type :=
  CMlPolynomial (Rq 𝓜(q, α)) (r + m) ×
    Decomp 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) (2 ^ r) (Nat.clog b q)

/-- Statement map of the adapter: the query splits into the low (first `r`) and high (last `m`)
point halves, the claimed response is the claimed evaluation, the commitment passes through. -/
def commitInputStmtMap (s : CommitInputStatement q α outerRows m r) :
    PolyEvalStatement 𝓜(q, α) innerRows (Nat.clog b q) outerRows (Nat.clog b q) dRows m r where
  u := s.1
  xl := (s.2.1.take r).cast (by omega)
  xh := (s.2.1.drop r).cast (by omega)
  y := s.2.2

/-- Witness map of the adapter: the decommitment's decompositions with the trivial challenge
`cᵢ = 1` — the honest weak opening shape of `honestOpening`. -/
def commitInputWitMap (w : CommitInputWitness b q α innerRows m r) :
    QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) (2 ^ r) (Nat.clog b q) where
  toDecomp := w.2
  challenge := fun _ => 1

/-- **The honest commitment-input relation**: the commitment and decommitment are the honest
committer's output on the data, and the claimed response is the data's actual evaluation at the
query — the commitment API's opening relation, specialized to the deterministic `commit`. -/
def relCommitInput (hb : 1 < b)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows) :
    Set (CommitInputStatement q α outerRows m r × CommitInputWitness b q α innerRows m r) :=
  {p | (p.1.1, p.2.2) = commit b hb pp p.2.1 ∧
    CMlPolynomial.eval p.2.1 p.1.2.1 = p.1.2.2}

/-- **The honest commitment input satisfies `relPolyEvalMsgShort`** — the forward relation lemma
of the input adapter, and the only direction correctness needs.

Three conjuncts. The `VerifiedOpening` one is `verifiedOpening_honestOpening` with the two norm
side conditions discharged for the balanced digits (short at radius `⌊b/2⌋`, relaxed into the
target parameters by `hβSq`/`hγ`). The **message
`ℓ∞` bound** `⌊b/2⌋` is the same balanced-digit fact read through
`gadgetDecompose_vecLInftyNorm_le_of_digit_le`; it is what the honest-`z` shortness bound
downstream consumes, and hence what lets the folded-witness digit count `τ` be sized from
`2ʳ·ω·⌊b/2⌋` rather than from `q`. The evaluation conjunct is the reconstruction chain: the
derived message matrix of the honest opening *is* the
committed coefficient matrix (`generateDecomps_derivedMessage`), whose polynomial is the data
(`toPolynomial_toMatrix`), evaluated at the recombined query point
(`Vector.cast_take_append_cast_drop`). -/
theorem mem_relPolyEvalMsgShort_of_relCommitInput {βSq γ κ : ℕ} (hb : 1 < b)
    (hbq : b ≤ q / 2) (hdeg : 1 ≤ 𝓜(q, α).φ.natDegree) (hclog : 0 < Nat.clog b q) (hκ : 1 ≤ κ)
    (hβSq : (2 ^ m) * Nat.clog b q * (𝓜(q, α).φ.natDegree * (b / 2) ^ 2) ≤ βSq)
    (hγ : b / 2 ≤ γ)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows)
    (s : CommitInputStatement q α outerRows m r) (w : CommitInputWitness b q α innerRows m r)
    (h : (s, w) ∈ relCommitInput b hb pp) :
    (commitInputStmtMap (innerRows := innerRows) (dRows := dRows) b s,
      commitInputWitMap b w)
      ∈ relPolyEvalMsgShort 𝓜(q, α) pp (b : ZMod q) βSq γ κ (b / 2) := by
  obtain ⟨hcm, heval⟩ := h
  set dd := balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q) with hdd
  -- The two components of the honest committer's output.
  have hu : s.1 = commitWithDecomps 𝓜(q, α) pp.toPublicParams
      (generateDecomps 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α) dd dd)
        pp.toPublicParams (Hachi.toMatrix w.1)) :=
    (congrArg Prod.fst hcm).trans (commit_fst b hb pp w.1)
  have hdc : w.2 = generateDecomps 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α) dd dd)
      pp.toPublicParams (Hachi.toMatrix w.1) :=
    (congrArg Prod.snd hcm).trans (commit_snd b hb pp w.1)
  -- The adapter's witness is the honest opening.
  have hwit : commitInputWitMap b w = honestOpening 𝓜(q, α)
      (Decomposition.ofDigits 𝓜(q, α) dd dd) pp.toPublicParams (Hachi.toMatrix w.1) := by
    unfold commitInputWitMap honestOpening
    rw [hdc]
  rw [hwit]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- `VerifiedOpening`, with the balanced-digit norm bounds relaxed into the parameters.
    have hβ : ∀ i, ‖(generateDecomps 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α) dd dd)
        pp.toPublicParams (Hachi.toMatrix w.1)).message i‖₂² ≤ βSq := by
      intro i
      refine le_trans ?_ hβSq
      change ‖gadgetDecompose 𝓜(q, α) dd _‖₂² ≤ _
      exact gadgetDecompose_vecL2NormSq_le_of_digit_le 𝓜(q, α) dd
        (fun c e => balancedZmodDigit_natAbs_le hb (Nat.le_pow_clog hb q) hbq c e) _
    have hγ' : vecLInftyNorm 𝓜(q, α) (PolyVec.flattenBlocks (generateDecomps 𝓜(q, α)
        (Decomposition.ofDigits 𝓜(q, α) dd dd) pp.toPublicParams
        (Hachi.toMatrix w.1)).innerDecomp) ≤ γ := by
      refine le_trans (vecLInftyNorm_flattenBlocks_le 𝓜(q, α) _ fun i => ?_) hγ
      change vecLInftyNorm 𝓜(q, α) (gadgetDecompose 𝓜(q, α) dd _) ≤ b / 2
      exact gadgetDecompose_vecLInftyNorm_le_of_digit_le 𝓜(q, α) dd
        (fun c e => balancedZmodDigit_natAbs_le hb (Nat.le_pow_clog hb q) hbq c e) _
    have hκle : ‖(1 : Rq 𝓜(q, α))‖₁ ≤ κ := by
      rw [Rq.l1Norm_one 𝓜(q, α) hdeg]; exact hκ
    change VerifiedOpening 𝓜(q, α) (b : ZMod q) βSq γ κ pp.toPublicParams
      (commitInputStmtMap (innerRows := innerRows) (dRows := dRows) b s).u _
    rw [show (commitInputStmtMap (innerRows := innerRows) (dRows := dRows) b s).u = s.1
      from rfl, hu]
    exact verifiedOpening_honestOpening 𝓜(q, α) (b : ZMod q) βSq γ κ
      (Decomposition.ofDigits 𝓜(q, α) dd dd)
      (gadgetDecompose_lawful 𝓜(q, α) hclog hdeg dd) hκle pp.toPublicParams
      (Hachi.toMatrix w.1) hβ hγ'
  · -- Evaluation consistency: reconstruction, then the query split round-trip.
    have hM : derivedMsgMatrix 𝓜(q, α) (b : ZMod q)
        (honestOpening 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α) dd dd)
          pp.toPublicParams (Hachi.toMatrix w.1)) = Hachi.toMatrix w.1 := by
      funext i k
      exact congrFun (generateDecomps_derivedMessage 𝓜(q, α) (b : ZMod q)
        (Decomposition.ofDigits 𝓜(q, α) dd dd)
        (gadgetDecompose_lawful 𝓜(q, α) hclog hdeg dd) pp.toPublicParams
        (Hachi.toMatrix w.1) i) k
    change CMlPolynomial.eval (extractedPoly 𝓜(q, α) (b : ZMod q) _) _ = _
    rw [extractedPoly, hM, Hachi.toPolynomial_toMatrix]
    change CMlPolynomial.eval w.1
      ((s.2.1.take r).cast (by omega) ++ (s.2.1.drop r).cast (by omega)) = s.2.2
    rw [Vector.cast_take_append_cast_drop]
    exact heval
  · -- The honest message decomposition is `ℓ∞`-short at the balanced radius `⌊b/2⌋`: the input
    -- to the honest-`z` bound (`vecLInftyNorm_honestZ_le`), and the reason `τ` may sit below `δ`.
    intro i
    change vecLInftyNorm 𝓜(q, α) (gadgetDecompose 𝓜(q, α) dd _) ≤ b / 2
    exact gadgetDecompose_vecLInftyNorm_le_of_digit_le 𝓜(q, α) dd
      (fun c e => balancedZmodDigit_natAbs_le hb (Nat.le_pow_clog hb q) hbq c e) _

/-- **The honest commitment input satisfies `relPolyEval`** — the old, weaker form of
`mem_relPolyEvalMsgShort_of_relCommitInput`, through the forgetful inclusion
`relPolyEvalMsgShort ⊆ relPolyEval`. Kept because it is the statement any consumer of the
unstrengthened relation wants. -/
theorem mem_relPolyEval_of_relCommitInput {βSq γ κ : ℕ} (hb : 1 < b)
    (hbq : b ≤ q / 2) (hdeg : 1 ≤ 𝓜(q, α).φ.natDegree) (hclog : 0 < Nat.clog b q) (hκ : 1 ≤ κ)
    (hβSq : (2 ^ m) * Nat.clog b q * (𝓜(q, α).φ.natDegree * (b / 2) ^ 2) ≤ βSq)
    (hγ : b / 2 ≤ γ)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows)
    (s : CommitInputStatement q α outerRows m r) (w : CommitInputWitness b q α innerRows m r)
    (h : (s, w) ∈ relCommitInput b hb pp) :
    (commitInputStmtMap (innerRows := innerRows) (dRows := dRows) b s,
      commitInputWitMap b w) ∈ relPolyEval 𝓜(q, α) pp (b : ZMod q) βSq γ κ :=
  relPolyEvalMsgShort_subset_relPolyEval 𝓜(q, α) pp (b : ZMod q) βSq γ κ (b / 2)
    (mem_relPolyEvalMsgShort_of_relCommitInput b hb hbq hdeg hclog hκ hβSq hγ pp s w h)

/-- **The commitment-input adapter**: the zero-round `ReduceClaim` head converting the
commitment API's opening claim into the Hachi chain's polynomial-evaluation claim. -/
def commitInputReduction :
    Reduction oSpec
      (CommitInputStatement q α outerRows m r) (CommitInputWitness b q α innerRows m r)
      (PolyEvalStatement 𝓜(q, α) innerRows (Nat.clog b q) outerRows (Nat.clog b q) dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) (2 ^ r) (Nat.clog b q))
      !p[] :=
  ReduceClaim.reduction oSpec (commitInputStmtMap (innerRows := innerRows) (dRows := dRows) b)
    (fun _ w => commitInputWitMap b w)


/-- **Perfect completeness of the commitment-input adapter**, from `relCommitInput` to
`relPolyEval`, error `0` — `ReduceClaim.reduction_completeness_of_imp` at the forward honest
relation lemma. Axiom-clean. -/
theorem commitInputReduction_perfectCompleteness {βSq γ κ : ℕ} (hb : 1 < b)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hbq : b ≤ q / 2) (hdeg : 1 ≤ 𝓜(q, α).φ.natDegree) (hclog : 0 < Nat.clog b q) (hκ : 1 ≤ κ)
    (hβSq : (2 ^ m) * Nat.clog b q * (𝓜(q, α).φ.natDegree * (b / 2) ^ 2) ≤ βSq)
    (hγ : b / 2 ≤ γ)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows) :
    (commitInputReduction (oSpec := oSpec) (innerRows := innerRows) (dRows := dRows)
        b).perfectCompleteness init impl
      (relCommitInput b hb pp)
      (relPolyEvalMsgShort 𝓜(q, α) pp (b : ZMod q) βSq γ κ (b / 2)) :=
  ReduceClaim.reduction_completeness_of_imp _ _
    (fun stmt wit h =>
      mem_relPolyEvalMsgShort_of_relCommitInput b hb hbq hdeg hclog hκ hβSq hγ pp stmt wit h)

end InputAdapter

/-! ## The nonrecursive Hachi scheme

`hachiNonrecursive` packages the honest committer `commit` with the complete opening protocol —
input adapter ▷ chain through the sumcheck ▷ terminal reveal-and-check — as a `Commitment.Scheme`.
The honest chain's input relation is established for that committer by
`mem_relPolyEval_of_relCommitInput`. -/

section Scheme

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows outerRows dRows m r M m₁ : Nat} {ω : ℕ}
variable {F : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] [SampleableType F]
variable {σ : Type}

/-! ### `τ` is an independent protocol parameter

The message and inner gadget steps decompose arbitrary residues, so their digit counts are pinned
to `δ = ⌈log_b q⌉` (`Nat.clog`) — that is correct and necessary. The **folded-witness** step is
different: `z = Σᵢ cᵢ sᵢ` is deterministically short, so its digit count is a free parameter `τ`,
sized from the honest bound `2ʳ·ω·⌊b/2⌋` rather than from `q`. `τ` and `zBound` are therefore
section variables here, and they flow into `μ₀`, the lift/sumcheck table widths, and the
soundness-side `quadEvalBetaSq` alike. Setting `τ := δ` recovers the old full-width behaviour as an
instance (the capacity hypothesis is then slack), so no separate compatibility path is needed at
this layer. -/

variable {τ zBound : Nat}

local notation "δ" P => Nat.clog (HonestRangeParams.b P) q
local notation "μ₀" P =>
  rlinCols innerRows (Nat.clog (HonestRangeParams.b P) q) (Nat.clog (HonestRangeParams.b P) q)
    τ m r
local notation "n₀" => rlinRows innerRows outerRows dRows

/-- **The complete nonrecursive opening**: input adapter ▷ chain through the sumcheck ▷ terminal
reveal-and-check, from the commitment API's claim to a Boolean verdict, over the composed
protocol specification. -/
def hachiNonrecursiveOpening (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (δ P) outerRows (2 ^ r) (δ P) dRows)
    (hcap : zBound ≤ balancedDigitCapacity P.b τ)
    (K : LiftCom (LiftedWitness 𝓜(q, α) (μ₀ P) n₀) (liftShort 𝓜(q, α) P.γ P.bZero))
    [DecidableEq K.TCom]
    (hd : 0 < 𝓜(q, α).φ.natDegree) (hbZero : 0 < P.bZero) (φF : ZMod q →+* F) :
    Reduction unifSpec
      (CommitInputStatement q α outerRows m r) (CommitInputWitness P.b q α innerRows m r)
      Bool Unit
      ((!p[] : ProtocolSpec 0) ++ₚ
        nonrecursiveOpeningSpec (F := F) (innerRows := innerRows)
          (messageDigits := δ P) (outerRows := outerRows) (innerDigits := δ P)
          (dRows := dRows) (zDigits := τ) (m := m) (r := r) (M := M) (m₁ := m₁) (ω := ω)
          𝓜(q, α) K.TCom P.bZero) :=
  (commitInputReduction (oSpec := unifSpec) (innerRows := innerRows) (dRows := dRows)
      P.b).append
    (nonrecursiveOpeningReduction (oSpec := unifSpec) (F := F) (ω := ω) (M := M) (m₁ := m₁)
      𝓜(q, α) P pp (Nat.le_pow_clog P.hb q) hcap K hd hbZero φF)

omit [DecidableEq F] in
/-- **Perfect completeness of the complete nonrecursive opening**, from `relCommitInput` (the
honest balanced commitment plus a truthful evaluation claim) to `acceptRejectRel`, error `0`.

Depends on the admitted `Reduction.append_completeness` through the appends; the adapter and
terminal links are axiom-clean. -/
theorem hachiNonrecursiveOpening_perfectCompleteness
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r).Challenge i)]
    (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl unifSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (δ P) outerRows (2 ^ r) (δ P) dRows)
    (hcap : zBound ≤ balancedDigitCapacity P.b τ)
    (hzb : 2 ^ r * ω * (P.b / 2) ≤ zBound) (hτ : 0 < τ)
    (hclog : 0 < Nat.clog P.b q) (hd : 0 < 𝓜(q, α).φ.natDegree)
    (hbZero : 0 < P.bZero)
    (K : LiftCom (LiftedWitness 𝓜(q, α) (μ₀ P) n₀) (liftShort 𝓜(q, α) P.γ P.bZero))
    [DecidableEq K.TCom]
    (φF : ZMod q →+* F)
    (hμn : ((μ₀ P) + n₀ * rhoDigitCount q P.bZero) * 𝓜(q, α).φ.natDegree ≤ 2 ^ (M + 1))
    (hZeroγ : P.bZero - 1 ≤ P.γ)
    {βSq κ : ℕ} (hκ : 1 ≤ κ)
    (hβSq : (2 ^ m) * Nat.clog P.b q * (𝓜(q, α).φ.natDegree * (P.b / 2) ^ 2) ≤ βSq) :
    (hachiNonrecursiveOpening (F := F) (ω := ω) (M := M) (m₁ := m₁)
      P pp hcap K hd hbZero φF).perfectCompleteness init impl
      (relCommitInput P.b P.hb pp) acceptRejectRel :=
  Reduction.append_perfectCompleteness _ _
    (commitInputReduction_perfectCompleteness (βSq := βSq) (γ := P.γ) (κ := κ)
      P.b P.hb init impl P.hbq hd hclog hκ hβSq P.hbγ pp)
    (nonrecursiveOpeningReduction_perfectCompleteness (zDigits := τ) (ω := ω)
      (M := M) (m₁ := m₁) (βSq := βSq) (κ := κ)
      𝓜(q, α) P init impl pp (Nat.le_pow_clog P.hb q) hcap
      (powTwoCyclotomic_hasMulLInftyBound α) hzb
      hclog hτ hd hbZero K φF hμn hZeroγ)

/-- **Hachi, nonrecursive, as a functional commitment** (`Commitment.Scheme`): the multilinear
evaluation oracle, honest key generation, the honest committer `commit`, and the
full composed opening `hachiNonrecursiveOpening` — input adapter, bridge, `QuadEval`, `R^lin`
adapter, lift, batching, nested zero-check, sumcheck, and the terminal reveal-and-check. Perfect
correctness is `hachiNonrecursive_perfectCorrectness`.

The opening keys both prover and verifier by the committer key `keys.1`; honest key generation
returns identical keys, so nothing is lost for correctness. A soundness treatment would want the
verifier keyed by `keys.2` separately, which needs split-key plumbing in the opening. -/
def hachiNonrecursive (P : HonestRangeParams q)
    [SampleableType (Simple.PublicParams 𝓜(q, α) innerRows ((2 ^ m) * Nat.clog P.b q))]
    [SampleableType
      (Simple.PublicParams 𝓜(q, α) outerRows ((2 ^ r) * (innerRows * Nat.clog P.b q)))]
    [SampleableType (Simple.PublicParams 𝓜(q, α) dRows ((2 ^ r) * Nat.clog P.b q))]
    (hcap : zBound ≤ balancedDigitCapacity P.b τ)
    (K : LiftCom (LiftedWitness 𝓜(q, α) (μ₀ P) n₀) (liftShort 𝓜(q, α) P.γ P.bZero))
    [DecidableEq K.TCom]
    (hd : 0 < 𝓜(q, α).φ.natDegree) (hbZero : 0 < P.bZero) (φF : ZMod q →+* F) :
    Commitment.Scheme unifSpec
      (CMlPolynomial (Rq 𝓜(q, α)) (r + m))
      (Commitment 𝓜(q, α) outerRows)
      (Decomp 𝓜(q, α) innerRows (2 ^ m) (δ P) (2 ^ r) (δ P))
      (Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (δ P) outerRows (2 ^ r) (δ P) dRows)
      (Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (δ P) outerRows (2 ^ r) (δ P) dRows)
      ((!p[] : ProtocolSpec 0) ++ₚ
        nonrecursiveOpeningSpec (F := F) (innerRows := innerRows)
          (messageDigits := δ P) (outerRows := outerRows) (innerDigits := δ P)
          (dRows := dRows) (zDigits := τ) (m := m) (r := r) (M := M) (m₁ := m₁) (ω := ω)
          𝓜(q, α) K.TCom P.bZero) where
  keygen := keygen P.b
  commit := fun pp p => pure (commit P.b P.hb pp p)
  opening := fun keys =>
    hachiNonrecursiveOpening (F := F) (ω := ω) (M := M) (m₁ := m₁) P keys.1 hcap K hd hbZero φF

omit [DecidableEq F] in
/-- **Perfect correctness of the nonrecursive Hachi commitment scheme**: for every committed
multilinear polynomial and every evaluation query, the honest run — key generation, balanced
commitment, and the complete composed opening — is accepted with probability `1`.

Hypotheses, by role: the chain's own parameter conditions
(`completeThroughSumcheckReduction_perfectCompleteness`'s, including the reverse range
orientation `hZeroγ` of the nested zero-check seam, which together with the bundled digit-base
facts pins `P.γ = P.bZero − 1 < q/2` — `pinned_of_soundness_orientations`, realized at every
digit base by `ofPinnedDigitBase`); and the two environment conditions `hInit`/`hKeygen` — the
ambient state and the simulated key-generation sampling must never fail, since an adversarial
`impl` could fail and then no scheme is correct.

Depends on the admitted `Reduction.append_completeness` through the appends; the adapter, the
terminal link, and the correctness bridge are axiom-clean. -/
theorem hachiNonrecursive_perfectCorrectness
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r).Challenge i)]
    (P : HonestRangeParams q)
    [SampleableType (Simple.PublicParams 𝓜(q, α) innerRows ((2 ^ m) * Nat.clog P.b q))]
    [SampleableType
      (Simple.PublicParams 𝓜(q, α) outerRows ((2 ^ r) * (innerRows * Nat.clog P.b q)))]
    [SampleableType (Simple.PublicParams 𝓜(q, α) dRows ((2 ^ r) * Nat.clog P.b q))]
    (init : ProbComp σ) (impl : QueryImpl unifSpec (StateT σ ProbComp))
    (hInit : NeverFail init)
    (hKeygen : ∀ s : σ, NeverFail ((simulateQ impl
      (keygen (q := q) (α := α) (innerRows := innerRows) (outerRows := outerRows)
        (dRows := dRows) (m := m) (r := r) P.b)).run s))
    (hcap : zBound ≤ balancedDigitCapacity P.b τ)
    (hzb : 2 ^ r * ω * (P.b / 2) ≤ zBound) (hτ : 0 < τ)
    (hclog : 0 < Nat.clog P.b q) (hd : 0 < 𝓜(q, α).φ.natDegree) (hbZero : 0 < P.bZero)
    (K : LiftCom (LiftedWitness 𝓜(q, α) (μ₀ P) n₀) (liftShort 𝓜(q, α) P.γ P.bZero))
    [DecidableEq K.TCom]
    (φF : ZMod q →+* F)
    (hμn : ((μ₀ P) + n₀ * rhoDigitCount q P.bZero) * 𝓜(q, α).φ.natDegree ≤ 2 ^ (M + 1))
    (hZeroγ : P.bZero - 1 ≤ P.γ) :
    Commitment.perfectCorrectness init impl
      (hachiNonrecursive (F := F) (ω := ω) (M := M) (m₁ := m₁) P hcap K hd hbZero φF) := by
  refine Commitment.perfectCorrectness_of_opening_perfectCompleteness init impl _
    (fun ck _vk => relCommitInput P.b P.hb ck) hInit hKeygen ?_ ?_ ?_
  · -- The committer is deterministic (`pure`), so its simulation never fails.
    intro data ck s
    exact ⟨by simp [hachiNonrecursive]⟩
  · -- The honest keygen/commit outputs satisfy the input relation.
    intro data query ck vk cm dc _hkg hcm
    simp only [hachiNonrecursive, support_pure, Set.mem_singleton_iff] at hcm
    exact ⟨hcm, rfl⟩
  · -- The composed opening is perfectly complete from every post-setup state.
    intro ck vk _hkg s
    exact hachiNonrecursiveOpening_perfectCompleteness (F := F) (ω := ω) (M := M) (m₁ := m₁)
      (βSq := (2 ^ m) * Nat.clog P.b q * (𝓜(q, α).φ.natDegree * (P.b / 2) ^ 2)) (κ := 1)
      P (pure s) impl ck hcap hzb hτ hclog hd hbZero K φF hμn hZeroγ le_rfl le_rfl

end Scheme

end ArkLib.Lattices.Ajtai.InnerOuter
