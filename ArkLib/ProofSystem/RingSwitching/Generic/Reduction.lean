/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Generic.Relations
import ArkLib.OracleReduction.Security.ChallengeRound
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Generic Ring-Switching — The Phase Reduction (S6-ii)

The hand-written `ProtocolSpec 2` **ring-switch phase**: the prover sends the recombination
slices, the verifier checks them against the input claims (the [BRW26] Remark-5 read-back —
DP24's "Check 1" in family form) and replies with a batching challenge; the output is the
batched sumcheck claim. Written **without** the composition operators, whose upstream
`OracleVerifier.append.verify` is sorried — so every definition in this file is sorry-free and
axiom-clean (the composed end-to-end `ringSwitch` is quarantined in `Generic/Assembly.lean`).

## The claim-consistency check is soundness-critical

The S6 design review (roadmap §8) found that omitting the verifier's check of the slices
against the claims `α` makes the phase's round-by-round knowledge soundness **false**: an
adversary sends the *honest* slices of a committed `t'₀` against a false claim vector `α`
(so `phaseRelIn` is empty while `phaseRelOut` holds with probability 1). The check
(`car.claimConsistent`) closes exactly this: a slice vector passing the check pins the claims
to the recombination read-back, which `openingDecomposition_injective` makes unique. The
verifier fails via `OptionT` `failure` — not via a dummy output statement (the legacy
`failureState` pattern, whose all-zero dummy can itself land in a relation).

## Relations

* `phaseRelIn` — the anchor `openingClaimRel` **and** the binding conjunct
  `pc.commitsTo (packedMLE wit)`: exactly the oracle-extended input relation promised at S5.
* `phaseRelOut` — the batched claim `sumcheckClaimRel` at the verifier's challenge weights
  **and** `commitsTo` carried through (the tail of the chain must land on `pcs.evalRel`).

Chain coherence for the honest prover is `sumcheckClaim_of_slices` (`Relations.lean`); the
read-back direction (check-passing slices anchor the claims) is the Remark-5 read-back lemma.

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024). Construction 3.1, steps 1–5.
- [BRW26] Bünz, Rothblum, Wang. "Flock: Fast Proving for Batch Boolean Computations."
  Cryptology ePrint Archive, Report 2026/1329. Appendix B, Remark 5.
- [RSG] "Ring switching, generalized." Note, leanEthereum/leanVM-b repository.
-/

noncomputable section

namespace RingSwitching.Generic

open OracleSpec OracleComp ProtocolSpec Module MvPolynomial Sumcheck.Structured
  ProbabilityTheory
open scoped NNReal ENNReal

variable {B : Type} [CommRing B] (car : RingSwitchCarrier B) (m : ℕ)
  (bat : BatchingStrategy car.P car.ιE) (pc : PackedCommitment car.P m)

-- The commitment's oracle interfaces, as instances (they are structure fields; registering
-- them is additive and lets the oracle verifier below elaborate against `pc.OStmt`).
attribute [instance] PackedCommitment.Oᵢ

/-! ## Protocol specification -/

/-- The ring-switch phase protocol: the prover sends the slices `s : ιE → P` (design step 4),
the verifier replies with a batching challenge (design step 5). -/
@[reducible]
def pSpecRingSwitchPhase : ProtocolSpec 2 :=
  ⟨![.P_to_V, .V_to_P], ![car.ιE → car.P, bat.Challenge]⟩

instance : ∀ j, OracleInterface ((pSpecRingSwitchPhase car bat).Message j)
  | ⟨0, _⟩ => OracleInterface.instDefault -- the slices, read whole (as DP24 sends ŝ)
  | ⟨1, _⟩ => OracleInterface.instDefault -- vacuous (V_to_P round)

instance : ∀ j, SampleableType ((pSpecRingSwitchPhase car bat).Challenge j)
  | ⟨0, h⟩ => by nomatch h -- P_to_V round has no challenge
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact SampleableType.ofFintype _

/-! ## Honest slices -/

namespace RingSwitchCarrier

/-- The honest prover's slices (design step 4): `sᵤ = ∑_y A(y,u) • t'(y)` — the eq-weighted
hypercube sums of the packed polynomial, i.e. the canonical `sliceRel` witness. -/
def honestSlices {m : ℕ} (r : Fin m → car.E) (t' : MultilinearPoly car.P m) :
    car.ιE → car.P :=
  fun u => ∑ y : Fin m → Fin 2, car.eqCoord r y u • t'.val.eval (y : Fin m → car.P)

/-- The honest slices are (by definition) the `sliceRel` witness for `t'`. -/
theorem honestSlices_mem_sliceRel {m : ℕ} (r : Fin m → car.E)
    (t' : MultilinearPoly car.P m) :
    (car.honestSlices r t', t') ∈ car.sliceRel m r :=
  fun _ => rfl

end RingSwitchCarrier

/-! ## Prover -/

/-- The phase prover's state: statement + commitment oracles + family throughout; the packed
polynomial after packing; the challenge once received. -/
def PhasePrvState : Fin (2 + 1) → Type
  | ⟨0, _⟩ => (((car.ιP → car.E) × (Fin m → car.E)) × (∀ j, pc.OStmt j))
      × (car.ιP → MultilinearPoly B m)
  | ⟨1, _⟩ => (((car.ιP → car.E) × (Fin m → car.E)) × (∀ j, pc.OStmt j))
      × MultilinearPoly car.P m
  | _ => ((((car.ιP → car.E) × (Fin m → car.E)) × (∀ j, pc.OStmt j))
      × MultilinearPoly car.P m) × bat.Challenge

/-- The honest phase prover: packs the family, sends the honest slices, and outputs the
batched sumcheck claim at the received challenge together with the packed witness. -/
def ringSwitchPhaseProver :
    OracleProver (oSpec := []ₒ)
      (StmtIn := (car.ιP → car.E) × (Fin m → car.E)) (OStmtIn := pc.OStmt)
      (WitIn := car.ιP → MultilinearPoly B m)
      (StmtOut := ((Fin m → car.E) × bat.Challenge) × car.P) (OStmtOut := pc.OStmt)
      (WitOut := MultilinearPoly car.P m)
      (pSpec := pSpecRingSwitchPhase car bat) where
  PrvState := PhasePrvState car m bat pc

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => ((stmt, oStmt), wit)

  sendMessage
    | ⟨0, _⟩ => fun ((stmt, oStmt), wit) => do
      -- Design steps 1+4: pack the family, send the honest slices.
      let t' := car.packedMLE wit
      return ⟨car.honestSlices stmt.2 t', ((stmt, oStmt), t')⟩
    | ⟨1, h⟩ => fun _ => by nomatch h -- V_to_P round

  receiveChallenge
    | ⟨0, h⟩ => by nomatch h -- P_to_V round
    | ⟨1, _⟩ => fun st => do
      return fun c => (st, c)

  output := fun (((stmt, oStmt), t'), c) => do
    -- Design step 5: the batched sumcheck target at the verifier's challenge.
    let σ := ∑ u, bat.weight c u * car.honestSlices stmt.2 t' u
    return (⟨((stmt.2, c), σ), oStmt⟩, t')

/-! ## Verifier -/

open scoped Classical in
/-- The phase verifier: reads the slices, **checks them against the input claims** (the
[BRW26] Remark-5 read-back; soundness-critical, see the module docstring), samples the
batching challenge, and outputs the batched sumcheck target. Fails via `OptionT` on a bad
slice vector. (`Classical`: the check is a `Prop`; the verifier is already noncomputable.) -/
def ringSwitchPhaseVerifier :
    OracleVerifier (oSpec := []ₒ)
      (StmtIn := (car.ιP → car.E) × (Fin m → car.E)) (OStmtIn := pc.OStmt)
      (StmtOut := ((Fin m → car.E) × bat.Challenge) × car.P) (OStmtOut := pc.OStmt)
      (pSpec := pSpecRingSwitchPhase car bat) where
  verify := fun stmt challenges => do
    -- Read the slices (whole-message oracle, as DP24's V reads ŝ).
    let s : car.ιE → car.P ← query
      (spec := [(pSpecRingSwitchPhase car bat).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    -- The claim-consistency check (design review F1; DP24 Check 1 in family form).
    if car.claimConsistent stmt.1 s then
      let c := challenges ⟨1, rfl⟩
      return ((stmt.2, c), ∑ u, bat.weight c u * s u)
    else
      failure
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The ring-switch phase, as a hand-written oracle reduction (no composition operators:
sorry-free, axiom-clean definitions). -/
def ringSwitchPhase :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := (car.ιP → car.E) × (Fin m → car.E)) (OStmtIn := pc.OStmt)
      (WitIn := car.ιP → MultilinearPoly B m)
      (StmtOut := ((Fin m → car.E) × bat.Challenge) × car.P) (OStmtOut := pc.OStmt)
      (WitOut := MultilinearPoly car.P m)
      (pSpec := pSpecRingSwitchPhase car bat) where
  prover := ringSwitchPhaseProver car m bat pc
  verifier := ringSwitchPhaseVerifier car m bat pc

/-! ## Relations -/

/-- **The phase input relation** (the oracle-extended anchor promised at S5): the semantic
anchor `openingClaimRel` — every claim is the family's evaluation at `r` — **and** the
binding conjunct: the commitment commits to the *packed* family. -/
def phaseRelIn :
    Set ((((car.ιP → car.E) × (Fin m → car.E)) × (∀ j, pc.OStmt j))
      × (car.ιP → MultilinearPoly B m)) :=
  { x | ((x.1.1.1, x.1.1.2), x.2) ∈ car.openingClaimRel m
      ∧ pc.commitsTo x.1.2 (car.packedMLE x.2) }

/-- **The phase output relation**: the batched sumcheck claim at the challenge's weights
(`sumcheckClaimRel`), with the binding conjunct carried through (the relation chain's tail
must land on the PCS's `evalRel`). -/
def phaseRelOut :
    Set ((((((Fin m → car.E) × bat.Challenge) × car.P)) × (∀ j, pc.OStmt j))
      × MultilinearPoly car.P m) :=
  { x | (x.1.1.2, x.2) ∈ car.sumcheckClaimRel m x.1.1.1.1 (bat.weight x.1.1.1.2)
      ∧ pc.commitsTo x.1.2 x.2 }

/-! ## Round-by-round error -/

/-- The phase's round-by-round knowledge error, as a per-round **vector**: the batching
strategy's separation error at the (single) challenge round. -/
def phaseRBRError : (pSpecRingSwitchPhase car bat).ChallengeIdx → ℝ≥0
  | ⟨1, _⟩ => bat.error
  | _ => 0

/-! ## Round-by-round knowledge-soundness components -/

/-- Intermediate witness types for the phase's RBR extraction: the family before the slices
are sent; the packed polynomial once they are (functionality pins it); the packed polynomial
at the end (= `WitOut`). -/
def phaseWitMid : Fin (2 + 1) → Type
  | ⟨0, _⟩ => car.ιP → MultilinearPoly B m
  | ⟨1, _⟩ => MultilinearPoly car.P m
  | ⟨2, _⟩ => MultilinearPoly car.P m

/-- The phase's round-by-round extractor: the challenge round is witness-preserving; the
message round reads the family back through `unpack` (the section of `packedMLE` —
[BRW26] Remark 5's "uniqueness of the `B`-decomposition" in extractor form). -/
noncomputable def phaseRbrExtractor :
    Extractor.RoundByRound []ₒ
      (StmtIn := ((car.ιP → car.E) × (Fin m → car.E)) × (∀ j, pc.OStmt j))
      (WitIn := car.ιP → MultilinearPoly B m)
      (WitOut := MultilinearPoly car.P m)
      (pSpec := pSpecRingSwitchPhase car bat)
      (WitMid := phaseWitMid car m) where
  eqIn := rfl
  extractMid m' _ _ witSucc :=
    match m' with
    | ⟨0, _⟩ => car.unpack witSucc
    | ⟨1, _⟩ => witSucc
  extractOut _ _ witOut := witOut

/-- **The phase's RBR knowledge soundness**, as the framework proposition against the fixed
anchored relations and the per-round error vector (`bat.error` at the single challenge
round). Recorded as a `Prop`-valued definition (roadmap §8, F3): its proof — the batching
round via `BatchingStrategy.separates` + `commitsTo_functional` — is the S6 stretch goal,
and must never be asserted as a bare `theorem … := sorry`. -/
def ringSwitchPhaseRBRKnowledgeSound {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) : Prop :=
  OracleVerifier.rbrKnowledgeSoundness
    (verifier := ringSwitchPhaseVerifier car m bat pc)
    (init := init) (impl := impl)
    (relIn := phaseRelIn car m pc)
    (relOut := phaseRelOut car m bat pc)
    (rbrKnowledgeError := phaseRBRError car bat)

/-! ## Round-by-round knowledge soundness (the S6 stretch goal) -/

section RBRKnowledgeSoundness

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- Auxiliary: an everywhere-false event has probability `0` under any `PMF`. -/
private lemma pr_eq_zero_of_forall_not {α : Type} (D : PMF α) (P : α → Prop)
    (h : ∀ x, ¬ P x) : Pr_{ let x ← D }[ P x ] = 0 := by
  classical
  rw [prob_tsum_form_singleton]
  simp [h]

/-- **The phase's knowledge state function.** Round 0 tracks `phaseRelIn` of the extracted
witness (forced by `toFun_empty`); round 1 (after the slices `s`) tracks the verifier's
Remark-5 check, the binding conjunct, and the slice relation for the intermediate packed
witness; round 2 (the full transcript) tracks the check again (the verifier `failure`s
without it, so no output can land in `phaseRelOut`), binding, and the batched sumcheck claim
at the challenge's weights.

`[IsDomain car.E]` enters only through `toFun_next` at the message round: the Remark-5
read-back `openingClaimRel_of_claimConsistent` (the logged S6 deviation, see
`Relations.lean`). -/
noncomputable def phaseKnowledgeStateFunction [IsDomain car.E] :
    (ringSwitchPhaseVerifier car m bat pc).KnowledgeStateFunction init impl
      (phaseRelIn car m pc) (phaseRelOut car m bat pc)
      (phaseRbrExtractor car m bat pc) where
  toFun
    | ⟨0, _⟩ => fun stmtIn _ witMid => (stmtIn, witMid) ∈ phaseRelIn car m pc
    | ⟨1, _⟩ => fun stmtIn tr witMid =>
        car.claimConsistent stmtIn.1.1 (tr 0)
          ∧ pc.commitsTo stmtIn.2 witMid
          ∧ ((tr 0 : car.ιE → car.P), witMid) ∈ car.sliceRel m stmtIn.1.2
    | ⟨2, _⟩ => fun stmtIn tr witMid =>
        car.claimConsistent stmtIn.1.1 (tr 0)
          ∧ pc.commitsTo stmtIn.2 witMid
          ∧ ((∑ u, bat.weight (tr 1) u * (tr 0 : car.ιE → car.P) u), witMid)
              ∈ car.sumcheckClaimRel m stmtIn.1.2 (bat.weight (tr 1))
  toFun_empty := fun stmtIn witMid => Iff.rfl
  toFun_next
    | ⟨0, _⟩ => fun _ stmtIn tr msg witMid h => by
        obtain ⟨hc, hcommit, hslice⟩ := h
        refine ⟨car.openingClaimRel_of_claimConsistent hc hslice, ?_⟩
        change pc.commitsTo _ (car.packedMLE (car.unpack witMid))
        rw [car.packedMLE_unpack]
        exact hcommit
    | ⟨1, _⟩ => fun hDir => absurd hDir (by simp)
  toFun_full := fun stmtIn tr witOut h => by
    classical
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hRel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [Verifier.run, OracleVerifier.toVerifier, ringSwitchPhaseVerifier,
      OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s0, _, hx⟩ := hx
    simp only [simulateQ_optionT_bind] at hx
    -- The verifier's slice read is deterministic: the simulated whole-message query *is*
    -- (definitionally) the transcript's round-0 message.
    have hq : (simulateQ
          (OracleInterface.simOracle2 ([]ₒ : OracleSpec PEmpty.{1}) stmtIn.2
            (FullTranscript.messages (pSpec := pSpecRingSwitchPhase car bat) tr))
          (query (spec := [(pSpecRingSwitchPhase car bat).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
            : OptionT (OracleComp (([]ₒ : OracleSpec PEmpty.{1})
                + ([pc.OStmt]ₒ + [(pSpecRingSwitchPhase car bat).Message]ₒ))) _)
          : OptionT (OracleComp ([]ₒ : OracleSpec PEmpty.{1})) _)
        = (pure (some (tr (0 : Fin 2)))
            : OracleComp ([]ₒ : OracleSpec PEmpty.{1}) (Option (car.ιE → car.P))) := rfl
    rw [hq] at hx
    -- Collapse the (definitional) pure-binds: the bound slice variable *is* `tr 0`, so the
    -- verifier's check becomes a concrete `if` we can case on.
    replace hx : some x ∈ _root_.support (StateT.run'
        ((simulateQ impl (simulateQ
            (OracleInterface.simOracle2 ([]ₒ : OracleSpec PEmpty.{1}) stmtIn.2
              (FullTranscript.messages (pSpec := pSpecRingSwitchPhase car bat) tr))
            (if car.claimConsistent stmtIn.1.1 (tr (0 : Fin 2))
              then pure ((stmtIn.1.2, (tr (1 : Fin 2) : bat.Challenge)),
                ∑ u, bat.weight (tr (1 : Fin 2) : bat.Challenge) u
                  * (tr (0 : Fin 2) : car.ιE → car.P) u)
              else failure
              : OptionT (OracleComp (([]ₒ : OracleSpec PEmpty.{1})
                  + ([pc.OStmt]ₒ + [(pSpecRingSwitchPhase car bat).Message]ₒ)))
                  (((Fin m → car.E) × bat.Challenge) × car.P)))
            : OptionT (StateT σ ProbComp) (((Fin m → car.E) × bat.Challenge) × car.P))
          >>= (fun a => pure (a, fun i => stmtIn.2 i))
            : OptionT (StateT σ ProbComp) ((((Fin m → car.E) × bat.Challenge) × car.P)
                × ((i : pc.ιC) → pc.OStmt i)))
        s0) := hx
    by_cases hc : car.claimConsistent stmtIn.1.1 (tr (0 : Fin 2))
    · -- Check passes: the run is (definitionally) `pure` of the batched output; `x` is pinned.
      rw [if_pos hc] at hx
      replace hx : some x ∈ _root_.support
          ((pure (some (((stmtIn.1.2, (tr (1 : Fin 2) : bat.Challenge)),
              ∑ u, bat.weight (tr (1 : Fin 2) : bat.Challenge) u
                * (tr (0 : Fin 2) : car.ιE → car.P) u),
            fun i => stmtIn.2 i)) : ProbComp _)) := hx
      simp only [support_pure] at hx
      obtain rfl := Option.some.inj hx
      exact ⟨hc, hRel.2, hRel.1⟩
    · -- Check fails: the run is (definitionally) `failure`, whose support has no `some`.
      rw [if_neg hc] at hx
      replace hx : some x ∈ _root_.support
          ((pure none : ProbComp (Option ((((Fin m → car.E) × bat.Challenge) × car.P)
              × ((i : pc.ιC) → pc.OStmt i))))) := hx
      simp at hx

/-- **The per-prefix challenge-round bound**: with the prefix (statement, commitment oracles,
slices `s`) fixed, the round-1→2 bad event of the RBR game — some intermediate witness fails
the round-1 state but satisfies the round-2 state after the challenge — has probability at
most `bat.error` over a uniform batching challenge. `commitsTo_functional` collapses the
`∃ witMid` to a single committed `t'₀`; the surviving case is exactly
`BatchingStrategy.separates` on `s` vs the honest slices of `t'₀`
(via `sumcheckClaim_of_slices`). -/
private theorem phase_badEvent_le
    (α : car.ιP → car.E) (r : Fin m → car.E) (oStmt : ∀ j, pc.OStmt j) (s : car.ιE → car.P) :
    Pr_{ let c ←$ᵖ bat.Challenge }[
      ∃ t' : MultilinearPoly car.P m,
        ¬(car.claimConsistent α s ∧ pc.commitsTo oStmt t' ∧ (s, t') ∈ car.sliceRel m r)
          ∧ (car.claimConsistent α s ∧ pc.commitsTo oStmt t'
              ∧ ((∑ u, bat.weight c u * s u), t') ∈ car.sumcheckClaimRel m r (bat.weight c)) ]
      ≤ (bat.error : ℝ≥0∞) := by
  classical
  by_cases hlive : ∃ t'₀, pc.commitsTo oStmt t'₀ ∧ car.claimConsistent α s
      ∧ (s, t'₀) ∉ car.sliceRel m r
  · -- The live case: a committed `t'₀` whose honest slices differ from `s`.
    obtain ⟨t'₀, hcm, _, hsl⟩ := hlive
    have hne : s ≠ car.honestSlices r t'₀ := fun hEq => hsl fun u => congrFun hEq u
    refine le_trans (Pr_le_Pr_of_implies _ _ _ ?_)
      (bat.separates s (car.honestSlices r t'₀) hne)
    rintro c ⟨t', -, -, hcm', hsum⟩
    obtain rfl : t' = t'₀ := pc.commitsTo_functional hcm' hcm
    have hsum' : (∑ u, bat.weight c u * s u)
        = ∑ y : Fin m → Fin 2, car.bridge (bat.weight c) (eqTilde r (car.boolToE y))
            * t'.val.eval (y : Fin m → car.P) := hsum
    have h2 : (∑ u, bat.weight c u * car.honestSlices r t' u)
        = ∑ y : Fin m → Fin 2, car.bridge (bat.weight c) (eqTilde r (car.boolToE y))
            * t'.val.eval (y : Fin m → car.P) :=
      car.sumcheckClaim_of_slices (car.honestSlices_mem_sliceRel r t') (bat.weight c)
    exact hsum'.trans h2.symm
  · -- The empty case: every committed-and-checked `t'` already satisfies the round-1 state.
    push Not at hlive
    refine le_of_eq_of_le (pr_eq_zero_of_forall_not _ _ ?_) zero_le'
    rintro c ⟨t', hnot1, hc, hcm, -⟩
    exact hnot1 ⟨hc, hcm, hlive t' hcm hc⟩

/-- **Round-by-round knowledge soundness of the ring-switch phase** (the S6 stretch goal):
the phase reduction, against the anchored relations `phaseRelIn`/`phaseRelOut`, is
round-by-round knowledge sound with error `bat.error` at the (single) batching-challenge
round. Witnesses: `phaseWitMid`, `phaseRbrExtractor`, `phaseKnowledgeStateFunction`; the
challenge round factors through `Verifier.probEvent_challengeRound_le` and lands on
`phase_badEvent_le` — `commitsTo_functional` collapses the `∃ witMid`, and the surviving
event is exactly `BatchingStrategy.separates` on the sent slices vs. the honest slices of
the committed polynomial (via `sumcheckClaim_of_slices`).

`[IsDomain car.E]` is the accepted S6 hypothesis (Remark-5 read-back, see `Relations.lean`);
no `[Fintype car.P]`/`[IsDomain car.P]` is needed — the batching error is abstract and
`bat.separates` is a strategy field. -/
theorem ringSwitchPhase_rbrKnowledgeSound [IsDomain car.E] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ringSwitchPhaseRBRKnowledgeSound car m bat pc init impl := by
  refine ⟨phaseWitMid car m, phaseRbrExtractor car m bat pc,
    phaseKnowledgeStateFunction car m bat pc init impl, ?_⟩
  intro stmtIn witIn prover i
  rcases i with ⟨⟨_ | _ | iv, hlt⟩, hdir⟩
  · -- Round 0 is P_to_V: not a challenge round.
    exact nomatch hdir
  · -- Round 1: the batching challenge. Factor the game through the fixed prefix, then
    -- the per-prefix PMF bound `phase_badEvent_le` (everything else is definitional:
    -- the `Fin.snoc` reads of the extended transcript reduce to the prefix reads).
    letI : Fintype ((pSpecRingSwitchPhase car bat).Challenge ⟨⟨1, hlt⟩, hdir⟩) :=
      inferInstanceAs (Fintype bat.Challenge)
    letI : Nonempty ((pSpecRingSwitchPhase car bat).Challenge ⟨⟨1, hlt⟩, hdir⟩) :=
      inferInstanceAs (Nonempty bat.Challenge)
    refine Verifier.probEvent_rbrGame_le init impl stmtIn witIn prover _ ?_
    intro tr log
    exact phase_badEvent_le car m bat pc stmtIn.1.1 stmtIn.1.2 stmtIn.2 (tr (0 : Fin 1))
  · -- No round ≥ 2 exists.
    exact absurd hlt (by omega)

end RBRKnowledgeSoundness

/-! ## Perfect completeness -/

section Completeness

/-- **Point form of phase completeness**: for an input in `phaseRelIn` and *any* batching
challenge `c`, the honest prover's outputs — the batched claim over its honest slices, the
carried commitment oracles, and the packed witness — land in `phaseRelOut`. The two conjuncts
are `sumcheckClaim_of_slices` (chain coherence at the honest slices) and the binding conjunct
carried from the input. -/
theorem honest_mem_phaseRelOut
    {stmt : (car.ιP → car.E) × (Fin m → car.E)} {oStmt : ∀ j, pc.OStmt j}
    {wit : car.ιP → MultilinearPoly B m}
    (hIn : ((stmt, oStmt), wit) ∈ phaseRelIn car m pc) (c : bat.Challenge) :
    ((((stmt.2, c),
        ∑ u, bat.weight c u * car.honestSlices stmt.2 (car.packedMLE wit) u), oStmt),
      car.packedMLE wit) ∈ phaseRelOut car m bat pc :=
  ⟨car.sumcheckClaim_of_slices (car.honestSlices_mem_sliceRel _ _) _, hIn.2⟩

/-- **The honest slices pass the verifier's Remark-5 check**: point form of the check's
completeness against the anchored input. `[IsDomain car.E]` is the accepted S6 hypothesis
(see `aeval_unpack_of_slices`). -/
theorem honest_claimConsistent [IsDomain car.E]
    {stmt : (car.ιP → car.E) × (Fin m → car.E)} {oStmt : ∀ j, pc.OStmt j}
    {wit : car.ιP → MultilinearPoly B m}
    (hIn : ((stmt, oStmt), wit) ∈ phaseRelIn car m pc) :
    car.claimConsistent stmt.1 (car.honestSlices stmt.2 (car.packedMLE wit)) :=
  car.claimConsistent_of_slices hIn.1 (car.honestSlices_mem_sliceRel _ _)

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- **Perfect completeness of the ring-switch phase** against the anchored relations: on any
input in `phaseRelIn`, the honest execution outputs a pair in `phaseRelOut` (and prover/verifier
statements agree) with probability `1`. The honest slices pass the verifier's claim-consistency
check (`honest_claimConsistent`), so the `OptionT` `failure` branch is never taken; the batched
output is in the relation for every sampled challenge (`honest_mem_phaseRelOut`).

`[IsDomain car.E]` is the accepted S6 hypothesis (Remark-5 read-back; see `Relations.lean`). -/
theorem ringSwitchPhase_perfectCompleteness [IsDomain car.E] :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (relIn := phaseRelIn car m pc)
      (relOut := phaseRelOut car m bat pc)
      (oracleReduction := ringSwitchPhase car m bat pc) := by
  unfold OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmtIn witIn hRel
  -- Resolve the two round directions via the framework per-direction `processRound` unfolds,
  -- then unfold the reduction run and the 2-round prover (`Fin.induction_two`).
  have h0 : (pSpecRingSwitchPhase car bat).dir 0 = .P_to_V := rfl
  have h1 : (pSpecRingSwitchPhase car bat).dir 1 = .V_to_P := rfl
  simp only [OracleReduction.toReduction, Reduction.run, ringSwitchPhase,
    ringSwitchPhaseProver, OracleVerifier.toVerifier, ringSwitchPhaseVerifier,
    Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_P_to_V 0 h0,
    Prover.processRound_of_dir_eq_V_to_P 1 h1,
    Verifier.run, bind_pure_comp]
  -- Reduce `Pr[…] = 1` to a support-membership obligation.
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro x hx
  -- Peel the prover-run prefix of `Reduction.run`.
  obtain ⟨proverResult, hPR, hx⟩ := OptionT.mem_support_run_lift_bind _ _ hx
  -- Peel the prover-run bind tree by *definitional*-unification `obtain` (the elaborated
  -- `Fin.induction` bind tree is defeq but not syntactically `>>=`, so `rw`-based peelers
  -- do not engage; the peelers unify straight through the identity `monadLift` wrapper):
  -- output map, round-1 (challenge `c`, pure `receiveChallenge`), round-0 (pure base, pure
  -- `sendMessage`).
  obtain ⟨A, hA, hPR⟩ := OracleComp.mem_support_bind_peel _ _ hPR
  obtain ⟨out, hout, hPR⟩ := OracleComp.mem_support_map_peel _ _ hPR
  have hout := OracleComp.eq_of_mem_support_pure _ hout
  obtain ⟨A1, hA1, hA⟩ := OracleComp.mem_support_bind_peel _ _ hA
  obtain ⟨c, _, hA⟩ := OracleComp.mem_support_bind_peel _ _ hA
  obtain ⟨f, hf, hA⟩ := OracleComp.mem_support_map_peel _ _ hA
  have hf := OracleComp.eq_of_mem_support_pure _ hf
  obtain ⟨A0, hA0, hA1⟩ := OracleComp.mem_support_bind_peel _ _ hA1
  have hA0 := OracleComp.eq_of_mem_support_pure _ hA0
  obtain ⟨msg, hmsg, hA1⟩ := OracleComp.mem_support_map_peel _ _ hA1
  have hmsg := OracleComp.eq_of_mem_support_pure _ hmsg
  subst hA0 hmsg hA1 hf hA hout hPR
  -- Reduce the substituted tuple projections; the transcript is now the concrete
  -- `snoc (snoc default honestSlices) c`.
  dsimp only at hx
  -- The verifier's whole-message query is (definitionally) the transcript's round-0 read —
  -- the honest slices (same move as `phaseKnowledgeStateFunction.toFun_full`).
  simp only [simulateQ_optionT_bind] at hx
  have hq : (simulateQ
        (OracleInterface.simOracle2 ([]ₒ : OracleSpec PEmpty.{1}) stmtIn.2
          (FullTranscript.messages (pSpec := pSpecRingSwitchPhase car bat)
            (Transcript.concat (m := (1 : Fin 2)) c
              (Transcript.concat (m := (0 : Fin 2))
                (car.honestSlices stmtIn.1.2 (car.packedMLE witIn))
                (default : (pSpecRingSwitchPhase car bat).Transcript 0)))))
        (query (spec := [(pSpecRingSwitchPhase car bat).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
          : OptionT (OracleComp (([]ₒ : OracleSpec PEmpty.{1})
              + ([pc.OStmt]ₒ + [(pSpecRingSwitchPhase car bat).Message]ₒ))) _)
        : OptionT (OracleComp ([]ₒ : OracleSpec PEmpty.{1})) _)
      = (pure (car.honestSlices stmtIn.1.2 (car.packedMLE witIn))
          : OptionT (OracleComp ([]ₒ : OracleSpec PEmpty.{1})) (car.ιE → car.P)) := rfl
  rw [hq] at hx
  -- The honest slices pass the Remark-5 check.
  have hcheck : car.claimConsistent stmtIn.1.1
      (car.honestSlices stmtIn.1.2 (car.packedMLE witIn)) :=
    honest_claimConsistent car m pc hRel
  classical
  -- Collapse the (definitional) `pure`-bind: the bound slice variable *is* the honest slices,
  -- so the verifier's `OptionT` subterm becomes a concrete `if` on `car.claimConsistent`.
  replace hx : x ∈ _root_.support
      (((do
          let stmtOut ←
            liftM
                ((fun a ↦ (a, fun i ↦ stmtIn.2 i)) <$>
                  simulateQ
                    (OracleInterface.simOracle2 ([]ₒ : OracleSpec PEmpty.{1}) stmtIn.2
                      (FullTranscript.messages (pSpec := pSpecRingSwitchPhase car bat)
                        (Transcript.concat (m := (1 : Fin 2)) c
                          (Transcript.concat (m := (0 : Fin 2))
                            (car.honestSlices stmtIn.1.2 (car.packedMLE witIn))
                            (default : (pSpecRingSwitchPhase car bat).Transcript 0)))))
                    (if car.claimConsistent stmtIn.1.1
                          (car.honestSlices stmtIn.1.2 (car.packedMLE witIn)) then
                      pure
                        ((stmtIn.1.2, c),
                          ∑ u, bat.weight c u
                            * car.honestSlices stmtIn.1.2 (car.packedMLE witIn) u)
                    else failure
                      : OptionT (OracleComp (([]ₒ : OracleSpec PEmpty.{1})
                          + ([pc.OStmt]ₒ + [(pSpecRingSwitchPhase car bat).Message]ₒ)))
                          (((Fin m → car.E) × bat.Challenge) × car.P))
                    : OptionT (OracleComp ([]ₒ : OracleSpec PEmpty.{1})) _).run
          Prod.mk
                (Transcript.concat (m := (1 : Fin 2)) c
                    (Transcript.concat (m := (0 : Fin 2))
                      (car.honestSlices stmtIn.1.2 (car.packedMLE witIn))
                      (default : (pSpecRingSwitchPhase car bat).Transcript 0)),
                  (((stmtIn.1.2, c),
                        ∑ u, bat.weight c u
                          * car.honestSlices stmtIn.1.2 (car.packedMLE witIn) u), stmtIn.2),
                  car.packedMLE witIn) <$>
              stmtOut.getM)
        : OptionT (OracleComp _) _).run) := hx
  -- The honest slices pass the Remark-5 check, so the `OptionT` `failure` branch is dead.
  rw [if_pos hcheck] at hx
  -- Everything downstream (`simulateQ σ (pure …)`, `liftM`, `getM`, and the output map) collapses
  -- by defeq to `pure (some finalValue)`; the support then pins `x`.
  replace hx : x ∈ _root_.support
      (pure (some
          ((Transcript.concat (m := (1 : Fin 2)) c
                (Transcript.concat (m := (0 : Fin 2))
                  (car.honestSlices stmtIn.1.2 (car.packedMLE witIn))
                  (default : (pSpecRingSwitchPhase car bat).Transcript 0)),
              (((stmtIn.1.2, c),
                    ∑ u, bat.weight c u
                      * car.honestSlices stmtIn.1.2 (car.packedMLE witIn) u), stmtIn.2),
              car.packedMLE witIn),
            ((stmtIn.1.2, c),
                ∑ u, bat.weight c u
                  * car.honestSlices stmtIn.1.2 (car.packedMLE witIn) u), stmtIn.2))
        : OracleComp _ _) := hx
  obtain rfl := OracleComp.eq_of_mem_support_pure _ hx
  -- Close: batched output in `phaseRelOut` (`honest_mem_phaseRelOut`) and prover/verifier
  -- statement agreement (`rfl`; the honest challenge `c` matches the read-back challenge).
  exact ⟨_, rfl, honest_mem_phaseRelOut car m bat pc hRel c, rfl⟩

end Completeness

/-! ## Sanity / testable deliverables (S6 §5.3) -/

section Sanity

-- INV-2: the phase reduction is statable on the *tower* carrier (arbitrary field extension,
-- arbitrary finite rank), with any batching strategy and any commitment…
example {K L ι : Type} [Field K] [Field L] [Algebra K L] [Fintype ι] (β : Basis ι K L)
    (m : ℕ) (bat : BatchingStrategy (towerCarrier β).P (towerCarrier β).ιE)
    (pc : PackedCommitment (towerCarrier β).P m) :
    OracleReduction (oSpec := []ₒ)
      (StmtIn := ((towerCarrier β).ιP → (towerCarrier β).E) × (Fin m → (towerCarrier β).E))
      (OStmtIn := pc.OStmt)
      (WitIn := (towerCarrier β).ιP → MultilinearPoly K m)
      (StmtOut := ((Fin m → (towerCarrier β).E) × bat.Challenge) × (towerCarrier β).P)
      (OStmtOut := pc.OStmt)
      (WitOut := MultilinearPoly (towerCarrier β).P m)
      (pSpec := pSpecRingSwitchPhase (towerCarrier β) bat) :=
  ringSwitchPhase (towerCarrier β) m bat pc

-- …and on the *decoupled field* carrier (`P = 𝔽₄ ≠ E = 𝔽₈`), the γ-power strategy landed at
-- `ιE` by reindexing (the exact S6 plumbing promised at S3), the trivial commitment.
example :
    letI : IsDomain decoupledFieldCarrier.P := inferInstanceAs (IsDomain (GaloisField 2 2))
    letI : Fintype decoupledFieldCarrier.P :=
      letI : Finite decoupledFieldCarrier.P := inferInstanceAs (Finite (GaloisField 2 2))
      Fintype.ofFinite _
    OracleReduction (oSpec := []ₒ)
      (StmtIn := (decoupledFieldCarrier.ιP → decoupledFieldCarrier.E)
        × (Fin 3 → decoupledFieldCarrier.E))
      (OStmtIn := (PackedCommitment.trivial decoupledFieldCarrier.P 3).OStmt)
      (WitIn := decoupledFieldCarrier.ιP → MultilinearPoly (ZMod 2) 3)
      (StmtOut := ((Fin 3 → decoupledFieldCarrier.E)
        × ((BatchingStrategy.gammaPowers decoupledFieldCarrier.P
            (Fintype.card decoupledFieldCarrier.ιE)).reindex
            (Fintype.equivFin decoupledFieldCarrier.ιE)).Challenge) × decoupledFieldCarrier.P)
      (OStmtOut := (PackedCommitment.trivial decoupledFieldCarrier.P 3).OStmt)
      (WitOut := MultilinearPoly decoupledFieldCarrier.P 3)
      (pSpec := pSpecRingSwitchPhase decoupledFieldCarrier
        ((BatchingStrategy.gammaPowers decoupledFieldCarrier.P
            (Fintype.card decoupledFieldCarrier.ιE)).reindex
            (Fintype.equivFin decoupledFieldCarrier.ιE))) :=
  letI : IsDomain decoupledFieldCarrier.P := inferInstanceAs (IsDomain (GaloisField 2 2))
  letI : Fintype decoupledFieldCarrier.P :=
    letI : Finite decoupledFieldCarrier.P := inferInstanceAs (Finite (GaloisField 2 2))
    Fintype.ofFinite _
  ringSwitchPhase decoupledFieldCarrier 3 _ (PackedCommitment.trivial _ 3)

-- Close-review pins (2026-07-12): `phaseRelIn` is NONEMPTY — true claims + the trivial
-- commitment on honest data — so the RBR theorem's obligation is not discharged by an empty
-- input relation…
example (r : Fin 3 → decoupledToyCarrier.E)
    (Ps : decoupledToyCarrier.ιP → MultilinearPoly (ZMod 2) 3) :
    ((((fun i => MvPolynomial.aeval r (Ps i).val), r),
        fun _ : (PackedCommitment.trivial decoupledToyCarrier.P 3).ιC =>
          decoupledToyCarrier.packedMLE Ps), Ps)
      ∈ phaseRelIn decoupledToyCarrier 3 (PackedCommitment.trivial _ 3) :=
  ⟨fun _ => rfl, rfl⟩

-- …and the RBR theorem itself applies end-to-end at a concrete carrier + PROVEN strategy
-- (γ-powers on 𝔽₄, separation error 3/4 — a real, nonzero, non-unit error).
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    letI : IsDomain decoupledFieldCarrier.P := inferInstanceAs (IsDomain (GaloisField 2 2))
    letI : Fintype decoupledFieldCarrier.P :=
      letI : Finite decoupledFieldCarrier.P := inferInstanceAs (Finite (GaloisField 2 2))
      Fintype.ofFinite _
    ringSwitchPhaseRBRKnowledgeSound decoupledFieldCarrier 3
      ((BatchingStrategy.gammaPowers decoupledFieldCarrier.P
          (Fintype.card decoupledFieldCarrier.ιE)).reindex
          (Fintype.equivFin decoupledFieldCarrier.ιE))
      (PackedCommitment.trivial _ 3) init impl :=
  letI : IsDomain decoupledFieldCarrier.P := inferInstanceAs (IsDomain (GaloisField 2 2))
  letI : Fintype decoupledFieldCarrier.P :=
    letI : Finite decoupledFieldCarrier.P := inferInstanceAs (Finite (GaloisField 2 2))
    Fintype.ofFinite _
  letI : IsDomain decoupledFieldCarrier.E := inferInstanceAs (IsDomain (GaloisField 2 3))
  ringSwitchPhase_rbrKnowledgeSound decoupledFieldCarrier 3 _ _ init impl

-- INV-5 pin: the phase error vector is *definitionally* the strategy's separation error at
-- the challenge round (and 0 elsewhere — there is no other challenge round).
example (i : (pSpecRingSwitchPhase car bat).ChallengeIdx) (h : i.1 = 1) :
    phaseRBRError car bat i = bat.error := by
  rcases i with ⟨i, hi⟩
  subst h
  rfl

end Sanity

end RingSwitching.Generic

end
