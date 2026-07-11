/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Generic.Relations

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
open scoped NNReal

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
