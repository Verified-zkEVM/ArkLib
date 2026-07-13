/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Generic.Batching
import ArkLib.ProofSystem.RingSwitching.Generic.Packing
import ArkLib.ProofSystem.RingSwitching.Generic.Recombine

/-!
# Generic Ring-Switching — Anchored Relations + PCS Interface (S5)

Design safety pillars 2 + 4 (see `docs/kb/concepts/ring-switching.md`, "The Generic layer"):
the **framework-fixed relation chain** and the **PCS binding interface**.

## The relation chain (pillar 4: no free `Prop` anywhere)

Every relation of the generic ring switch is a *framework definition* parameterized only by the
carrier and the protocol data — an instance has no hook to substitute a weaker predicate:

* `openingClaimRel` — the input anchor (design step 2): `∀ i, αᵢ = P̂ᵢ(r)`, the family's
  evaluation claims at the common point `r` over the opening algebra `E`. This is the semantic
  statement the end-to-end soundness theorem (S6) is *about*; fixing it here is what makes
  "satisfying the interface" mean "getting the right theorem".
* `sliceRel` — the middle relation after eq-decomposition/recombination (design step 4): the
  prover-sent slices are the eq-weighted hypercube sums of the packed polynomial,
  `sᵤ = ∑_y A(y,u) • t'(y)`.
* `sumcheckClaimRel` — the batched sumcheck input claim (design steps 5–6):
  `σ = ∑_y Φ_w(eq(r,y)) · t'(y)`, i.e. `∑_y B(y)·t'(y) = σ` with `B = Φ∘eq` the multiplier
  (`Bmult`'s defining values). `sumcheckClaim_of_slices` proves the chain coheres: batching
  honest slices with weights `w` *is* the sumcheck claim — via the linchpin `bridge_eqTilde`.
* `claimConsistent` — the **Remark-5 consistency check** ([BRW26] Remark 5; S6 design review F1):
  the phase verifier's read-back of the slices against the input claims,
  `αᵢ = ∑ᵤ (packBasis.repr sᵤ i) • bᵤ^E` — both bases at once. Completeness
  (`claimConsistent_of_slices`, review F6-4) and the soundness read-back to the anchor
  (`openingClaimRel_of_claimConsistent`, review F2, via the generic `unpack`) are proven below;
  both route through `aeval_unpack_of_slices`, whose `[IsDomain car.E]` hypothesis is the one
  logged S6 deviation (eq-expansion of the anchor by root-counting interpolation over `E`).

## The PCS interface (pillar 2: binding is the PCS's proven semantics, not a free hook)

`PackedCommitment` carries `commitsTo : (∀ j, OStmt j) → MultilinearPoly P m → Prop` **plus the
functionality law** `commitsTo_functional` (an oracle statement commits to at most one
polynomial). Functionality is what makes the field *not* a free hook, in two enforced senses:

1. `fun _ _ => True` is *unstatable* as a `commitsTo` (`commitsTo_ne_top`, backed by the `neC`
   well-formedness guard): functionality would collapse all multilinears into one, contradicting
   `Nontrivial P`. Compare the legacy `AbstractOStmtIn.initialCompatibility`, which type-admits
   `True` (design Hole A).
2. It is exactly what the S6 round-by-round argument needs to collapse the `∃ witMid` event of
   `rbrKnowledgeSoundness` to the fixed pair fed to `BatchingStrategy.separates` — without it a
   `|WitMid|` union factor would destroy the batching error bound. (At S5 the law is carried;
   its in-file consumer is `commitsTo_not_top`/`commitsTo_ne_top`, its main consumer is S6.)

`DenseMLPCS` then mirrors the legacy `MLIOPCS` bundle (protocol + perfect completeness + RBR
knowledge soundness) with its input relation *fixed* to `PackedCommitment.evalRel` — evaluation
correctness (`MLPEvalRelation`, reused) **and** `commitsTo` — so the PCS's own security fields
are stated against the instance's binding predicate: the round-0 knowledge state function must
track `commitsTo` *bidirectionally* (`KnowledgeStateFunction.toFun_empty` is an iff), and
completeness must cover every `commitsTo`-satisfying input. Functionality bars the trivial hook;
a bogus-but-functional predicate survives locally but is caught at S6 composition, where the
ring switch's completeness needs honest provers to *satisfy* `evalRel`.

**INV-3 audit note.** `commitsTo` is the *sanctioned* hook-shaped `Prop`-valued field of the
generic layer (well-formedness guards like `neC` are `Prop`-valued too, but are positive
obligations, not hooks):
it is law-constrained (`commitsTo_functional`) and consumed by the structure's own security
fields, unlike the legacy free `initialCompatibility` hook it replaces (retirement of the legacy
hook is the S7 Binius-migration step; the Binius codeword-consistency predicate is re-expressed
in `commitsTo` orientation as `Binius.FRIBinius.biniusCommitsTo`, whose functionality proof —
by unique decoding, over the `witnessNovelCoeffs` cube-table encoding fixed at the S5
close-review — is the logged S7 obligation).

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
- [BRW26] Bünz, Rothblum, Wang. "Flock: Fast Proving for Batch Boolean Computations." Cryptology
  ePrint Archive, Report 2026/1329. Appendix B.
- [RSG] "Ring switching, generalized." Note, leanEthereum/leanVM-b repository.
-/

noncomputable section

namespace RingSwitching.Generic

open OracleSpec OracleComp ProtocolSpec Module MvPolynomial Sumcheck.Structured
open scoped NNReal

/-! ## The framework-fixed relation chain (safety pillar 4) -/

namespace RingSwitchCarrier

variable {B : Type} [CommRing B] (car : RingSwitchCarrier B)

/-- **The input anchor** (design step 2, the semantic core of the S6 `relIn`): the batch of
evaluation claims `∀ i, αᵢ = P̂ᵢ(r)` — each `B`-multilinear of the family evaluates at the
common point `r` over the opening algebra `E` to its claimed value. Statement =
(claims, point); witness = the family. The oracle-reduction `relIn` assembled at S6 extends
this with the input-oracle component and the `commitsTo` binding conjunct; the anchor itself is
framework-fixed — an instance cannot override or weaken it (safety pillar 4) — and
`Nontrivial E` (a carrier field) keeps it non-vacuous (see the non-vacuity `example` below). -/
def openingClaimRel (m : ℕ) :
    Set (((car.ιP → car.E) × (Fin m → car.E)) × (car.ιP → MultilinearPoly B m)) :=
  { x | ∀ i, x.1.1 i = MvPolynomial.aeval x.1.2 (x.2 i).val }

/-- **The slice relation** (design step 4, middle): the prover-sent slices `s : ιE → P` are the
eq-weighted hypercube sums of the packed polynomial, `sᵤ = ∑_y A(y,u) • t'(y)` with
`A(y,u) = eqCoord r y u` the (unique — `openingDecomposition_injective`) `B`-coordinates of
`eq(r,y)` in the opening basis. -/
def sliceRel (m : ℕ) (r : Fin m → car.E) :
    Set ((car.ιE → car.P) × MultilinearPoly car.P m) :=
  { x | ∀ u, x.1 u =
      ∑ y : Fin m → Fin 2, car.eqCoord r y u • x.2.val.eval (y : Fin m → car.P) }

/-- **The batched sumcheck claim** (design steps 5–6, middle): the single claim handed to the
sumcheck, `σ = ∑_y Φ_w(eq(r,y)) · t'(y)` — the hypercube sum of the multiplier `B(y) = Φ(eq(r,y))`
(the values defining `Bmult`) against the packed polynomial. -/
def sumcheckClaimRel (m : ℕ) (r : Fin m → car.E) (w : car.ιE → car.P) :
    Set (car.P × MultilinearPoly car.P m) :=
  { x | x.1 = ∑ y : Fin m → Fin 2,
      car.bridge w (eqTilde r (car.boolToE y)) * x.2.val.eval (y : Fin m → car.P) }

/-- **Chain coherence** (the middle relations compose): batching honest slices with weights `w`
*is* the sumcheck input claim. This is the `bridge_eqTilde` linchpin doing its designed job —
`∑_u wᵤ·sᵤ = ∑_y Φ_w(eq(r,y))·t'(y)` by expanding each slice and reassembling the
eq-coordinates through `Φ`. -/
theorem sumcheckClaim_of_slices {m : ℕ} {r : Fin m → car.E}
    {s : car.ιE → car.P} {t' : MultilinearPoly car.P m}
    (hs : (s, t') ∈ car.sliceRel m r) (w : car.ιE → car.P) :
    (∑ u, w u * s u, t') ∈ car.sumcheckClaimRel m r w := by
  change _ = _
  calc ∑ u, w u * s u
      = ∑ u, ∑ y : Fin m → Fin 2,
          car.eqCoord r y u • (w u * t'.val.eval (y : Fin m → car.P)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        have hsu : s u
            = ∑ y : Fin m → Fin 2, car.eqCoord r y u • t'.val.eval (y : Fin m → car.P) := hs u
        rw [hsu, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => mul_smul_comm _ _ _
    _ = ∑ y : Fin m → Fin 2,
          (∑ u, car.eqCoord r y u • w u) * t'.val.eval (y : Fin m → car.P) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun u _ => (smul_mul_assoc _ _ _).symm
    _ = ∑ y : Fin m → Fin 2,
          car.bridge w (eqTilde r (car.boolToE y)) * t'.val.eval (y : Fin m → car.P) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [car.bridge_eqTilde]

/-! ### The Remark-5 consistency check (S6 design review F1/F2/F6-4) -/

/-- **The Remark-5 claim-consistency check** ([BRW26] Remark 5; design review F1): the phase
verifier's check of the prover-sent slices against the input claims — each claim `αᵢ` must be the
opening-basis recombination of the `i`-th packing-basis coordinates of the slices,
`αᵢ = ∑ᵤ (packBasis.repr sᵤ i) • bᵤ^E`. This uses **both** bases, which is exactly why it is
sound: `recombine_injective` (packing side) and `openingDecomposition_injective` (opening side)
pin both decompositions. `claimConsistent_of_slices` is the completeness direction (honest slices
pass), `openingClaimRel_of_claimConsistent` the soundness read-back to the anchor. -/
def claimConsistent (α : car.ιP → car.E) (s : car.ιE → car.P) : Prop :=
  ∀ i, α i = ∑ u, car.packBasis.repr (s u) i • car.openBasis u

/-- **The slice read-back identity** (the shared core of both directions of the Remark-5 check):
for honest slices of a packed `t'`, the recombination the check compares `αᵢ` against *is* the
`i`-th unpacked component's evaluation at `r`:
`∑ᵤ (packBasis.repr sᵤ i) • bᵤ^E = (unpack t')ᵢ(r)`. The proof expands the anchor evaluation over
the hypercube (`aeval_multilinear_eq_sum_eqTilde`), reads each hypercube evaluation back through
`unpack_eval_zeroOne`, and reassembles the eq-coordinates via `Basis.sum_repr` — Flock's "by the
uniqueness of the 𝔽₂-decomposition" step, in equational form.

**Hypothesis note (the logged S6 deviation):** `[IsDomain car.E]` is an accepted theorem
hypothesis — the eq-expansion of the anchor interpolates the mapped multilinear over `E` by root
counting. Both live carriers (`towerCarrier`: `E = L` a field; `decoupledFieldCarrier`:
`E = 𝔽₈`) satisfy it; generalizing to plain `CommRing E` is future work. -/
theorem aeval_unpack_of_slices [IsDomain car.E] {m : ℕ} {r : Fin m → car.E}
    {s : car.ιE → car.P} {t' : MultilinearPoly car.P m}
    (hs : (s, t') ∈ car.sliceRel m r) (i : car.ιP) :
    MvPolynomial.aeval r (car.unpack t' i).val
      = ∑ u, car.packBasis.repr (s u) i • car.openBasis u := by
  calc MvPolynomial.aeval r (car.unpack t' i).val
      = ∑ y : Fin m → Fin 2, eqTilde (y : Fin m → car.E) r
          * algebraMap B car.E ((car.unpack t' i).val.eval (y : Fin m → B)) :=
        aeval_multilinear_eq_sum_eqTilde (car.unpack t' i).property r
    _ = ∑ y : Fin m → Fin 2, ∑ u, (car.eqCoord r y u
          * car.packBasis.repr (t'.val.eval (y : Fin m → car.P)) i) • car.openBasis u := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [car.unpack_eval_zeroOne]
        have hb : car.boolToE y = (y : Fin m → car.E) := (coe_boolFun_eq_ite y).symm
        have h1 : eqTilde (y : Fin m → car.E) r = eqTilde r (car.boolToE y) := by
          rw [hb]; exact eqPolynomial_symm _ _
        rw [h1, ← car.openBasis.sum_repr (eqTilde r (car.boolToE y)), Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [smul_mul_assoc, ← Algebra.commutes, ← Algebra.smul_def, smul_smul]
        rfl
    _ = ∑ u, car.packBasis.repr (∑ y : Fin m → Fin 2,
          car.eqCoord r y u • t'.val.eval (y : Fin m → car.P)) i • car.openBasis u := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        rw [map_sum, Finsupp.finsetSum_apply]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ u, car.packBasis.repr (s u) i • car.openBasis u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← hs u]

/-- **Remark-5 check completeness** (design review F6-4): honest slices of the packed family pass
the consistency check against the honest claims — any `α` satisfying the input anchor for the
family. `[IsDomain car.E]` is inherited from the shared core `aeval_unpack_of_slices` (the logged
S6 deviation; see there). -/
theorem claimConsistent_of_slices [IsDomain car.E] {m : ℕ} {r : Fin m → car.E}
    {α : car.ιP → car.E} {Ps : car.ιP → MultilinearPoly B m} {s : car.ιE → car.P}
    (hα : ((α, r), Ps) ∈ car.openingClaimRel m)
    (hs : (s, car.packedMLE Ps) ∈ car.sliceRel m r) :
    car.claimConsistent α s := fun i => by
  have h := car.aeval_unpack_of_slices hs i
  rw [car.unpack_packedMLE] at h
  exact (hα i).trans h

/-- **Remark-5 read-back, soundness direction** (design review F2): if the claims pass the
consistency check against slices that are honest for some packed `t'`, then the input anchor
`openingClaimRel` holds for the claims against the *unpacked* family — the witness the S6
extractor returns. `[IsDomain car.E]` is inherited from the shared core `aeval_unpack_of_slices`
(the logged S6 deviation; see there). -/
theorem openingClaimRel_of_claimConsistent [IsDomain car.E] {m : ℕ} {r : Fin m → car.E}
    {α : car.ιP → car.E} {s : car.ιE → car.P} {t' : MultilinearPoly car.P m}
    (hc : car.claimConsistent α s) (hs : (s, t') ∈ car.sliceRel m r) :
    ((α, r), car.unpack t') ∈ car.openingClaimRel m :=
  fun i => (hc i).trans (car.aeval_unpack_of_slices hs i).symm

end RingSwitchCarrier

/-! ## The PCS binding interface (safety pillar 2) -/

/-- **The commitment half of a dense multilinear PCS over `P`**: oracle-statement types (the
commitment as the verifier sees it) together with the binding predicate `commitsTo` and its
**functionality law** — an oracle statement commits to *at most one* multilinear. Functionality
is the enforcement making `commitsTo` a genuine binding semantics rather than a free hook
(`commitsTo_not_top`), and it is exactly what the S6 round-by-round extraction needs to collapse
the `∃ witMid` event to the fixed claim pair fed to `BatchingStrategy.separates`. -/
structure PackedCommitment (P : Type) [CommRing P] (m : ℕ) where
  /-- Index set of the commitment's oracle statements. -/
  ιC : Type
  /-- The oracle-statement types (the commitment, as oracles the verifier may query). -/
  OStmt : ιC → Type
  /-- Oracle interfaces for the commitment oracles. -/
  Oᵢ : ∀ i, OracleInterface (OStmt i)
  -- Well-formedness: a commitment value exists. Same design move as the carrier's `Nontrivial`
  -- guards: without it, an *empty* oracle-statement type is a bona-fide instance on which
  -- `commitsTo := fun _ _ => True` is statable (functionality vacuous) and `evalRel = ∅` —
  -- a vacuous, self-punishing corner, but one that would falsify the "`True` is unstatable"
  -- guarantee (`commitsTo_ne_top`). Real commitment types are inhabited.
  [neC : Nonempty (∀ j, OStmt j)]
  /-- The binding predicate: the oracle statement commits to this multilinear. -/
  commitsTo : (∀ j, OStmt j) → MultilinearPoly P m → Prop
  /-- **Functionality**: an oracle statement commits to at most one multilinear. -/
  commitsTo_functional : ∀ {c : ∀ j, OStmt j} {p p' : MultilinearPoly P m},
    commitsTo c p → commitsTo c p' → p = p'

namespace PackedCommitment

variable {P : Type} [CommRing P] {m : ℕ}

/-- The trivial (identity) commitment: the oracle *is* the multilinear. The degenerate but
honest member of the interface — binding holds definitionally. Used as the statability witness;
real PCSs (FRI-Binius etc.) supply nontrivial oracles at S7. -/
def trivial (P : Type) [CommRing P] (m : ℕ) : PackedCommitment P m where
  ιC := Unit
  OStmt := fun _ => MultilinearPoly P m
  Oᵢ := fun _ => OracleInterface.instDefault
  commitsTo := fun c p => c () = p
  commitsTo_functional := fun h h' => h.symm.trans h'

/-- **`commitsTo` cannot be the free hook `fun _ _ => True`** (design Hole A is closed, not just
discouraged): functionality forces distinct multilinears — e.g. the constant-`0` and constant-`1`
MLEs, distinct since `P` is nontrivial — to be uncommitted-to simultaneously. Compare the legacy
`AbstractOStmtIn.initialCompatibility`, which type-admits `True`. -/
theorem commitsTo_not_top [Nontrivial P] (pc : PackedCommitment P m) (c : ∀ j, pc.OStmt j) :
    ¬ ∀ p : MultilinearPoly P m, pc.commitsTo c p := by
  intro h
  have h01 : (⟨MLE fun _ => 0, MLE_mem_restrictDegree _⟩ : MultilinearPoly P m)
      = ⟨MLE fun _ => 1, MLE_mem_restrictDegree _⟩ :=
    pc.commitsTo_functional (h _) (h _)
  have hval := congrArg
    (fun p : MultilinearPoly P m =>
      p.val.eval (((fun _ => 0) : Fin m → Fin 2) : Fin m → P)) h01
  simp only [MLE_eval_zeroOne] at hval
  exact zero_ne_one hval

/-- Function-level form of the enforcement: `commitsTo` **is not** the legacy free hook
`fun _ _ => True` — for any well-formed `PackedCommitment` (the `neC` guard supplies the
commitment value the pointwise theorem needs). This is *syntactic* inequality against the
literal hook; the semantic guarantee (no commitment accepts every polynomial) is
`commitsTo_not_top`, which `neC` keeps non-vacuous. -/
theorem commitsTo_ne_top [Nontrivial P] (pc : PackedCommitment P m) :
    pc.commitsTo ≠ fun _ _ => True := fun h =>
  pc.commitsTo_not_top (Classical.choice pc.neC) (fun p => by rw [h]; trivial)

/-- **The PCS's own anchored input relation** (what its completeness and knowledge soundness are
stated against): evaluation correctness — the legacy `MLPEvalRelation`, reused verbatim — *and*
the binding predicate `commitsTo`. This is the pillar-2 replacement of the legacy
`AbstractOStmtIn.toRelInput` (whose second conjunct is the free `initialCompatibility`). -/
def evalRel (pc : PackedCommitment P m) :
    Set (((MLPEvalStatement P m) × (∀ j, pc.OStmt j)) × (WitMLP P m)) :=
  { input | MLPEvalRelation P m pc.ιC pc.OStmt input ∧ pc.commitsTo input.1.2 input.2.t }

end PackedCommitment

/-- **A dense multilinear PCS over `P`** (design §6 irreducible obligation 2 — the one honest
trust boundary): a `PackedCommitment` together with an evaluation oracle reduction and its
security properties, *stated against the fixed anchored relation* `evalRel` — so `commitsTo`
is consumed by the structure's own completeness and knowledge-soundness fields (safety
pillar 2). Mirrors the legacy `MLIOPCS` bundle shape (kept intact for the S7 migration), with
`evalRel` replacing the free-hook relation `toRelInput`. -/
structure DenseMLPCS (P : Type) [CommRing P] (m : ℕ) extends PackedCommitment P m where
  /-- Number of interaction rounds of the evaluation protocol. -/
  numRounds : ℕ
  /-- Protocol specification of the evaluation protocol. -/
  pSpec : ProtocolSpec numRounds
  /-- Oracle interfaces for the protocol messages. -/
  Oₘ : ∀ j, OracleInterface (pSpec.Message j)
  /-- Sampleability of the verifier challenges. -/
  O_challenges : ∀ i : pSpec.ChallengeIdx, SampleableType (pSpec.Challenge i)
  /-- The evaluation protocol, as an oracle reduction from the anchored evaluation claim to
  accept/reject. -/
  oracleReduction : OracleReduction (oSpec := []ₒ)
    (StmtIn := MLPEvalStatement P m) (OStmtIn := OStmt)
    (StmtOut := Bool) (OStmtOut := fun _ : Empty => Unit)
    (WitIn := WitMLP P m) (WitOut := Unit)
    (pSpec := pSpec)
  /-- Perfect completeness w.r.t. the **fixed** anchored relation `evalRel`. -/
  perfectCompleteness : ∀ {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    OracleReduction.perfectCompleteness (oSpec := []ₒ)
      (StmtIn := MLPEvalStatement P m) (OStmtIn := OStmt)
      (StmtOut := Bool) (OStmtOut := fun _ : Empty => Unit)
      (WitIn := WitMLP P m) (WitOut := Unit) (pSpec := pSpec) (init := init) (impl := impl)
      (relIn := toPackedCommitment.evalRel)
      (relOut := acceptRejectOracleRel)
      (oracleReduction := oracleReduction)
  /-- Round-by-round knowledge error of the evaluation protocol. -/
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  /-- RBR knowledge soundness w.r.t. the **fixed** anchored relation `evalRel` — the extractor
  is obligated to produce a witness satisfying `commitsTo` (this is what makes the binding
  predicate load-bearing rather than decorative). -/
  rbrKnowledgeSoundness : ∀ {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl []ₒ (StateT σ ProbComp)},
    OracleVerifier.rbrKnowledgeSoundness
      (verifier := oracleReduction.verifier)
      (init := init) (impl := impl)
      (relIn := toPackedCommitment.evalRel)
      (relOut := acceptRejectOracleRel)
      (rbrKnowledgeError := rbrKnowledgeError)

/-! ## Sanity / testable deliverables (S5 §5.3) -/

section Sanity

-- **Non-vacuity witness** (the `Nontrivial E` guard doing its designed job): the all-`1` claims
-- on the all-`0` family are NOT in the anchor relation — `openingClaimRel` is not `univ`, so
-- proving membership carries real semantic content.
example (r : Fin 3 → decoupledToyCarrier.E) :
    ((fun _ => 1, r), fun _ => 0) ∉ decoupledToyCarrier.openingClaimRel 3 := by
  intro h
  have h0 := h ((0 : Fin 2) : decoupledToyCarrier.ιP)
  simp only [ZeroMemClass.coe_zero, map_zero] at h0
  exact one_ne_zero h0

-- INV-2: the whole relation chain typechecks on the *decoupled* `P ≠ E` carrier…
example (r : Fin 3 → decoupledToyCarrier.E) (w : decoupledToyCarrier.ιE → decoupledToyCarrier.P) :
    (Set (((decoupledToyCarrier.ιP → decoupledToyCarrier.E) × (Fin 3 → decoupledToyCarrier.E))
        × (decoupledToyCarrier.ιP → MultilinearPoly (ZMod 2) 3)))
      × Set ((decoupledToyCarrier.ιE → decoupledToyCarrier.P)
        × MultilinearPoly decoupledToyCarrier.P 3)
      × Set (decoupledToyCarrier.P × MultilinearPoly decoupledToyCarrier.P 3) :=
  ⟨decoupledToyCarrier.openingClaimRel 3,
   decoupledToyCarrier.sliceRel 3 r,
   decoupledToyCarrier.sumcheckClaimRel 3 r w⟩

-- …and on the *tower* carrier (arbitrary field extension, arbitrary rank).
example {K L ι : Type} [Field K] [Field L] [Algebra K L] [Fintype ι] (β : Basis ι K L)
    (m : ℕ) (r : Fin m → (towerCarrier β).E) (w : (towerCarrier β).ιE → (towerCarrier β).P) :
    (Set ((((towerCarrier β).ιP → (towerCarrier β).E) × (Fin m → (towerCarrier β).E))
        × ((towerCarrier β).ιP → MultilinearPoly K m)))
      × Set (((towerCarrier β).ιE → (towerCarrier β).P)
        × MultilinearPoly (towerCarrier β).P m)
      × Set ((towerCarrier β).P × MultilinearPoly (towerCarrier β).P m) :=
  ⟨(towerCarrier β).openingClaimRel m,
   (towerCarrier β).sliceRel m r,
   (towerCarrier β).sumcheckClaimRel m r w⟩

-- INV-2: the PCS interface instantiates at both carriers' packing algebras (the trivial
-- commitment; real PCSs land at S7).
example : PackedCommitment decoupledToyCarrier.P 3 := .trivial _ 3

example {K L ι : Type} [Field K] [Field L] [Algebra K L] [Fintype ι] (β : Basis ι K L) :
    PackedCommitment (towerCarrier β).P 3 := .trivial _ 3

-- The full PCS bundle is statable at any commutative ring (the S8 Hachi shape included) —
-- like `BatchingStrategy`, the vocabulary is `CommRing`-only; hypotheses live on theorems.
example : Type 1 := DenseMLPCS (ZMod 6) 3

-- INV-2: the Remark-5 check (`claimConsistent`) is *statable* with no domain hypothesis, on the
-- decoupled toy carrier (a non-domain product ring)…
example (α : decoupledToyCarrier.ιP → decoupledToyCarrier.E)
    (s : decoupledToyCarrier.ιE → decoupledToyCarrier.P) : Prop :=
  decoupledToyCarrier.claimConsistent α s

-- …and both of its directions instantiate on the *tower* carrier (`[IsDomain E]` from the field
-- structure; the projection is opaque to instance search, so it is landed by `letI`)…
example {K L ι : Type} [Field K] [Field L] [Algebra K L] [Fintype ι] (β : Basis ι K L)
    {m : ℕ} {r : Fin m → (towerCarrier β).E} {α : (towerCarrier β).ιP → (towerCarrier β).E}
    {s : (towerCarrier β).ιE → (towerCarrier β).P} {t' : MultilinearPoly (towerCarrier β).P m}
    (hc : (towerCarrier β).claimConsistent α s)
    (hs : (s, t') ∈ (towerCarrier β).sliceRel m r) :
    ((α, r), (towerCarrier β).unpack t') ∈ (towerCarrier β).openingClaimRel m :=
  letI : IsDomain (towerCarrier β).E := inferInstanceAs (IsDomain L)
  (towerCarrier β).openingClaimRel_of_claimConsistent hc hs

-- …and on the *decoupled field* carrier `P = 𝔽₄ ≠ E = 𝔽₈` (the R5 anti-overfit witness for the
-- `[IsDomain E]`-gated soundness layer): completeness — honest slices pass the check.
example {m : ℕ} {r : Fin m → decoupledFieldCarrier.E}
    {α : decoupledFieldCarrier.ιP → decoupledFieldCarrier.E}
    {Ps : decoupledFieldCarrier.ιP → MultilinearPoly (ZMod 2) m}
    {s : decoupledFieldCarrier.ιE → decoupledFieldCarrier.P}
    (hα : ((α, r), Ps) ∈ decoupledFieldCarrier.openingClaimRel m)
    (hs : (s, decoupledFieldCarrier.packedMLE Ps) ∈ decoupledFieldCarrier.sliceRel m r) :
    decoupledFieldCarrier.claimConsistent α s :=
  letI : IsDomain decoupledFieldCarrier.E := inferInstanceAs (IsDomain (GaloisField 2 3))
  decoupledFieldCarrier.claimConsistent_of_slices hα hs

-- …and the soundness read-back on the decoupled field carrier too.
example {m : ℕ} {r : Fin m → decoupledFieldCarrier.E}
    {α : decoupledFieldCarrier.ιP → decoupledFieldCarrier.E}
    {s : decoupledFieldCarrier.ιE → decoupledFieldCarrier.P}
    {t' : MultilinearPoly decoupledFieldCarrier.P m}
    (hc : decoupledFieldCarrier.claimConsistent α s)
    (hs : (s, t') ∈ decoupledFieldCarrier.sliceRel m r) :
    ((α, r), decoupledFieldCarrier.unpack t') ∈ decoupledFieldCarrier.openingClaimRel m :=
  letI : IsDomain decoupledFieldCarrier.E := inferInstanceAs (IsDomain (GaloisField 2 3))
  decoupledFieldCarrier.openingClaimRel_of_claimConsistent hc hs

end Sanity

end RingSwitching.Generic

end
