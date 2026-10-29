/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Basic
public import ArkLib.ProofSystem.RingSwitching.Packing.Multiplier
public import ArkLib.ProofSystem.RingSwitching.Packing.ClaimLayout
public import ArkLib.ProofSystem.RingSwitching.Packing.DerivedBatching
public import ArkLib.ProofSystem.RingSwitching.RoundVerifiers
public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.OracleReduction.LogicStep

/-!
# A scalar claim to a product-sumcheck claim

Let `p = ∑ᵢ βᵢ pᵢ` be the packed source, and let `x(q)` and `λᵢ(q)` describe a scalar query.
The first message decodes to component values `αᵢ`. The verifier checks
`s = ∑ᵢ λᵢ(q) αᵢ`, then samples `c` and uses the batching weights `wᵤ(c)`. It derives the target
`∑ᵤ wᵤ(c) · ∑ᵢ repr_E(αᵢ)ᵤ βᵢ` and the public multiplier whose Boolean values are
`A_c(y) = ∑ᵤ wᵤ(c) · repr_E(eq(x(q), y))ᵤ`.

The transmitted carrier is `M`; an explicit equivalence decodes it to the component family.
DP24 keeps its original tensor carrier through the column equivalence. Canonical consumers use
an identity equivalence. There is one message and one challenge, with no extra slice message.

The output is the initial product-sumcheck statement on `A_c · p`, retaining `(q,c)`, the same
commitment oracle collection and the same packed polynomial. `RingSwitch` appends product sumcheck
directly. Completeness uses only the operational batching rule and scalar reconstruction.
Round-by-round knowledge soundness uses a separation certificate and injective
coefficient transport. Equal component evaluations among compatible polynomials at each fixed query
and oracle statement suffice for the standalone head theorem. Polynomial functionality supplies
that premise as a corollary; full ring-switching security retains functionality through sumcheck.
The fixed-candidate theorem bounds the union of the head collision events for a list chosen
before the batching challenge.
-/

@[expose] public section

noncomputable section

namespace RingSwitching.Packing.Head

open OracleSpec OracleComp ProtocolSpec MvPolynomial Probability ProbabilityTheory
  CoordinateWise.ScalarRound
open scoped NNReal ENNReal

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  (layout : ClaimLayout data m)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]

variable {M : Type} (messageEquiv : M ≃ (data.ιP → data.E))

section Program
variable (rule : BatchingRule C data.ιE) (pc : PackedCommitment data.P m)

/-- The original scalar evaluation query and claimed value. -/
abbrev Input := layout.Query × data.E

/-- The original query, batching challenge and batched target at the empty prefix. -/
abbrev Output := ProductSumcheck.Statement (layout.Query × rule.Challenge) C (0 : Fin (m + 1))

/-- One component-value message followed by one batching challenge. -/
def pSpec : ProtocolSpec 2 := pSpecScalar M rule.Challenge

instance : ∀ i, OracleInterface ((pSpec (M := M) data rule).Message i) :=
  letI : OracleInterface M := OracleInterface.instDefault
  inferInstanceAs (∀ i, OracleInterface
    ((pSpecScalar M rule.Challenge).Message i))

instance : ∀ i, SampleableType ((pSpec (M := M) data rule).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => rule.sampleC

/-- Component evaluations sent by the honest prover. -/
def partials (q : layout.Query) (p : layout.Source) : data.ιP → data.E :=
  fun i => aeval (layout.point q) (layout.components p i).val

/-- The message must reconstruct the claimed scalar value under the chosen layout. -/
def check (stmt : Input data m layout) (α : data.ιP → data.E) : Prop :=
  stmt.2 = ∑ i, layout.weight stmt.1 i * α i

/-- The output is computed from the public transpose, without another prover message. -/
def nextStatement (stmt : Input data m layout) (α : data.ιP → data.E)
    (c : rule.Challenge) : Output data m layout rule :=
  ⟨(stmt.1, c), Fin.elim0, data.derivedTarget α (rule.weight c)⟩

/-- The input anchors the scalar claim to this commitment's packed source. -/
def relIn : Set (((Input data m layout) × (∀ j, pc.OStmt j)) × layout.Source) :=
  { sw | sw.1.1.2 = layout.eval sw.1.1.1 sw.2 ∧
    pc.commitsTo sw.1.2 (data.packedMLE (layout.components sw.2)) }

open scoped Classical in
/-- The multiplier polynomial and its read-once matrix evaluator. -/
def multiplier : ProductSumcheck.Multiplier (layout.Query × rule.Challenge) C m where
  polynomial ctx := data.multiplier (layout.point ctx.1) (rule.weight ctx.2)
  evaluate ctx r := data.evaluateMultiplier (layout.point ctx.1) (rule.weight ctx.2) r
  evaluate_eq ctx r := data.evaluateMultiplier_eq (layout.point ctx.1) (rule.weight ctx.2) r

/-- The output is the initial sumcheck relation on the same committed polynomial. -/
abbrev relOut := ProductSumcheck.rel (multiplier data m layout rule) pc 0

omit [IsScalarTower B data.P C] in
/-- The initial residual-sum relation is the derived-slice sumcheck claim. -/
theorem relOut_iff (stmt : Output data m layout rule) (ost : ∀ j, pc.OStmt j)
    (p : data.P⦃≤ 1⦄[X Fin m]) :
    ((stmt, ost), p) ∈ relOut data m layout rule pc ↔
      (stmt.target, p) ∈ data.sumcheckClaimRel m (layout.point stmt.ctx.1)
        (rule.weight stmt.ctx.2) ∧ pc.commitsTo ost p := by
  have hempty : stmt.challenges = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  change (stmt.target = hypercubeSum m (ProductSumcheck.productPoly
      (multiplier data m layout rule stmt.ctx) p).val 0 stmt.challenges ∧
    pc.commitsTo ost p) ↔ _
  rw [hempty, hypercubeSum_zero]
  have heval (y : Fin m → Fin 2) : aeval (y : Fin m → C) p.val =
      algebraMap data.P C (p.val.eval (y : Fin m → data.P)) := by
    simpa only [MvPolynomial.aeval_def, Function.comp_def, map_natCast] using
      (MvPolynomial.eval₂_comp (algebraMap data.P C) (y : Fin m → data.P) p.val).symm
  simp only [ProductSumcheck.productPoly_eval, heval]
  rfl

/-- Honest commitments and exact scalar claims always inhabit the input relation. -/
theorem mem_relIn_commit (honest : pc.Honest) (q : layout.Query) (p : layout.Source) :
    (((q, layout.eval q p), honest.commit (data.packedMLE (layout.components p))), p) ∈
      relIn data m layout pc := ⟨rfl, honest.commitsTo_commit _⟩

/-- The original source before the message, its packed polynomial afterwards, then the challenge. -/
def OracleState {ι : Type} (OStmt : ι → Type) : Fin 3 → Type
  | ⟨0, _⟩ => (Input data m layout × (∀ j, OStmt j)) × layout.Source
  | ⟨1, _⟩ => ((Input data m layout × (∀ j, OStmt j)) × data.P⦃≤ 1⦄[X Fin m]) ×
      (data.ιP → data.E)
  | _ => (((Input data m layout × (∀ j, OStmt j)) × data.P⦃≤ 1⦄[X Fin m]) ×
      (data.ιP → data.E)) × rule.Challenge

/-- The honest round algorithm depends only on the oracle family, independently of compatibility. -/
def proverForOracles {ι : Type} (OStmt : ι → Type) :
    OracleProver []ₒ (Input data m layout) OStmt layout.Source
    (Output data m layout rule) OStmt data.P⦃≤ 1⦄[X Fin m] (pSpec (M := M) data rule) where
  PrvState := OracleState data m layout rule OStmt
  input := id
  sendMessage
    | ⟨0, _⟩ => fun ((stmt, ost), p) => pure
      (messageEquiv.symm (partials data m layout stmt.1 p),
        (((stmt, ost), data.packedMLE (layout.components p)), partials data m layout stmt.1 p))
    | ⟨1, h⟩ => fun _ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ((((stmt, ost), p), α), c) =>
    pure ((nextStatement data m layout rule stmt α c, ost), p)

/-- The honest state family at a fixed commitment oracle interface. -/
abbrev ProverState := OracleState data m layout rule pc.OStmt

/-- Send component values while retaining the same packed polynomial and oracle collection. -/
def prover := proverForOracles data m layout messageEquiv rule pc.OStmt

open scoped Classical in
/-- Reject a failed reconstruction and otherwise return the derived batched claim. -/
def verifier : OracleVerifier []ₒ (Input data m layout) pc.OStmt
    (Output data m layout rule) pc.OStmt (pSpec (M := M) data rule) :=
  scalarRoundOracleVerifier (oSpec := []ₒ) (OStmt := pc.OStmt)
    (fun stmt z => check data m layout stmt (messageEquiv z))
    (fun stmt z c => nextStatement data m layout rule stmt (messageEquiv z) c)

/--
The reusable scalar-claim reduction, parameterized by both algebras, the message encoding and the
  batching rule.
-/
def reduction : OracleReduction []ₒ (Input data m layout) pc.OStmt layout.Source
    (Output data m layout rule) pc.OStmt data.P⦃≤ 1⦄[X Fin m] (pSpec (M := M) data rule) :=
  ⟨prover data m layout messageEquiv rule pc, verifier data m layout messageEquiv rule pc⟩

open scoped Classical in
/-- The exact guard and accepted output of the verifier. -/
def guardedForm : (verifier data m layout messageEquiv rule pc).toVerifier.GuardedForm :=
  scalarRoundOracleVerifierGuardedForm (oSpec := []ₒ) (OStmt := pc.OStmt)
    (fun stmt z => check data m layout stmt (messageEquiv z))
    (fun stmt z c => nextStatement data m layout rule stmt (messageEquiv z) c)

omit [Algebra B C] [IsScalarTower B data.P C] in
open scoped Classical in
/-- The guard is the scalar reconstruction check on the transmitted message. -/
theorem guardedForm_check (stmt : Input data m layout × (∀ j, pc.OStmt j))
    (tr : FullTranscript (pSpec (M := M) data rule)) :
    (guardedForm data m layout messageEquiv rule pc).check stmt tr =
      decide (check data m layout stmt.1 (messageEquiv (tr.messages ⟨0, rfl⟩))) := rfl

omit [Algebra B C] [IsScalarTower B data.P C] in
/-- The accepted output retains the input commitment oracle verbatim. -/
theorem guardedForm_out (stmt : Input data m layout × (∀ j, pc.OStmt j))
    (tr : FullTranscript (pSpec (M := M) data rule)) :
    (guardedForm data m layout messageEquiv rule pc).out stmt tr =
      (nextStatement data m layout rule stmt.1 (messageEquiv (tr.messages ⟨0, rfl⟩))
        (tr.challenges ⟨1, rfl⟩), stmt.2) := rfl

/-- The honest scalar check is exactly the layout's reconstruction identity. -/
theorem check_partials_of_mem_relIn {stmt : Input data m layout} {ost : ∀ j, pc.OStmt j} {p :
    layout.Source}
    (h : ((stmt, ost), p) ∈ relIn data m layout pc) :
    check data m layout stmt (partials data m layout stmt.1 p) :=
  h.1.trans (layout.reconstruct stmt.1 p)

/-- Every batching challenge gives a valid honest output on the original commitment. -/
theorem nextStatement_mem_relOut {stmt : Input data m layout} {ost : ∀ j, pc.OStmt j} {p :
    layout.Source}
    (h : ((stmt, ost), p) ∈ relIn data m layout pc) (c : rule.Challenge) :
    ((nextStatement data m layout rule stmt (partials data m layout stmt.1 p) c, ost),
      data.packedMLE (layout.components p)) ∈ relOut data m layout rule pc := by
  rw [relOut_iff]
  refine ⟨data.sumcheckClaimRel_derivedTarget_of_openingClaimRel _ _ _ _ ?_, h.2⟩
  rw [data.unpack_packedMLE]
  exact fun _ => rfl

/--
Correct component values plus the scalar check read the source witness back deterministically.
-/
theorem mem_relIn_of_check_of_openingClaimRel (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j)
    (α : data.ιP → data.E) (p : data.P⦃≤ 1⦄[X Fin m])
    (hc : check data m layout stmt α)
    (hα : ((α, layout.point stmt.1), data.unpack p) ∈ data.openingClaimRel m)
    (hcommit : pc.commitsTo ost p) :
    ((stmt, ost), layout.components.symm (data.unpack p)) ∈ relIn data m layout pc := by
  constructor
  · rw [layout.reconstruct, Equiv.apply_symm_apply]
    exact hc.trans (Finset.sum_congr rfl fun i _ => congrArg (layout.weight stmt.1 i * ·) (hα i))
  · simpa only [Equiv.apply_symm_apply, data.packedMLE_unpack] using hcommit

/-- The prover output contains no oracle queries and can be composed statefully. -/
instance : (prover data m layout messageEquiv rule pc).OutputIsPure where
  output_is_pure := ⟨fun ((((stmt, ost), p), α), c) =>
    ((nextStatement data m layout rule stmt α c, ost), p), fun _ => rfl⟩

omit [Algebra B C] [IsScalarTower B data.P C] in
/-- Exact honest execution of the two-round prover, before materializing its fresh challenge. -/
theorem prover_run (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j) (p : layout.Source) :
    (prover data m layout messageEquiv rule pc).run (stmt, ost) p = (do
      let c ← (liftM (query (spec := [(pSpec (M := M) data rule).Challenge]ₒ) ⟨⟨1, rfl⟩, ()⟩ :
        OracleComp [(pSpec (M := M) data rule).Challenge]ₒ rule.Challenge) :
        OracleComp ([]ₒ + [(pSpec (M := M) data rule).Challenge]ₒ) rule.Challenge)
      pure (FullTranscript.mk2 (pSpec := pSpec (M := M) data rule)
        (messageEquiv.symm (partials data m layout stmt.1 p)) c,
        ((nextStatement data m layout rule stmt (partials data m layout stmt.1 p) c, ost),
          data.packedMLE (layout.components p)))) := by
  have h0 : (pSpec (M := M) data rule).dir 0 = .P_to_V := rfl
  have h1 : (pSpec (M := M) data rule).dir 1 = .V_to_P := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_P_to_V 0 h0,
    Prover.processRound_of_dir_eq_V_to_P 1 h1]
  simp only [prover, proverForOracles, id_eq, pure_bind, liftM_pure, bind_pure_comp,
    LawfulApplicative.map_pure, getChallenge]
  simp only [liftM, map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro c
  change (pure
    (((default : (pSpec (M := M) data rule).Transcript 0).concat (m := 0)
        (messageEquiv.symm (partials data m layout stmt.1 p))).concat (m := 1) c,
      ((nextStatement data m layout rule stmt (partials data m layout stmt.1 p) c, ost),
        data.packedMLE (layout.components p))) :
    OracleComp ([]ₒ + [(pSpec (M := M) data rule).Challenge]ₒ) _) = _
  congr 1
  exact congrArg (fun tr => (tr,
    ((nextStatement data m layout rule stmt (partials data m layout stmt.1 p) c, ost),
      data.packedMLE (layout.components p))))
    (FullTranscript.mk2_eq_snoc_snoc (pSpec := pSpec (M := M) data rule)
      (messageEquiv.symm (partials data m layout stmt.1 p)) c).symm

/-- Perfect completeness at every initial oracle state, for every challenge sampled by the phase. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m layout messageEquiv rule pc).perfectCompleteness init impl
      (relIn data m layout pc) (relOut data m layout rule pc) := by
  classical
  let _ : ∀ j, OracleInterface ((pSpec (M := M) data rule).Challenge j) :=
    ProtocolSpec.challengeOracleInterface
  apply Reduction.perfectCompleteness_of_guarded_prover_support _
    (guardedForm data m layout messageEquiv rule pc)
  intro ⟨stmt, ost⟩ p hIn q hq
  change q ∈ support ((prover data m layout messageEquiv rule pc).run (stmt, ost) p) at hq
  rw [prover_run] at hq
  obtain ⟨c, _, hq⟩ := (mem_support_bind_iff _ _ _).mp hq
  have hq := OracleComp.eq_of_mem_support_pure _ hq
  subst q
  refine ⟨?_, ?_, ?_⟩
  · change decide (check data m layout stmt
      (messageEquiv (messageEquiv.symm (partials data m layout stmt.1 p)))) = true
    rw [Equiv.apply_symm_apply]
    exact decide_eq_true (check_partials_of_mem_relIn data m layout pc hIn)
  · change ((nextStatement data m layout rule stmt
      (messageEquiv (messageEquiv.symm (partials data m layout stmt.1 p))) c, ost),
      data.packedMLE (layout.components p)) ∈ relOut data m layout rule pc
    rw [Equiv.apply_symm_apply]
    exact nextStatement_mem_relOut data m layout rule pc hIn c
  · change (nextStatement data m layout rule stmt (partials data m layout stmt.1 p) c, ost) =
      (nextStatement data m layout rule stmt
        (messageEquiv (messageEquiv.symm (partials data m layout stmt.1 p))) c, ost)
    rw [Equiv.apply_symm_apply]

/-- The source witness before the message and the packed polynomial thereafter. -/
def WitMid : Fin 3 → Type
  | ⟨0, _⟩ => layout.Source
  | ⟨1, _⟩ => data.P⦃≤ 1⦄[X Fin m]
  | ⟨2, _⟩ => data.P⦃≤ 1⦄[X Fin m]

/-- Read back the original source through both the packing and layout equivalences. -/
def extractor : Extractor.RoundByRound []ₒ
    (StmtIn := Input data m layout × (∀ j, pc.OStmt j)) (WitIn := layout.Source)
    (WitOut := data.P⦃≤ 1⦄[X Fin m]) (pSpec := pSpec (M := M) data rule)
    (WitMid := WitMid data m layout) where
  extractIn := fun _ w => w
  extractMid i _ _ p := match i with
    | ⟨0, _⟩ => layout.components.symm (data.unpack p)
    | ⟨1, _⟩ => p
  extractOut _ _ p := p

/-- Before the fresh challenge, the sent family must equal the committed component evaluations. -/
def beforeChallenge (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j)
    (α : data.ιP → data.E) (p : data.P⦃≤ 1⦄[X Fin m]) : Prop :=
  check data m layout stmt α ∧ pc.commitsTo ost p ∧
    ((α, layout.point stmt.1), data.unpack p) ∈ data.openingClaimRel m

/-- After the challenge, retain acceptance and the derived product-sumcheck relation. -/
def afterChallenge (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j)
    (α : data.ιP → data.E) (c : rule.Challenge) (p : data.P⦃≤ 1⦄[X Fin m]) : Prop :=
  check data m layout stmt α ∧
    ((nextStatement data m layout rule stmt α c, ost), p) ∈ relOut data m layout rule pc

/-- Knowledge states retain the scalar guard, with the committed source at each round. -/
def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m layout messageEquiv rule pc).KnowledgeStateFunction init impl
      (relIn data m layout pc) (relOut data m layout rule pc) (extractor (M := M) data m layout rule
        pc) where
  toFun
    | ⟨0, _⟩ => fun stmt _ p => (stmt, p) ∈ relIn data m layout pc
    | ⟨1, _⟩ => fun stmt tr p => beforeChallenge data m layout pc stmt.1 stmt.2 (messageEquiv (tr
      0)) p
    | ⟨2, _⟩ => fun stmt tr p => afterChallenge data m layout rule pc stmt.1 stmt.2 (messageEquiv
      (tr 0)) (tr 1) p
  toFun_empty _ _ h := h
  toFun_next
    | ⟨0, _⟩ => fun _ stmt _tr α p h =>
      mem_relIn_of_check_of_openingClaimRel data m layout pc stmt.1 stmt.2 (messageEquiv α) p h.1
        h.2.2 h.2.1
    | ⟨1, _⟩ => fun hdir => nomatch hdir
  toFun_full stmt tr p h := by
    classical
    obtain ⟨hc, hrel⟩ := (guardedForm data m layout messageEquiv rule pc).check_and_of_prEvent_pos h
    exact ⟨of_decide_eq_true hc, hrel⟩

end Program

section Security
variable (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- Equal component evaluations among compatible polynomials fix the collision family before
sampling and suffice to bound the existential collision event. -/
theorem pr_exists_derivedTarget_le_of_partials_eq
    (hinj : Function.Injective (algebraMap data.P C))
    (q : layout.Query) (ost : ∀ j, pc.OStmt j) (α : data.ιP → data.E)
    (hpartials : ∀ p p' : data.P⦃≤ 1⦄[X Fin m],
      pc.commitsTo ost p → pc.commitsTo ost p' → ∀ i,
        aeval (layout.point q) (data.unpack p i).val =
          aeval (layout.point q) (data.unpack p' i).val) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ p,
      pc.commitsTo ost p ∧ ((α, layout.point q), data.unpack p) ∉ data.openingClaimRel m ∧
        (data.derivedTarget α (bat.weight c), p) ∈
          data.sumcheckClaimRel m (layout.point q) (bat.weight c)] ≤
      (bat.error : ℝ≥0∞) := by
  classical
  by_cases hex : ∃ p, pc.commitsTo ost p ∧
      ((α, layout.point q), data.unpack p) ∉ data.openingClaimRel m
  · obtain ⟨p₀, hp₀, hwrong⟩ := hex
    refine (prEvent_mono _ _ (fun c => (data.derivedTarget α (bat.weight c), p₀) ∈
      data.sumcheckClaimRel m (layout.point q) (bat.weight c)) fun c h => ?_).trans
      (data.pr_derivedTarget_of_not_openingClaimRel_le bat hinj _ _ p₀ hwrong)
    obtain ⟨p, hp, _, hsum⟩ := h
    let values : data.ιP → data.E := fun i => aeval (layout.point q) (data.unpack p i).val
    have hself : ((values, layout.point q), data.unpack p) ∈
        data.openingClaimRel m := fun _ => rfl
    have hother : ((values, layout.point q), data.unpack p₀) ∈
        data.openingClaimRel m := hpartials p p₀ hp hp₀
    have hslices : data.actualSlices (layout.point q) p = data.actualSlices (layout.point q) p₀ :=
      ((data.openingClaimRel_iff_transpose_actualSlices _ values p).mp hself).symm.trans
        ((data.openingClaimRel_iff_transpose_actualSlices _ values p₀).mp hother)
    simpa only [data.sumcheckClaimRel_iff_actualSlices, hslices] using hsum
  · rw [prEvent_eq_zero_of_forall_not _ _ fun c ⟨p, hp, hwrong, _⟩ =>
      hex ⟨p, hp, hwrong⟩]
    exact _root_.zero_le

/-- Compatible packed polynomials need only have equal component evaluations at the fixed query
for the guarded head's bad event to obey the batching bound. -/
theorem bad_event_le_of_partials_eq
    (hinj : Function.Injective (algebraMap data.P C))
    (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j) (α : data.ιP → data.E)
    (hpartials : ∀ p p' : data.P⦃≤ 1⦄[X Fin m],
      pc.commitsTo ost p → pc.commitsTo ost p' → ∀ i,
        aeval (layout.point stmt.1) (data.unpack p i).val =
          aeval (layout.point stmt.1) (data.unpack p' i).val) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ p,
      ¬ beforeChallenge data m layout pc stmt ost α p ∧
        afterChallenge data m layout bat.toBatchingRule pc stmt ost α c p] ≤
      (bat.error : ℝ≥0∞) := by
  refine (prEvent_mono _ _ _ fun c h => ?_).trans
    (pr_exists_derivedTarget_le_of_partials_eq data m layout bat pc hinj stmt.1 ost α hpartials)
  obtain ⟨p, hbefore, hc, hrel⟩ := h
  obtain ⟨hsum, hcommit⟩ := (relOut_iff data m layout bat.toBatchingRule pc _ _ p).mp hrel
  exact ⟨p, hcommit, fun hα => hbefore ⟨hc, hcommit, hα⟩, hsum⟩

/-- A fixed commitment fixes the candidate before the challenge; only a batching collision
survives. -/
theorem bad_event_le (hfunctional : pc.Functional)
    (hinj : Function.Injective (algebraMap data.P C))
    (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j) (α : data.ιP → data.E) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ p,
      ¬ beforeChallenge data m layout pc stmt ost α p ∧
        afterChallenge data m layout bat.toBatchingRule pc stmt ost α c p] ≤
      (bat.error : ℝ≥0∞) :=
  bad_event_le_of_partials_eq data m layout bat pc hinj stmt ost α
    (fun p p' hp hp' _ => by rw [hfunctional hp hp'])

/-- A finite list covering the compatible packed candidates is fixed before this challenge.
Correct candidates are excluded from the collision event; no commitment functionality is needed. -/
theorem bad_event_le_of_fixed_candidates
    (hinj : Function.Injective (algebraMap data.P C))
    (stmt : Input data m layout) (ost : ∀ j, pc.OStmt j) (α : data.ιP → data.E)
    (S : Finset data.P⦃≤ 1⦄[X Fin m])
    (hcover : ∀ p, pc.commitsTo ost p → p ∈ S) {L : ℕ} (hcard : S.card ≤ L) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ p,
      ¬ beforeChallenge data m layout pc stmt ost α p ∧
        afterChallenge data m layout bat.toBatchingRule pc stmt ost α c p] ≤
      L * (bat.error : ℝ≥0∞) := by
  refine (prEvent_mono _ _ _ fun c h => ?_).trans
    (data.pr_exists_derivedTarget_not_openingClaimRel_le bat hinj
      (layout.point stmt.1) α S hcard)
  obtain ⟨p, hbefore, hc, hrel⟩ := h
  obtain ⟨hsum, hcommit⟩ := (relOut_iff data m layout bat.toBatchingRule pc _ _ p).mp hrel
  exact ⟨p, hcover p hcommit, fun hα => hbefore ⟨hc, hcommit, hα⟩, hsum⟩

/-- The single fresh challenge incurs exactly the strategy's separation bound. -/
def rbrError (_i : (pSpec (M := M) data bat.toBatchingRule).ChallengeIdx) : ℝ≥0 := bat.error

/-- Round-by-round knowledge soundness for the head requires only equal
component evaluations among compatible polynomials at each fixed query and oracle statement. -/
theorem rbrKnowledgeSoundnessWith_of_partials_eq
    (hpartials : ∀ (q : layout.Query) (ost : ∀ j, pc.OStmt j)
      (p p' : data.P⦃≤ 1⦄[X Fin m]), pc.commitsTo ost p → pc.commitsTo ost p' → ∀ i,
        aeval (layout.point q) (data.unpack p i).val =
          aeval (layout.point q) (data.unpack p' i).val)
    (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (relIn data m layout pc) (relOut data m layout bat.toBatchingRule pc) (verifier data m layout
        messageEquiv bat.toBatchingRule pc).toVerifier
      (WitMid data m layout) (extractor (M := M) data m layout bat.toBatchingRule pc)
      (knowledgeStateFunction data m layout messageEquiv bat.toBatchingRule pc init impl) (rbrError
        data bat) := by
  classical
  refine Verifier.rbrKnowledgeSoundnessWith_of_two_message rfl rfl _ _
    fun stmt tr => ?_
  exact bad_event_le_of_partials_eq data m layout bat pc hinj stmt.1 stmt.2
    (messageEquiv (tr ⟨0, by change 0 < 1; decide⟩)) (hpartials stmt.1.1 stmt.2)

/-- Functional compatibility implies round-by-round knowledge soundness for the
concrete extractor and knowledge states. -/
theorem rbrKnowledgeSoundnessWith
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (relIn data m layout pc) (relOut data m layout bat.toBatchingRule pc) (verifier data m layout
        messageEquiv bat.toBatchingRule pc).toVerifier
      (WitMid data m layout) (extractor (M := M) data m layout bat.toBatchingRule pc)
      (knowledgeStateFunction data m layout messageEquiv bat.toBatchingRule pc init impl) (rbrError
        data bat) :=
  rbrKnowledgeSoundnessWith_of_partials_eq data m layout messageEquiv bat pc
    (fun _ _ p p' hp hp' _ => by rw [hfunctional hp hp']) hinj init impl

/-- The same concrete knowledge states and extractor support a commitment with a uniformly
bounded finite list of compatible packed polynomials. Each list depends only on the original
oracle statement, so it is fixed before the fresh batching challenge. -/
theorem rbrKnowledgeSoundnessWith_of_fixed_candidates
    (hinj : Function.Injective (algebraMap data.P C))
    (candidates : (∀ j, pc.OStmt j) → Finset data.P⦃≤ 1⦄[X Fin m])
    (hcover : ∀ ost p, pc.commitsTo ost p → p ∈ candidates ost)
    {L : ℕ} (hcard : ∀ ost, (candidates ost).card ≤ L)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (relIn data m layout pc) (relOut data m layout bat.toBatchingRule pc) (verifier data m layout
        messageEquiv bat.toBatchingRule pc).toVerifier
      (WitMid data m layout) (extractor (M := M) data m layout bat.toBatchingRule pc)
      (knowledgeStateFunction data m layout messageEquiv bat.toBatchingRule pc init impl) (fun _ =>
        L * bat.error) := by
  classical
  refine Verifier.rbrKnowledgeSoundnessWith_of_two_message rfl rfl _ _
    fun stmt tr => ?_
  rw [ENNReal.coe_mul, ENNReal.coe_natCast]
  exact bad_event_le_of_fixed_candidates data m layout bat pc hinj stmt.1 stmt.2
    (messageEquiv (tr ⟨0, by change 0 < 1; decide⟩)) (candidates stmt.2) (hcover stmt.2) (hcard
      stmt.2)

end Security

end RingSwitching.Packing.Head

end
