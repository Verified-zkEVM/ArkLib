/-
PROTOTYPE (M5 step 7): the milestone's RUNTIME DEMO — constraint 2's honest demonstration.

Everything here runs against the **library**, not against a re-inlined copy: `leftPkg` is a real
`CoordinateWise.CWSSPackage` whose `extractor` field is `CoordinateWise.SingleRound.treeExtractor`
(M5's witness-only engine) and whose `isCWSS` field is M5's retyped
`coordinateWiseSpecialSoundWith_of_mkWitness`; `tailPkg` is a synthetic zero-round closing package
certified by M5's witnessing-agnostic `coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`; and
`chain := leftPkg ▷ tailPkg` goes through the canonical `▷` dispatch, hence
`Extractor.TreeBased.append`, `AppendSplit.gluePath` and `Verifier.PureForm.append`.

What the demo shows:

  1. `chain.extractor 3 T (fun _ => none)` `#eval`s to `some 17` — a real witness, kernel-`rfl`
     checked, and `(3, 17) ∈ chain.relIn` against a concretely-defined relation. The top-level
     witnessing is the CONSTANT-`none` one, so §4.6's claim is exhibited literally: a chain closed
     by a terminal link runs as a computable function of `(stmtIn, tree)` alone. The tail's
     extractor supplies `7` at each of the two branch leaves; the single-round engine `collect`s
     them and `mkWitness` sums them onto the statement (`3 + 7 + 7`).
  2. The single-round engine **declines** rather than inventing junk: on its own tree, at a
     witnessing that answers `none` at a branch, it returns `none`.
  3. The composed seam verdict `chain.isPure.verify` runs at runtime — it is what tells the right
     factor which statement to extract at.
  4. IR gates: both M5 engines, their path/`collect` readers, both delegates,
     `CommittedScalar.package`, and the three demo packages all have executable code.

Reproduce: `lake env lean docs/plans/prototypes/CM_m5demo.lean`
Expected: `some 17`, `none`, `some 17`, `5`, fourteen axiom prints free of `sorryAx`, and fourteen
`IR PRESENT` lines with no `NO IR`.
-/
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SingleRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.CommittedScalar
import ArkLib.OracleReduction.Security.SpecialSoundness

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree CoordinateWise
open CoordinateWise.SingleRound

namespace CMM5Demo

/-! ## Part A — the ambient sampling

Nothing here is about oracles or randomness, so the oracle spec is empty and the sampling is
`pure ()`. Both are erased at codegen; they exist only to index the packages. -/

/-- The empty oracle spec. -/
abbrev Ospec : OracleSpec PEmpty := []ₒ

/-- The (vacuous) query implementation. -/
def demoImpl : QueryImpl Ospec (StateT Unit ProbComp) := fun q => nomatch q

/-- The (trivial, productive) sampling. -/
abbrev demoInit : ProbComp Unit := pure ()

/-! ## Part B — the left factor: a REAL single-round package

`r = 0`, so the fold shape has one challenge coordinate and `2 ^ 0 + 1 = 2` sibling challenge
vectors. The verifier is the statement-extending one the engine's certificate expects; its purity
is carried as data (`Verifier.PureForm`), which is what the composed extractor reads at the seam. -/

/-- The challenge alphabet. -/
abbrev Chal := Fin 2

/-- The two-round single-challenge-round wire format at `r = 0`. -/
abbrev P1 : ProtocolSpec 2 := SingleRound.pSpec ℕ Chal 0

/-- The seam statement: input statement, carrier commitment, challenge vector. -/
abbrev Mid : Type := ℕ × ℕ × (Fin (2 ^ 0) → Chal)

/-- The single round's output relation: a branch response is valid iff it is `7`. -/
def relMid : Set (Mid × ℕ) := {p | p.2 = 7}

/-- The single round's input relation: the extracted witness is the statement plus `14`. -/
def relLeft : Set (ℕ × ℕ) := {p | p.2 = p.1 + 14}

/-- The pure statement-extending verifier of the fold round. -/
def V1 : Verifier Ospec ℕ Mid P1 where
  verify := fun s tr => pure (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)

/-- Its purity **as data** — the package field composition reads at the seam. -/
def V1PureForm : V1.PureForm where
  verify := fun s tr => (s, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)
  verify_eq := fun _ _ => rfl

/-- The protocol-specific witness assembler: sum the two branch responses onto the statement. -/
def mk : ℕ → ℕ → (Fin (2 ^ 0 + 1) → (Fin (2 ^ 0) → Chal)) → (Fin (2 ^ 0 + 1) → ℕ) → ℕ :=
  fun s _v _fam resp => s + resp 0 + resp 1

/-- The engine's only protocol-specific obligation `hmk`: `relMid`-valid branch responses assemble
into a `relLeft`-witness. The star-centre hypothesis is not needed at these relations. -/
theorem mk_mem (s : ℕ) (v : ℕ) (fam : Fin (2 ^ 0 + 1) → (Fin (2 ^ 0) → Chal))
    (resp : Fin (2 ^ 0 + 1) → ℕ)
    (hbranch : ∀ j, ((s, v, fam j), resp j) ∈ relMid) (_hstar : ∃ e, StarAt fam e) :
    (s, mk s v fam resp) ∈ relLeft := by
  have h0 : resp 0 = 7 := hbranch 0
  have h1 : resp 1 = 7 := hbranch 1
  change s + resp 0 + resp 1 = s + 14
  rw [h0, h1]

/-- **The left factor.** Its `extractor` is the library's witness-only single-round engine and its
`isCWSS` is the library's retyped generic assembly — nothing is re-inlined here. -/
def leftPkg : CWSSPackage demoInit demoImpl ℕ ℕ Mid ℕ P1 where
  verifier := V1
  struct := foldStructure
  relIn := relLeft
  relOut := relMid
  isPure := V1PureForm
  extractor := SingleRound.treeExtractor mk
  isCWSS :=
    SingleRound.coordinateWiseSpecialSoundWith_of_mkWitness demoInit demoImpl V1
      (fun _ _ => rfl) relLeft relMid mk mk_mem

/-! ## Part C — the right factor: a synthetic zero-round CLOSING package

This is the miniature of §4.6's closing tail: a package with no challenge rounds, whose extractor
reads the tree (here: answers `7`) and **ignores its leaf witnessing**. Placed on the right of a
chain it is what closes the recursion — the composed extractor stops consulting the top-level
witnessing entirely. `SingleRound.treeExtractor` is by design an *open* extractor, which is why the
closing factor has to be the right one. -/

/-- The zero-round wire format. -/
abbrev P2 : ProtocolSpec 0 := !p[]

instance : IsEmpty (P2.ChallengeIdx) := ⟨fun i => Fin.elim0 i.1⟩

/-- The tail's verifier: it forwards its statement unchanged. -/
def V2 : Verifier Ospec Mid Mid P2 where
  verify := fun s _ => pure s

/-- Its purity as data. -/
def V2PureForm : V2.PureForm where
  verify := fun s _ => s
  verify_eq := fun _ _ => rfl

/-- The tail's transcript-level extraction function: it produces the opening `7` the seam relation
`relMid` demands. In a real chain this is where the terminal link's own message is read. -/
def tailE : Mid → P2.FullTranscript → ℕ := fun _ _ => 7

/-- **The right factor**, certified by M5's witnessing-agnostic no-challenge bridge. -/
def tailPkg : CWSSPackage demoInit demoImpl Mid ℕ Mid Unit P2 where
  verifier := V2
  struct := CWSSStructure.ofIsEmpty
  relIn := relMid
  relOut := Set.univ
  isPure := V2PureForm
  extractor := fun stmtIn tree _ => some (tailE stmtIn tree.onlyPath.fullTranscript)
  isCWSS := Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx demoInit demoImpl
    CWSSStructure.ofIsEmpty V2 relMid Set.univ tailE (fun _ _ _ => rfl)

/-! ## Part D — the chain, and the runtime -/

/-- The composed package, through the canonical `▷`. -/
def chain := leftPkg ▷ tailPkg

/-- Two sibling challenge vectors at the composite spec: the constant `0` and the constant `1`. -/
def challengesT : Fin ((CWSSStructure.toShape chain.struct).arity ⟨1, rfl⟩) →
    (P1 ++ₚ P2).Challenge ⟨1, rfl⟩ :=
  fun j _ => if j.val = 0 then (0 : Chal) else 1

/-- The round-0 message of the composite tree. -/
def msgT : (P1 ++ₚ P2).Message ⟨0, rfl⟩ := (5 : ℕ)

/-- A concrete star tree of the composed protocol: one message node, one challenge node with the
two siblings, leaves below. -/
def T : ChallengeTree (P1 ++ₚ P2) (CWSSStructure.toShape chain.struct).arity 0 :=
  .msgNode 0 rfl msgT (.chalNode 1 rfl challengesT (fun _ => .leaf))

-- The chain extracts at the CONSTANT-`none` top-level witnessing: the tail closes the recursion,
-- so the composed extractor is a function of `(stmtIn, tree)` alone. `3 + 7 + 7 = 17`.
#eval chain.extractor 3 T (fun _ => none)  -- expect: some 17

/-- Kernel-checked, not merely `#eval`-checked: the composed extraction is definitional. -/
theorem chain_eval : chain.extractor 3 T (fun _ => none) = some 17 := rfl

/-- **Constraint 2, exhibited**: on a concrete tree the composed extractor really returns a witness
of the concretely-defined input relation — this is the notion's own conclusion, at real data. -/
theorem chain_extracts :
    ∃ w, chain.extractor 3 T (fun _ => none) = some w ∧ (3, w) ∈ chain.relIn :=
  ⟨17, rfl, rfl⟩

/-! ### The engine declines rather than inventing junk

On the left factor's own tree — where the extractor is genuinely *open* — a witnessing that
answers `none` makes extraction fail, instead of returning a default witness. -/

/-- The left factor's own star tree, built with the library's `tree2`. -/
def T1 : ChallengeTree P1 (CWSSStructure.toShape leftPkg.struct).arity 0 :=
  tree2 5 (fun j _ => if j.val = 0 then (0 : Chal) else 1)

#eval leftPkg.extractor 3 T1 (fun _ => none)     -- expect: none
#eval leftPkg.extractor 3 T1 (fun _ => some 7)   -- expect: some 17

/-- Kernel-checked: declining leaves decline the extraction. -/
theorem left_none : leftPkg.extractor 3 T1 (fun _ => none) = none := rfl

/-- Kernel-checked: the open engine reads its witnessing at the two branch paths. -/
theorem left_some : leftPkg.extractor 3 T1 (fun _ => some 7) = some 17 := rfl

/-! ### The composed seam verdict runs

`PureForm.append`'s composed verdict is what tells the right factor which statement to extract at.
It is data, on the executable path — not a `Prop` laundered through choice. -/

/-- The composite transcript of one of the tree's leaves, selected by the library's computable
`somePath` (whose positivity side condition is discharged by M3's `toShape_arity_pos`). -/
def trT : (P1 ++ₚ P2).FullTranscript :=
  (ChallengeTree.somePath (CWSSStructure.toShape_arity_pos chain.struct) T).fullTranscript

#eval (chain.isPure.verify 3 trT).2.1  -- expect: 5, the message the seam verdict reads

/-- Kernel-checked: the seam verdict reads the transcript at runtime. -/
theorem seam_reads_message : (chain.isPure.verify 3 trT).2.1 = 5 := rfl

end CMM5Demo

/-! ## Axiom audit -/

#print axioms CMM5Demo.chain_eval
#print axioms CMM5Demo.chain_extracts
#print axioms CMM5Demo.left_none
#print axioms CMM5Demo.left_some
#print axioms CMM5Demo.seam_reads_message
#print axioms CoordinateWise.SingleRound.treeExtractor
#print axioms CoordinateWise.ScalarRound.treeExtractorScalar
#print axioms CoordinateWise.SingleRound.coordinateWiseSpecialSoundWith_of_mkWitness
#print axioms CoordinateWise.SingleRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness
#print axioms CoordinateWise.ScalarRound.coordinateWiseSpecialSoundWith_of_mkWitness_scalar
#print axioms CoordinateWise.ScalarRound.coordinateWiseSpecialSoundWithEscape_of_mkWitness_scalar
#print axioms CoordinateWise.CommittedScalar.coordinateWiseSpecialSoundWithEscape
#print axioms Verifier.treeSpecialSoundWith_of_isEmpty_challengeIdx
#print axioms Verifier.specialSound.old_of_new

/-! ## IR gate: M5's engines, delegates, packages and this demo all compile to executable code -/

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for nm in [``CoordinateWise.SingleRound.treeExtractor,
             ``CoordinateWise.SingleRound.branchPathOf,
             ``CoordinateWise.SingleRound.collect,
             ``CoordinateWise.ScalarRound.treeExtractorScalar,
             ``CoordinateWise.ScalarRound.branchPathOf,
             ``CoordinateWise.ScalarRound.readFam,
             ``CoordinateWise.CommittedScalar.treeExtractor,
             ``CoordinateWise.CommittedScalar.package,
             ``CoordinateWise.CommittedScalar.verifierPureForm,
             ``CMM5Demo.leftPkg, ``CMM5Demo.tailPkg, ``CMM5Demo.chain,
             ``CMM5Demo.T, ``CMM5Demo.T1] do
    match Lean.IR.findEnvDecl env nm with
    | some _ => Lean.logInfo m!"IR PRESENT: {nm}"
    | none   => Lean.logError m!"NO IR (noncomputable): {nm}"

/-! ### The decisive probes (§9 note 1): outside any `noncomputable section` -/

def probeSingleRoundTreeExtractor := @CoordinateWise.SingleRound.treeExtractor
def probeScalarTreeExtractor := @CoordinateWise.ScalarRound.treeExtractorScalar
def probeCommittedScalarTreeExtractor := @CoordinateWise.CommittedScalar.treeExtractor
def probeCommittedScalarPackage := @CoordinateWise.CommittedScalar.package
