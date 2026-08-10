# Plan: computable CWSS extractors

**Status: ready to execute.** The design is fully prototyped and green (see
[`prototypes/`](prototypes/README.md)); no `ArkLib/` file has changed yet.

**Goal.** Remove every noncomputable extractor definition in the CWSS stack. Two independent
roots cause all of them:

1. **The notion**: the extractor type forces classical inversion of the output relation (four
   engine definitions, §2). Fixed by the witness-only leaf-witnessing design (§4) —
   Milestones M0 and M2–M9.
2. **The presentation layer**: `Lift.Presentation` carries Mathlib-`Polynomial` data fields,
   which have no computable values at all, denying IR to `liftPackage`, `openCore`,
   `openingChain` (§5). Fixed by the CompPoly rewrite — Milestone M1 (independent of the
   notion work, scheduled first so no later gate is conditional on it).

Audience: the implementing agent. Every load-bearing claim carries a `file:line` citation or a
reproduction command; §6 records which claims are machine-checked; §8 records every resolved
decision. **The core theorems are already proved in the vendored prototypes — the work is
transcription, not proof search.**

---

## 1. Execution contract

Read this first; it is the contract for how the rest of the document is consumed.

1. **All decisions are made.** §8 is a *resolved*-decisions table. Do not reopen D1–D9; if an
   abort criterion fires, stop and re-report — do not redesign inline. In particular, do not
   "simplify" the notion: §4.2 records the machine-checked kills of both simpler-looking
   variants (the ∀-over-outputs form, G0, and the reachability-free form, G3), and E1–E7 are
   the regression gates that catch a re-weakening.
2. **Navigate by declaration name, never by line number.** Line citations will drift;
   `rg -n "def treeExtractor" ArkLib/` is the ground truth. When M0 lands the baseline commit,
   record its SHA here: `BASELINE = 329ff98d554bb459892ff5dea99e8c0c6363cea0`.
3. **The prototypes are the design, vendored.** The four `CM_*` files in
   [`prototypes/`](prototypes/README.md) hold every machine-checked result in §6 and are the
   transcription source for M1–M6. Check one with
   `lake env lean docs/plans/prototypes/<file>.lean` (pass = no `sorryAx` in the output). These
   commands reproduce against `BASELINE`. Step 2a renames the repo declarations the prototypes
   import, so from 2a onward either re-run them checked out at `BASELINE`, or apply the same
   mechanical rename inside `docs/plans/prototypes/*.lean` (cheap, keeps the evidence live).
   Pick one and note the choice at 2a. `CM_presentation.lean` is exempt: it imports only the
   lattice/CompPoly layer, which no milestone renames.
4. **Green means two gates, not one.** Every landing milestone ends with (a) `lake build` green
   and (b) an **IR gate** on the definitions it was supposed to make computable (§9 note 3 has
   the template). A green build alone never certifies computability: nine files in the blast
   radius open a `noncomputable section`, which silently swallows codegen failures.
5. **At least one commit per lettered step** (2a, 2b, …), so any breakage bisects. New files
   need `git add` **before** `./scripts/update-lib.sh` regenerates `ArkLib.lean` (it only sees
   tracked files), and `ArkLib.lean` is generated — never hand-edit it.
6. **Context economy.** Each milestone names the files to read before editing. Do not re-derive
   the design from the codebase; §4 plus the prototypes are the design. Everything lands in
   **one PR**, executed as **one milestone per session** under §7's session protocol; §11 is
   the cross-session ledger.
7. **The `*Classical` layer is scaffolding, not a second API — it gets deleted.** Step 2a's
   rename exists only to keep `lake build` green while consumers migrate. Every renamed name is
   re-introduced computable under its canonical spelling (2b/3a/4a/4b, M5), and **M9 deletes the
   `Classical` twins outright** (§4.5, D3). The end state is **one** layer under today's names.
   While the shim is up: never write a new definition, theorem or package against a `*Classical`
   name — anything left there M9 has to delete, or its deletion gate fails.

## 2. The problem

Four definitions recover a per-branch prover response by classically inverting the output
relation:

| Definition | Location |
| --- | --- |
| `CoordinateWise.SingleRound.treeExtractor` | `ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:356` |
| `CoordinateWise.ScalarRound.treeExtractorScalar` | `ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:336` |
| `ReduceClaim.treeExtractor` | `ArkLib/ProofSystem/Component/ReduceClaim.lean:187` |
| `ReduceClaim.oracleTreeExtractor` | `ArkLib/ProofSystem/Component/ReduceClaim.lean:407` |

Each has the shape

```lean
if h : ∃ w, ((stmtIn, v, fam j), w) ∈ relOut then h.choose else Classical.ofNonempty
```

This is not a syntactic accident. The extractor type is

```lean
def Extractor.TreeBased (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → ChallengeTree pSpec arity 0 → WitIn
```

and a `ChallengeTree` carries only messages and challenges — never an output witness. The
information the extractor needs is **absent from its input**, information-theoretically: a total
computable function of `(stmtIn, tree)` landing in a cryptographic `relIn` would invert the
ambient commitments (§4.6). So the extra input cannot be eliminated, only typed and homed well.

The literature already names it. A reduction-of-knowledge extractor (Kothapalli–Parno) takes the
tree of accepting transcripts **and witnesses for the output claims at its leaves**, and returns
an input witness. In a chain, those leaf witnesses are exactly what the *downstream* reduction
extracts from each leaf's suffix tree. That observation is the whole design.

**Population.** The noncomputable count over the CWSS surface is **20**: definitions whose type
mentions `Extractor.TreeBased` or one of the four package structures carrying an `extractor`
field. Narrowly extractor-typed ones number **6**: the four roots above plus two pure delegates
(`CoordinateWise.CommittedScalar.treeExtractor`, `CommittedScalar.lean:198`, and
`RingSwitching.Lift.treeExtractor`, `Lift/Reduction.lean:174`). The other 14 are packages and
chains, 12 of them under Hachi (inventoried by name in M8). A fifth classical root independent
of the notion — `ChallengeTree.onlyTranscript` (`NoChallenge.lean:78`) — is removed by M0.

**Prerequisites already in the working tree** (uncommitted at `HEAD = 03c95a9b`; M0 commits
them): the tree-split rework (all 16 `*Package.append*` operators computable) and the removal of
`noncomputable` markers from sorried extractors, so the marker set now tracks computability debt
only.

## 3. Constraints

Fixed by the repository owner; a design violating any of these is out of scope.

1. **Option-valued.** The extractor returns `Option WitIn`, declining where it cannot extract;
   the security statement asserts it returns `some w` with `(stmtIn, w) ∈ relIn` on good input.
2. **Real extraction.** On a concrete accepting tree the extractor must `#eval` to a witness
   that actually satisfies `relIn`. A design where callers pass a junk recovery function and
   correctness stays hypothesis-bound is rejected. §4.6 explains the one place this constraint
   is read relative to a terminal link (Hachi's deliberately-open recursion seam).
3. **Stay close to the current design.** Package fields may move, but names like `isCWSS` stay,
   the existing notions stay recognisable, and additive changes are preferred over new bundled
   types. Two deliberate deviations (D7): `Extractor.TreeBased` stays a bare function but
   widens (a `WitOut` index and a witnessing argument; extractors are *witness-only* — statement
   attribution is the verifier's, never the extractor's), and the packages' `isPure`/`isGuarded`
   fields become data-carrying (`PureForm`/`GuardedForm`) so composition can read the verdict
   function without choice.
4. **No finiteness.** Witness types are infinite (lattice and polynomial vectors); any design
   resting on `Fintype`/decidable search over `WitOut` is dead on arrival.

## 4. The design: witness-only extractors and leaf witnessings

The guiding principle: **the extractor extracts a witness, full stop; attributing output
statements to leaves is the verifier's business.** Everything below follows from typing that
principle and gating the alternatives.

### 4.1 The two objects and the notion

Transcribe from `CM_gates.lean`; every declaration below is machine-checked there under the
same name, modulo the `CM.` prototype namespace.

```lean
-- ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean

/-- One candidate output witness per root-to-leaf transcript — the "output witnesses" input of a
reduction-of-knowledge extractor. In a chain it is produced by the downstream extractor; at the
top of a security statement, classically from `IsAccepting` (`canonWitnesses`). -/
def ChallengeTree.LeafWitnesses (tree : ChallengeTree pSpec arity 0) (WitOut : Type) : Type :=
  ChallengeTree.LeafPath tree → Option WitOut

/-- The statements the verifier can output on `(stmtIn, tr)` under the fixed sampling. -/
def Verifier.Outputs (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn) (tr : pSpec.FullTranscript) :
    Set StmtOut :=
  {out | some out ∈ support (do (simulateQ impl (V.run stmtIn tr)).run' (← init))}

/-- A witnessing is **valid** when it answers at every leaf and each answer certifies, in
`relOut`, some statement the verifier can actually output on that leaf's transcript. The
reachability condition is the notion's honesty discipline, carried in the premise; the
∃ over reachable outputs — not ∀ — is what keeps the premise satisfiable at randomized
verifiers (G0/G1). -/
def LeafWitnesses.IsValid (init) (impl) (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relOut : Set (StmtOut × WitOut)) (stmtIn : StmtIn) (o : tree.LeafWitnesses WitOut) : Prop :=
  ∀ p, ∃ w, o p = some w ∧
    ∃ out ∈ V.Outputs init impl stmtIn p.fullTranscript, (out, w) ∈ relOut

/-- The tree extractor — TODAY's bare-function shape, with the witnessing input added and the
`WitOut` index widened. No `StmtOut` index: output statements enter only through the notion's
validity premise. The extractor extracts; it does not attribute statements. -/
def Extractor.TreeBased (StmtIn WitIn WitOut : Type) {n : ℕ}
    (pSpec : ProtocolSpec n) (arity : pSpec.ChallengeIdx → ℕ) : Type :=
  StmtIn → (tree : ChallengeTree pSpec arity 0) → tree.LeafWitnesses WitOut → Option WitIn

/-- Replaces `Verifier.treeSpecialSoundWith` — the parameter list is TODAY'S; only `Ext`'s type
indices widen. ONE clause: no honesty conjunct, because there is no claim map to be honest
about. -/
def Verifier.treeSpecialSoundWith (S : ChallengeTreeShape pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (Ext : Extractor.TreeBased StmtIn WitIn WitOut pSpec S.arity) : Prop :=
  ∀ stmtIn tree, tree.IsStructured S →
    tree.IsAccepting init impl verifier stmtIn relOut.language →
      ∀ o, o.IsValid init impl verifier relOut stmtIn →
        ∃ w, Ext stmtIn tree o = some w ∧ (stmtIn, w) ∈ relIn
```

The escape twin keeps identical premises with conclusion
`esc stmtIn tree ∨ (∀ o valid → extraction succeeds)` — today's disjunction shape exactly — at
an **unchanged** `ChallengeTree.EscapeEvent`. `coordinateWiseSpecialSoundWith` keeps its name,
shape and `isCWSS` field name; only the extractor's type index changes.

**Purity as data.** Statement attribution belongs to the verifier. On the proof side it is
already there (`Verifier.IsPure`, `IsGuardedWith`); what composition additionally needs is the
verdict function as *data* — extracting it from the `IsPure` existential costs
`Classical.choice`. `PureForm` is that data: the bundled form of `IsPure`, playing the role
`Equiv` plays for `Bijective`. All machine-checked in `CM_gates.lean`:

```lean
-- ArkLib/OracleReduction/Basic.lean, beside Verifier.IsPure (:748)
/-- A purity witness carrying its verdict function as data. -/
structure Verifier.PureForm (V : Verifier oSpec StmtIn StmtOut pSpec) where
  verify : StmtIn → pSpec.FullTranscript → StmtOut
  verify_eq : ∀ stmtIn tr, V.verify stmtIn tr = pure (verify stmtIn tr)

theorem PureForm.isPure (P : V.PureForm) : V.IsPure               -- forgetful
noncomputable def pureFormOfIsPure (V) [V.IsPure] : V.PureForm    -- shim-only; choice

-- ArkLib/OracleReduction/Composition/Sequential/IsPure.lean, beside IsPure.append
/-- Purity data composes computably — transcript-level, no path machinery. -/
def PureForm.append (P₁ : V₁.PureForm) (P₂ : V₂.PureForm) : (V₁.append V₂).PureForm where
  verify := fun stmt tr => P₂.verify (P₁.verify stmt tr.fst) tr.snd
  verify_eq := …  -- IsPure.append's proof, minus the choice destructuring

-- ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean
/-- The bundled `IsGuardedWith` (mirror of `PureForm`). -/
structure Verifier.GuardedForm (V) where
  check : StmtIn → pSpec.FullTranscript → Bool
  out   : StmtIn → pSpec.FullTranscript → StmtOut
  verify_eq : V.IsGuardedWith check out

def PureForm.toGuardedForm (P : V.PureForm) : V.GuardedForm       -- data form of of_isPure
```

The classical closers, all in `CM_gates.lean`:

```lean
/-- The witnessing `IsAccepting` already guarantees: per leaf, a chosen `relOut`-witness at a
chosen reachable statement. Classical; lives in proofs and the top-level closer, erased at
codegen. -/
noncomputable def canonWitnesses (init) (impl) (V) (relOut) (stmtIn) :
    tree.LeafWitnesses WitOut :=
  fun p => if h : ∃ w, ∃ out ∈ V.Outputs init impl stmtIn p.fullTranscript, (out, w) ∈ relOut
    then some h.choose else none

/-- Valid on every accepting tree (`outputs_nonempty_of_isAccepting` +
`mem_language_of_mem_outputs`). The premise is never an obstruction. -/
theorem canonWitnesses_isValid (hacc : tree.IsAccepting init impl V stmtIn relOut.language) :
    (canonWitnesses init impl V relOut stmtIn).IsValid init impl V relOut stmtIn

/-- The unconditioned classical statement, recovered. Needs `[Inhabited WitIn]` and nothing
else — no purity hypothesis. -/
theorem old_of_new [Inhabited WitIn] … :
    treeSpecialSoundWith … Ext → ∀ stmtIn tree, tree.IsStructured S →
      tree.IsAccepting init impl V stmtIn relOut.language →
      (stmtIn, (Ext stmtIn tree (canonWitnesses init impl V relOut stmtIn)).getD default) ∈ relIn

/-- **The pure-case collapse**: at a pure verifier with a productive sampling, validity IS
per-verdict witnessing — the statements are pinned by the verdict function, not carried by the
witnessing. Engine certificates consume `→` (their `hpure` pins the statements); composition
proofs produce validity with `←`. -/
theorem isValid_iff_pure (hV : ∀ s t, V.verify s t = pure (verify s t))
    (hinit : (support init).Nonempty) :
    o.IsValid init impl V relOut stmtIn ↔
      ∀ p, ∃ w, o p = some w ∧ (verify stmtIn p.fullTranscript, w) ∈ relOut
```

### 4.2 Why this shape is load-bearing

Three typing choices carry the notion; each is pinned by machine-checked gates on the fixtures
in `CM_gates.lean`.

**The ∃ over reachable outputs — not ∀.** Requiring one witness per leaf to serve *every*
reachable statement makes the premise unsatisfiable at any randomized verifier with two
separated outputs, so the notion becomes vacuously provable at the constant-`none` extractor
with `relIn = ∅` — on data where the classical notion is refutable (G0 + companion). The
adopted `IsValid` demands each witness certify *some* reachable statement: on the very fixture
that kills the ∀-form, a valid ∃-form witnessing exists (G1), and non-vacuity holds in its
strongest form — with `relIn = ∅` the notion is refutable for **every** extractor (G2). The
two variants differ by one quantifier; the gates pin the right one.

**Reachability inside `IsValid` is the notion's honesty.** Validity *demands* reachability of
whatever statement each witness certifies, so trusting a witness at a statement the verifier
cannot output is unrepresentable — a witnessing citing only unreachable statements is not a
witnessing of the tree at all. The condition has teeth in both directions (G3, the
`reachable_sound`/`free_refuted` pair): on the same sound data with the same forwarding engine,
the adopted notion is provable while the reachability-free variant is refuted — junk witnesses
at unreachable statements are exactly what it excludes. And it costs the premise nothing:
`canonWitnesses` is valid on every accepting tree (G5), so the top-level closer never blocks
(`old_of_new`, E8).

**The intermediate statement's named home is the verifier.** In `append`, something must tell
the composition operator which statement to run `E₂` at, and extracting `verify₁` from the
`IsPure` existential costs `choice` — so the verdict function must be named as data. Its
semantic home is the verifier: `PureForm.verify`, a data field of the package's purity witness
(§4.1), which composition reads. (Storing a statement map in the *extractor* instead would
solve the same problem at the cost of crossing responsibilities — D7 records the rejection.)
At a pure verifier, validity collapses to exactly per-verdict witnessing (`isValid_iff_pure`),
which is why the engine certificates need TODAY's `hpure` hypotheses and no more.

### 4.3 Composition

Transcribe from `CM_append.lean` (path glue, operator, all four theorems, and the guarded
seam lemmas). The composed **extract** threads witnessings through the seam with
`AppendSplit.gluePath` — since extractors attribute no statements, nothing ever *un-glues* a
path, and the glue is the only dependent-index machinery composition needs:

```lean
-- TranscriptTree/Composition.lean — new, machine-checked in CM_append.lean Part A:
--   LeafPath.embedRight, SplitData.gluePath (+ transcript specs), LeafPath.transport,
--   AppendSplit.gluePath + fullTranscript_gluePath

/-- The intermediate statement is `verify₁` — the LEFT VERIFIER's verdict function, passed as
data; packages read it off their `PureForm`/`GuardedForm` field. -/
def Extractor.TreeBased.append (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : TreeBased Stmt₁ Wit₁ Wit₂ pSpec₁ arity₁)
    (E₂ : TreeBased Stmt₂ Wit₂ Wit₃ pSpec₂ arity₂) :
    TreeBased Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) (appendArity arity₁ arity₂) :=
  fun stmt tree o =>
    E₁ stmt tree.appendSplit.fst fun p₁ =>
      E₂ (verify₁ stmt p₁.fullTranscript) (tree.appendSplit.sndAt p₁)
        fun p₂ => o (AppendSplit.gluePath tree p₁ p₂)
```

`CWSSPackage.append`'s `extractor` field (`Package.lean:106`) becomes
`L₁.extractor.append L₁.isPure.verify L₂.extractor` (guarded packages pass
`L₁.isGuarded.out`). In a ≥3-fold chain the left factor's seam function is
`PureForm.append`'s composed verdict — a transcript-level read (`tr.fst`/`tr.snd` plus the two
verdicts), which **runs at runtime** and is IR-gated (the 3-fold demo, E19); nothing traverses
paths besides `gluePath`.

All four composition theorems are proved in `CM_append.lean` under these names:

| Theorem | Left factor | Conclusion | Corresponds to |
| --- | --- | --- | --- |
| `append_treeSpecialSoundWith` | pure (`verify₁`, `hV₁`) | plain | `CWSS/Composition.lean:327` |
| `append_treeSpecialSoundWithEscape` | pure | escape, at today's `EscapeEvent.append` | `CWSS/Composition.lean:379` |
| `append_treeSpecialSoundWith_guardedLeft` | guarded (`check₁`, `out₁`, `harity₂`) | plain | `Guarded.lean:161` |
| `append_treeSpecialSoundWithEscape_guardedLeft` | guarded | escape | **`Guarded.lean:141` — today's `sorry`** |

The proofs share one skeleton whose key move dissolves an apparent circularity between the two
certificates: prefix acceptance is established by running the **right** certificate at
`canonWitnesses` first (`key0`), which licenses the **left** certificate. The two
witnessing-validity transfers ride `fullTranscript_gluePath` + `append_run_outputs` (validity
is `Outputs`-relative, so left purity rewrites the output set directly — §9 note 6's `key`
pattern in transcript position), and the prefix witnessing's reachability comes from
`pure_verdict_mem_outputs` + `support_init_nonempty_of_accepting` at the prefix tree's own
acceptance. The escape twins route the disjunction with a case split on "does the right factor
escape anywhere" before the plain skeleton. For guarded left factors, `hcheck` (every prefix
guard passes on an accepting tree, learned from one `somePath` suffix leaf) comes first, the
reachability lemma is the guarded analogue `guarded_verdict_mem_outputs` (verdict reachable
*when the check passes*), and the rest is identical — which is why the escape × guarded case
falls to the same skeleton.

### 4.4 What does and does not change around the notion

- **The `IsPure`/`IsGuarded` *classes* survive; the *package fields* become their data forms.**
  The classes and every existing instance stay (other layers use them; `PureForm.isPure`
  forgets back). The four packages retype `isPure : verifier.IsPure` to
  `isPure : verifier.PureForm` and `isGuarded : verifier.IsGuarded` to
  `isGuarded : verifier.GuardedForm` — same field names, now data-carrying; this is the ONE
  package-field change the design makes, and it is what lets the composed `extractor` and
  `esc` fields read `verify₁` computably. The append *theorems* keep taking `(verify₁, hV₁)`
  exactly as at `CWSS/Composition.lean:332`. The suffix verifier's reachable outputs and the
  composite's coincide only through `verify₁`, via `Verifier.append_run_pure_left` and
  `append_run_outputs` (E16). `GuardedForm.append`'s data half
  (composed check/out) is a plain definition; its `verify_eq` proof obligation is exactly
  today's sorried `IsGuarded.append` (`Guarded.lean:113`) — the sorry moves, the census count
  does not.
- **The escape layer freezes byte-for-byte** (D4, machine-checked): `ChallengeTree.EscapeEvent`,
  the `verify₁`-indexed `EscapeEvent.append`, `SingleRound.escEvent` and `escEventScalar*` are
  untouched; both escape appends are proved at today's `EscapeEvent.append` literally (E13,
  E15). The event's `verify₁` index is natural here: package appends feed it
  `L₁.isPure.verify` instead of laundering `L₁.isPure.is_pure.choose` (`Escape.lean`). Price:
  escape events cannot mention recovered witnesses, so `SingleRound.escEvent` keeps its
  `∃ resp` and gains no tightness.
- **`ChallengeTree`, `LeafPath`, `IsStructured`, `transcripts`, `IsAccepting`** — all unchanged.
  A `LeafWitnesses` is a plain function off `LeafPath`; nothing is bundled into the tree (D1).
- **The four package structures keep their field lists** — `verifier`, `struct`, `relIn`,
  `relOut`, `isPure`/`isGuarded`, `esc`, `extractor`, `isCWSS` — with `extractor` at the
  widened bare-function type (`WitOut` index; no `StmtOut`), `isPure`/`isGuarded` at the data
  forms (first bullet), and `isCWSS` meaning the new notion.
- **Hachi's witness assembly.** `quadEvalMkWitness` and `buildWitness`
  (`QuadEval/Soundness.lean:221-275`) already take a total per-branch `resp` as data and use it
  materially. They need no change; the engines feed them via `collect` (an `Option`-traverse,
  `CM_enginecerts.lean`).
- **The classical choice is relocated, not removed.** It reappears inside `canonWitnesses`
  (now also choosing the reachable statement, not just the witness), acting on the existential
  `IsAccepting` already carries, and is erased at codegen.

### 4.5 The migration shim (D3)

The refactor lands **always-green**: at every commit, `lake build` over all 324 `ArkLib.lean`
imports passes. The mechanism:

- **Rename first (2a).** One mechanical commit suffixes the outgoing layer with `Classical`.
  The complete list:

  | Renamed | To |
  | --- | --- |
  | `Extractor.TreeBased` | `Extractor.TreeBasedClassical` |
  | `Verifier.{treeSpecialSoundWith, treeSpecialSoundWithEscape, treeSpecialSound, treeSpecialSoundEscape}` | same + `Classical` |
  | `Verifier.{coordinateWiseSpecialSoundWith, coordinateWiseSpecialSoundWithEscape, coordinateWiseSpecialSound, coordinateWiseSpecialSoundEscape, specialSound}` | same + `Classical` |
  | the `OracleVerifier` mirrors of all of the above | same + `Classical` |
  | the forgetful/transport lemmas `toCWSS`, `toEscape`, `toTreeSpecialSound`, `*_iff_exists`, `*_congr`, `mono`, `withEscape`, `*_false_iff` | same + `Classical` |
  | `CoordinateWise.{CWSSPackage, GCWSSPackage, EscapeCWSSPackage, EscapeGCWSSPackage}` | same + `Classical`, with their 16 appends, `toGuarded` and `toEscape` |
  | **the certificate-*producing* theorems** — `Verifier.append_treeSpecialSoundWith`, `append_treeSpecialSoundWithEscape`, the four `append_coordinateWiseSpecialSound*` (`Verifier` + `OracleVerifier`), both `append_coordinateWiseSpecialSound{With,WithEscape}_of_guardedLeft`, the three `*_of_isEmpty_challengeIdx` (`NoChallenge.lean:107, 122, 151`), and `SingleRound`/`ScalarRound`'s `*_of_mkWitness*` | same + `Classical` |

  A pure rename; everything still compiles, and every canonical name is re-introduced at the new
  types in 2b/3a/4a/4b or M5. Names **not** renamed because they do not change: `ChallengeTree`
  machinery, `EscapeEvent` + `escEvent*`, `IsPure`/`IsGuarded`, `CWSSStructure`/shapes. Blast
  radius: 41 files
  (`rg -l 'TreeBased|treeSpecialSound|coordinateWiseSpecialSound|CWSSPackage|GCWSSPackage' ArkLib/`).

  **Why the last row is load-bearing.** A certificate-producing theorem is retyped one step
  before its consumers migrate: 4a retypes the append theorems whose only consumers are the four
  package `append` certificates (`Package.lean:112`, `Guarded.lean:257`, `Escape.lean:115`,
  `Escape.lean:189`), which 4b keeps on the `*Classical` names; M5 step 4 retypes the
  `NoChallenge` bridges whose consumers (`CheckClaim.lean:314`, `SendClaim.lean:156`,
  `ReduceClaim.lean:206, :431`, `SendWitness.lean:158, :419`) migrate in M6; M5 step 1 retypes
  `SingleRound`'s `*_of_mkWitness*`, consumed by Hachi's `QuadEval/Soundness.lean` until M8.
  Renaming these gives every straggler a working certificate source — exactly what keeps
  `lake build` green across the gaps.
- **New layer lands under the canonical names**, additively, in `Security/**` — legal because
  the import DAG cooperates: `Security/**` never imports `ProofSystem`/`Commitments` (verified).
- **`ofClassical` is the bridge, already proved** (`CM_gates.lean`: `ofClassical` +
  `new_of_old`). At the extractor level it is a *computability-preserving* one-liner —
  `fun s t _ => some (E s t)` — instance-free (no `[Nonempty StmtOut]`), no `init/impl/V`
  argument, IR whenever `E` has IR (gated in the prototype). The one shim cost sits at the
  *package* level: lifting a `*Classical` package's Prop-`isPure` to the canonical `PureForm`
  field goes through `pureFormOfIsPure` (choice), so lifted packages are noncomputable.
- **`▷` carries two dispatch tables for the duration.** 2a renames the existing 16-entry
  `univAppendFn` table's literals so it dispatches the `*Classical` packages (renamed, not
  deleted: the canonical packages do not exist until 4b). 4b adds a **second** 16-entry table
  over the canonical packages; `packageKindOf` (`Escape.lean:380`) already reads the head
  constant but returns only a `Name`, so it widens to `Expr → TermElabM (Name × Expr)`,
  returning the `ofClassical`-wrapped factor for the four `*Classical` kinds; the `▷` elaborator
  body (`Escape.lean:391-400`) then elaborates the wrapped expression (no instance synthesis
  needed — the wrapper is instance-free) and falls through to the `*Classical` table if
  it cannot. M9 deletes the `*Classical` table and the lift cases, leaving one table again.
- **The shim never buys computability by itself**: `ofClassical E` of a noncomputable `E` is
  still noncomputable, and a lifted *package* is noncomputable regardless (`pureFormOfIsPure`),
  so the per-milestone IR gates are what actually track the goal. Once every consumer is
  migrated (M5–M8), the `Classical` twins have no consumers and **M9 deletes them** (including
  `pureFormOfIsPure` if it has no organic uses by then — grep at M9), leaving one layer, under
  today's names, computable.

### 4.6 Hachi's open recursion seam

**`openingChain`'s open end is the recursion loop, not a defect.** Its last link
(`handoffPackage`, `TraceHandoff.lean:222-231`) has `relOut := relIn Φ' …`, the *next*
iteration's QuadEval input relation, **by design**: one iteration reduces `relPolyEval` to a
parameter-shifted copy of the row-2 entry relation, and iteration `i+1` is the same chain
re-instantiated at `Φ'`, re-entering at `quadEvalPackage` (`Hachi/Composition.lean:307-309`).
The intended eventual shape: (1) one composed CWSS package for a **single iteration** — today's
`openingChain`; (2) a second package that iterates it and closes the loop by appending a
"prover sends witness" tail (`Hachi/Composition.lean:415-417` already names it). That tail's
extractor is a transcript read (computable via M0's `onlyPath`), so it needs no leaf witnesses
and bootstraps the whole stack: each iteration's extractor consumes the leaf witnesses the next
iteration's extractor produces. Formalizing (2) is future work outside this plan's scope;
nothing here blocks it. The M5 exit-gate demo (open engine `▷` closing tail) is exactly this
shape in miniature.

**The impossibility fact is per *open* link — the rationale for `LeafWitnesses` (D7), not a
residual limitation.** A single link's tree does not contain its output witness, and for
QuadEval's `relIn` this is cryptographic: a total computable function of `(stmtIn, tree)`
*alone* landing in it (`QuadEval/Reduction.lean:373`) would invert the Ajtai commitments. It
costs the *closed* composition nothing: there the witness is in the tree (the tail's one
message), the tail's extractor reads it while ignoring its witnessing input, and the composed
`extract` consults the top-level witnessing only through its rightmost factor — so the closed
chain runs as a computable function of `(stmtIn, tree)` alone with a constant witnessing
plugged in at the top. An open chain cannot be "closed" by feeding it nothing: at the empty
witnessing the certificate's premise simply fails (E6) — nothing is claimed, nothing is lied
about. That is what D1's "closed relative to a terminal link" means.

**`handoffExtractor` stays `sorry`, but is closer than it looks.** Its specification is "pull
an output opening back through ψ". ψ is real (`psi`,
`Data/Lattices/CyclotomicRing/Subfield/Packing.lean:126`, proved bijective at
`Subfield/Bijectivity.lean:34`); what is missing is a **named computable inverse** — `psiInv`
does not exist in `ArkLib/`, and one obtained from `psi_bijective` is noncomputable. Ordinary
work on existing foundations; out of scope — do not let M8 wander into it.

**Also unchanged:** relations stay `Set`-valued and `esc` still launders purity through
`isPure.is_pure.choose`. Both are `Prop`-level and erased at codegen (E25).

## 5. The second root: the presentation layer

`Lift.Presentation` carries two `Type`-valued data fields over Mathlib's `Polynomial`
(`Lift/Presentation.lean:84-86`), which is `Finsupp`-backed and has **no computable values at
all** — `def t0 : Polynomial (ZMod 5) := 0` fails codegen. The presentation is a **kept
argument** of `Lift.package`/`Lift.treeExtractor` (`Lift/Reduction.lean:117`): even after
the notion work (M2–M8), `P` is consumed only through `Prop`s, but Lean never erases a
`Type`-valued binder, so
`Lift.package (cyclotomicPresentation Φ) …` (`Hachi/RingSwitch/Reduction.lean:219`) denies IR
to `liftPackage → openCore → openingChain` forever. `cyclotomicPresentation`
(`Hachi/RingSwitch/Reduction.lean:101`) is the **only** noncomputable constant left in any CWSS
extractor's transitive value graph once the notion work lands (verified two independent ways).
E32 vendors the failure as a compiling negative control next to the passing rewrite.

The same `Polynomial` reaches the witness: `LiftedWitness.ρ : Fin n → Polynomial R`
(`Lift/Reduction.lean:80`). Not an IR blocker (extractors forward witnesses), but a
**constructibility** barrier: at the old type no concrete `LiftedWitness`, hence no concrete
leaf witnessing and no runtime demo, can exist on the lift/sumcheck segment.

**The fix (D8, D9): computable data, `toPoly` laws.** Not an adapter — the structure is
rewritten in the repo's own `CyclotomicModulus`/`IsCyclotomic` idiom (which `Presentation`'s
docstring already claims to mirror):

```lean
structure Presentation (R S : Type*) [CommRing R] [CommRing S] where
  modulus : CPolynomial R          -- was: Polynomial R
  rep     : S → CPolynomial R      -- was: S → Polynomial R

class IsPresentation (P : Presentation R S) : Prop where
  monic               : P.modulus.toPoly.Monic
  natDegree_rep_lt    : ∀ s, (P.rep s).toPoly.natDegree < P.modulus.toPoly.natDegree
  rep_injective       : Function.Injective (fun s => (P.rep s).toPoly)
  modulus_dvd_rep_add : ∀ a b, P.modulus.toPoly ∣
    (P.rep (a + b)).toPoly - ((P.rep a).toPoly + (P.rep b).toPoly)
  modulus_dvd_rep_mul : ∀ a b, P.modulus.toPoly ∣
    (P.rep (a * b)).toPoly - (P.rep a).toPoly * (P.rep b).toPoly
```

The principle: **data lives in the computable carrier; the laws are the Mathlib semantics of
that data, via `toPoly`; the proof engine never leaves `Polynomial`-land.** Consequences, all
machine-checked (E30–E33):

- The engine transcribes under the mechanical rename `P.modulus ↦ P.modulus.toPoly`,
  `P.rep x ↦ (P.rep x).toPoly` — every proof verbatim, because they treat these as opaque
  `Polynomial` terms and never unfold the fields (E30).
- The cyclotomic instance becomes two projections — `{ modulus := Φ.φ, rep := fun a => a.1 }` —
  because the Hachi data was computable all along; the old structure *forced* it through
  `toPoly`. Its laws are discharged by the same QuotientLift lemmas as today, verbatim (E32).
- `rep_injective` is stated at the semantics (`toPoly ∘ rep`) because that is what the engine
  consumes and what `val_toPoly_injective` provides; injectivity of `P.rep` follows.
- `LiftedWitness.ρ : Fin n → CPolynomial R`, `hρ` `toPoly`-stated (D9). Concrete witnesses now
  construct and `#eval`; `recover` consumes `hρ` with zero bridging (E31, E33). The complete
  `w.ρ`/`P.rep` read census outside the two Lift files is ONE site:
  `ZeroCheck/Constraints.lean:175` gains `.toPoly`; everything else in `Hachi/**` uses
  `LiftedWitness` purely as a type index (verified by grep).
- Stays `noncomputable` **by design**: `rowSum`, `evalAt` — `Polynomial`-valued spec objects
  reachable only through `Prop`s. Not debt; their docstrings say so after M1 step 1.
- Untouched: `QuotientLift.lean`, `Rq`/`CyclotomicModulus` (already the target idiom), the CWSS
  notion layer (M1 is orthogonal to the notion work, M2–M8), `exists_rowSum_eq_of_mulVec_eq`.

## 6. Evidence

The four prototype files are vendored in [`prototypes/`](prototypes/README.md), all green. Each
row names the prototype declaration that checks it; rows marked *repo* cite the repo instead.

| # | Claim | How checked |
| --- | --- | --- |
| E1 | The ∀-over-outputs variant is vacuous at a randomized verifier (provable at constant-`none`, `relIn = ∅`) — the regression gate against re-weakening | `CM_gates.lean`, `unclaimed_vacuous` (G0) |
| E2 | The classical notion is refutable on that same data, for every extractor — the ∀-variant is strictly weaker | `CM_gates.lean`, `classical_refutable` |
| E3 | At that same two-output verifier, a valid ∃-form witnessing EXISTS — the premise is satisfiable exactly where the ∀-form collapses | `CM_gates.lean`, `exists_valid_witnessing` (G1) |
| E4 | The notion is refutable at `relIn = ∅` for EVERY extractor — non-vacuity in strongest form | `CM_gates.lean`, `not_vacuous` (G2) |
| E5 | Reachability inside `IsValid` is load-bearing: the same forwarding engine on the same sound data satisfies the adopted notion and refutes the reachability-free variant | `CM_gates.lean`, `reachable_sound` / `free_refuted` (G3) |
| E6 | The constant-`none` witnessing is invalid whenever a leaf exists — no chain closes on nothing | `CM_gates.lean`, `isValid_none_false` (G4) |
| E7 | `canonWitnesses` is valid on every accepting tree; bridge `IsAccepting ⟹ Outputs ⊆ relOut.language`, support-based | `CM_gates.lean`, `canonWitnesses_isValid` (G5), `mem_language_of_mem_outputs` |
| E8 | Two-way classical bridge: `old_of_new` needs `[Inhabited WitIn]`, no purity; `new_of_old` = `ofClassical`'s certificate, and `ofClassical` is a computability-preserving one-liner — instance-free, no `init/impl/V` argument, IR-gated | `CM_gates.lean`, `old_of_new`, `new_of_old`, `ofClassical` + IR gate |
| E9 | The structural output-statement readers live on the verifier as `PureForm.verify` data (they are the existing verify functions / `IsPure` instance bodies); the engines attribute no statements and their certificates pin statements via `hpure` | *repo*: component verifier defs; consumed in E27/E28's certificates |
| E10 | Leaf-path glue: `AppendSplit.gluePath` + `fullTranscript_gluePath` — the ONLY path machinery composition needs (nothing ever un-glues a path) | `CM_append.lean` Part A |
| E11 | `somePath` — a computable leaf path of any positive-arity tree (the guarded appends' probe), with IR | `CM_append.lean` Part E + IR gate |
| E12 | Composition, plain (pure left) | `CM_append.lean`, `append_treeSpecialSoundWith` |
| E13 | Composition, escape (pure left) at today's UNCHANGED `EscapeEvent.append` | `CM_append.lean`, `append_treeSpecialSoundWithEscape` |
| E14 | Composition, guarded left (with `harity₂`) | `CM_append.lean`, `append_treeSpecialSoundWith_guardedLeft` |
| E15 | Composition, escape × guarded left — `Guarded.lean:141`'s statement in FULL generality | `CM_append.lean`, `append_treeSpecialSoundWithEscape_guardedLeft` |
| E16 | Purity still required for composition; the output-set bridges `append_run_outputs` and the guarded analogues (`append_run_guardedLeft`, `append_run_outputs_guardedLeft`, `outputs_guarded_subsingleton`, `guarded_accepting_of_mem`, `guarded_verdict_mem_outputs`) | `CM_append.lean` Parts C and E |
| E17 | `ReduceClaim` engine is computable and **classical-free** (`[propext, Quot.sound]`), with a FULL CWSS certificate. The *certificate* legitimately depends on `Classical.choice` (via Mathlib's `probEvent_eq_one_iff`); only the extractor is choice-free and IR-gated | `CM_enginecerts.lean`, `CMEngines.rcTreeExtractor`, `rc_coordinateWiseSpecialSoundWith` |
| E18 | `SingleRound` engine definitions: `branchPathOf`, `collect`, `CMSR.treeExtractor` — all with IR; no inverse path readers, no path classification (validity is consumed at `branchPathOf`-paths only) | `CM_enginecerts.lean` Part C |
| E19 | Runtime: 2-fold chain `#eval`s to `some 11`, 3-fold chain to `some 211` — `verify₁`, `gluePath`, and (3-fold) the composed seam function (`PureForm.append`'s data, transcript split at runtime) all on the executable path, kernel-`rfl`-checked; declining leaves decline the chain | `CM_append.lean` Part F (`CMDemo`: `chain_eval`, `chain₃_eval`, `chain_none`) |
| E20 | Arity-0 degeneracy: at `arity i = 0` the statement is unprovable rather than vacuous; CWSS shapes give `arity ≥ 1`; the classical notion degenerates identically | `CM_gates.lean`, `isAccepting_of_no_transcripts`, `fullTranscripts_eq_nil_of_arity_zero` |
| E21 | Path↔transcript bridge in both directions | *repo*: `mem_fullTranscripts` (`TranscriptTree/Basic.lean:211`), `exists_of_mem_fullTranscripts` (`:234`) |
| E22 | Nothing consumes an extractor's output yet (no SS→KS bridge; `Rewinding.run` commented out) — no caller constrains the extractor's shape | *repo*: grep; `Rewinding.lean:55` |
| E23 | Extractors are applied beyond the four package fields: ~11 theorem conclusions (`Guarded.lean:154, 170`; `CWSS/Composition.lean:337, 391, 444, 466, 507, 535`; `NoChallenge.lean:116, 131, 162`) and two `SendWitness` statements (`:157, :418`) | *repo*: statement sites M2–M6 must touch |
| E24 | `onlyPath` — computable replacement for the `onlyTranscript` choice root — with IR | `CM_gates.lean` + `CM_enginecerts.lean` (inlined + IR-gated in both) |
| E25 | Codegen calibration: `Prop`/`Set`-valued fields are erased and never block `#eval` — a package failing an IR gate is always a data field's fault | `CM_gates.lean`, `CMCalibration` |
| E26 | The transports (`treeSpecialSoundWith_congr`, `treeSpecialSoundWithEscape.mono`, `treeSpecialSoundWithEscape_congr`) at the single `HEq`: `subst` at the shape homogenizes before the `HEq` is consumed; `mono` never inspects the extractor | `CM_gates.lean`, the three transport theorems |
| E27 | `SingleRound` certificates in full — plain + escape `*_of_mkWitness*` at the named witness-only engine, TODAY's `hpure`/`hmk`, UNCHANGED `escEvent`, `[Nonempty WitOut]` dropped; validity consumed via `isValid_iff_pure` at `hpure`; `fullTranscript_branchPathOf` by bare `rfl`; escape disjunction decided before seeing `o` | `CM_enginecerts.lean` Part C |
| E28 | `ScalarRound` transplant (`ℓ = 1, k`): witness-only engine with IR, no classical inversion, no `[Nonempty WitOut]`; both certificates at unchanged `escEventScalar`, `hmk` at `Function.Injective fam` via `injective_of_nodeOk` | `CM_enginecerts.lean` Part D |
| E29 | Real-engine runtime demo: `CMSR.treeExtractor` on a concrete star tree `#eval`s to `some 21`; missing leaf witness yields `none`, not junk; kernel-`rfl`-checked | `CM_enginecerts.lean` Part E |
| E30 | The computable presentation (§5): structures + `toPoly` laws; the ENTIRE `Lift/Presentation.lean` proof engine transcribes mechanically, every proof verbatim, no new typeclass assumptions | `CM_presentation.lean` Parts A–B |
| E31 | Retyped `LiftedWitness`, `checkAt`, `relLin`, full `recover` at the computable structures, proofs verbatim | `CM_presentation.lean` Part C |
| E32 | `cyclotomicPresentation := { modulus := Φ.φ, rep := fun a => a.1 }` is a plain computable `def`; `isPresentation_cyclotomic` discharged from the SAME QuotientLift lemmas verbatim; the `liftPackage`-shaped application has IR, the Mathlib-typed one has NO IR (negative control) | `CM_presentation.lean` Parts D–E |
| E33 | Presentation runtime: concrete modulus, `Rq` element, `LiftedWitness` all construct and `#eval`; package-shaped extraction returns `some 2`. Caveat: `Array`-backed *values* are not kernel-`decide`-able (`Array`/`USize` internals) — design gates around it | `CM_presentation.lean` Part F |
| E34 | Purity as data: `PureForm`/`GuardedForm`, forgetful maps, `PureForm.toGuardedForm`, and computable `PureForm.append` (transcript-level, IR-gated); plus the reachability producers `pure_verdict_mem_outputs`, `support_init_nonempty_of_accepting` | `CM_gates.lean` (`appendedPF` IR gate); consumed throughout `CM_append.lean` |
| E35 | The pure-case collapse: at a pure verifier with productive sampling, `IsValid` ⟺ per-verdict witnessing — engine certificates consume `→`, composition proofs produce with `←` | `CM_gates.lean`, `isValid_iff_pure` |

Reproduce (pass = `#print axioms` output free of `sorryAx`; `CM_gates` also prints `some 42`,
`some 5`, `some 4` and five `IR PRESENT` lines; `CM_append` prints `some 11`, `some 211` and
ten `IR PRESENT` lines — `SplitData.gluePath`/`AppendSplit.gluePath`/`somePath` among them;
`CM_enginecerts` prints `some 21`, `none` and seven `IR PRESENT` lines; `CM_presentation`
prints `2, 3, 5, 2, 2, some 2`, six `IR PRESENT` lines and one `NO IR AS EXPECTED`):

```bash
lake env lean docs/plans/prototypes/CM_gates.lean        # E1–E8, E20, E24–E26, E34, E35
lake env lean docs/plans/prototypes/CM_append.lean       # E10–E16, E19
lake env lean docs/plans/prototypes/CM_enginecerts.lean  # E17, E18, E24, E27–E29
lake env lean docs/plans/prototypes/CM_presentation.lean # E30–E33
```

Step 2b re-lands the gate theorems as a permanent in-library regression file
(`TranscriptTree/NonVacuity.lean`); the prototypes remain the vendored evidence.

## 7. Milestones

Ten milestones, each a 5–13 h unit with its own exit gate. The cuts and the order are chosen
so that every milestone is one reviewable theme: the core notion work is cut at commit
boundaries into three like-sized milestones (M2–M4); Hachi is cut into an additive
preparation (M7) and the retype (M8); and the presentation layer sits first (M1) — nothing
else depends on it, but M8's hardest IR gates cannot pass without it, so landing it up front
keeps every later gate unconditional.

| # | Milestone | Size | Waits on |
| --- | --- | --- | --- |
| M0 | Baseline, audit, and `onlyPath` | 5–8 h | — |
| M1 | The computable presentation layer (independent of the notion work) | 8–12 h | M0 |
| M2 | The rename and the generic notion (steps 2a–2b) | 9–13 h | M0 |
| M3 | CWSS notion and path glue (steps 3a–3b) | 5–7 h | M2 |
| M4 | Composition and packages (steps 4a–4b) | 8–10 h | M3 |
| M5 | `Security/**` consumers, core engines, runtime demo | 5–8 h | M4 |
| M6 | Components and the `Lift` marker sweep | 9–13 h | M1, M5 |
| M7 | Hachi purity data (additive) | 5–8 h | M4 |
| M8 | Hachi retype and computability sweep | 9–12 h | M1, M6, M7 |
| M9 | Shim removal, validation, docs | 6–8 h | M2–M8 |

The **Waits on** column is the mandatory ordering, not a full serialization: M1's session may
be slotted anywhere among M2–M4's, and M7's anywhere among M5–M6's.

Rules:

- **Everything lands in-repo on the single PR branch, additively, green at every commit** —
  the shim (§4.5) makes that legal. Two ordering exceptions, both self-contained changes that
  complete before the notion work starts: M0 step 3 and M1.
- **Abort means stop and re-report** — do not fix forward, do not redesign inline. Every
  milestone carries an abort criterion; "over budget" means more than 2× the milestone's upper
  hour figure. Hour figures are sizing, not deadlines.
- **Every landing milestone ends with an IR gate, not just a green build.** Nine files in the
  blast radius open a `noncomputable section` (`Package`, `CWSS/Composition`, `Guarded`,
  `CWSS/Basic:135`, `CommittedScalar`, `NoChallenge`, `Escape`, `SpecialSoundness`,
  `Implications:22`); inside one, a definition pulling in `Classical.choice` compiles with no
  error. Gate each milestone with the IR-gate template (§9 note 3) over its targets, and delete
  each `noncomputable section` as its file comes clean.
- **Transcription discipline.** When a step says "transcribe from `CM_x`", copy the prototype's
  statement and proof and adapt namespaces/imports — do not re-derive. If a transcription does
  not go through as stated, that is a signal (the repo moved, or the adaptation touched
  something load-bearing): re-check against the prototype before improvising.

### Session protocol (one milestone = one session)

Each milestone is sized for a single focused session. A session executing milestone MX:

1. **Loads exactly:** §1 (the contract), this protocol, MX's own section, MX's *Read first*
   list, and the §9 notes MX cites — nothing else from this document. Do not read other
   milestones; do not re-derive the design (§1 rule 6). M0 is the one exception: it reads the
   whole plan, because it records the baseline the rest navigates by.
2. **Verifies entry before editing:** every milestone in MX's *Waits on* row (the §7 table) is
   **green in §11**, and MX's *Entry probe* passes. The probe is a cheap belt-and-suspenders
   check; §11 is authoritative. If either fails, stop and report — do not start.
3. **Confirms the ground is green:** working tree on `tr/computable-extractors`, `lake build`
   green before the first edit (cold clone: `lake exe cache get` first). Feedback cycles are
   dominated by build time, not editing — plan the session around that.
4. **Commits per lettered/numbered step** (§1 rule 5). Commits are the checkpoints: if context
   runs low mid-milestone, record `in progress (through step …)` in §11 and stop at the last
   green commit; a follow-up session resumes there. Never leave uncommitted work at session
   end.
5. **Closes by gating:** run the exit gate, paste its *actual output* (grep hits, `IR PRESENT`
   lines, axiom prints) into §11, set the row to green, and commit the plan-file update. Then
   stop — never start the next milestone in the same session.
6. **On abort:** record the trigger and the exact state in §11, set the row to
   `aborted (<trigger>)`, and stop. Do not fix forward (§7 rules).

### M0 — baseline, audit, and `onlyPath` (2–3 h + 3–5 h for step 3)

*Read first: this file (in full — the M0 session records the baseline everything else
navigates by); `docs/skills/make-computable.md`.*

*Entry probe:* `git status --short` shows §2's uncommitted prerequisites (the tree-split
rework and marker removals) and `docs/plans/`; nothing else is assumed.

1. **Commit the working tree.** The tree-split rework, the marker removal, `docs/plans/` and
   the vendored prototypes are uncommitted. Commit them (logical pieces or one baseline commit)
   and **record the SHA in §1 rule 2**.
2. **Re-confirm the inventory** with the inventory probe (§9 note 2). Expected: 20
   noncomputable definitions, 6 narrowly extractor-typed. Notes:
   - `CoordinateWise.CommittedScalar.treeExtractor` and `RingSwitching.Lift.treeExtractor` are
     **delegates, not engines** — retype only.
   - `ProtocolSpec.ChallengeTree.onlyTranscript` (`NoChallenge.lean:78`, body
     `(fullTranscripts_eq_singleton tree).choose`) is a genuine fifth classical root,
     independent of the notion change — step 3 removes it.
   - **`SendWitness` defines no extractor.** `fun _ tree => tree.onlyTranscript 0` appears only
     inline inside two theorem *statements* (`SendWitness.lean:157, 418`); the file has one
     message and zero *challenge* rounds. It needs no extractor work beyond retyping those two
     statements.
3. **The `onlyPath` step (D6: land it first).** A computable `ChallengeTree.onlyPath`
   plus witnessing-agnostic no-challenge bridges. `onlyPath` is vendored and IR-checked (E24) —
   transcribe it. Restate the three `NoChallenge` bridges every zero-challenge component routes
   through (`Verifier.treeSpecialSoundWith_of_isEmpty_challengeIdx:107`,
   `Verifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx:122`, and the same-named
   `OracleVerifier` mirror at `:151` — disambiguate by namespace). **Then delete
   `onlyTranscript` itself in the same step**: after the three bridges and the two `SendWitness`
   statements move to `onlyPath`, `onlyTranscript` and `onlyTranscript_mem` (`:83`) have zero
   consumers (verified census). Deleting the definition — not just its uses — is what removes
   the root: it carries no `Classical` suffix, so M9's cleanup grep cannot see it. Delete
   `NoChallenge.lean`'s `noncomputable section` (`:33`) in the same commit if the file then
   compiles without it.

- **Exit gate (steps 1–2):** baseline SHA recorded; inventory list in hand;
  `./scripts/validate.sh` green on the committed baseline.
- **Exit gate (step 3):** `./scripts/validate.sh` green over all 324 imports; IR gate on
  `ChallengeTree.onlyPath`; `SendWitness.lean:157` and `:418` updated in the same commit (they
  apply the very bridges step 3 restates, so they go red otherwise); and
  `rg -w onlyTranscript ArkLib/` returns nothing.
- **Abort if** the three `NoChallenge` bridges cannot be restated witnessing-agnostically
  without touching a consumer beyond those two `SendWitness` statements.

### M1 — the computable presentation layer (8–12 h; independent of the notion work)

*Read first: §5; `prototypes/CM_presentation.lean`; `Lift/Presentation.lean`,
`Lift/Reduction.lean`, `Hachi/RingSwitch/Reduction.lean`,
`Data/Lattices/CyclotomicRing/QuotientLift.lean`.*

*Entry probe (M0 landed):* §1 rule 2's `BASELINE` is filled in, and
`rg -w onlyTranscript ArkLib/` returns nothing.

Scheduling-independent of the notion work: it touches no CWSS notion and no name the 2a rename
touches, so it may land any time after M0 — including between M2–M4's sessions. It sits first
because M8's exit gate on `liftPackage`/`openCore`/`openingChain` cannot pass without it (§5);
landing it up front makes every later IR gate unconditional. The marker sweep it enables on
`Lift.treeExtractor`/`Lift.package` happens in M6, once those definitions' other root
(ScalarRound's engine, M5) is also gone.

1. **`Lift/Presentation.lean` — the structures and the engine.** Transcribe
   `CM_presentation.lean` Parts A–B over the existing file: `Presentation`'s fields become
   `modulus : CPolynomial R`, `rep : S → CPolynomial R` (names, binders unchanged; no new
   typeclass assumptions); `IsPresentation`'s five laws restate via `toPoly` (E30); every
   engine theorem renames `P.modulus ↦ P.modulus.toPoly`, `P.rep x ↦ (P.rep x).toPoly`, proofs
   verbatim. `rowSum` stays a `noncomputable` `Polynomial`-valued spec object **by design**
   (reachable only through `Prop`s) — say so in its docstring so a later marker sweep does not
   misread it. Gate: green; the file's theorem list is unchanged (name-for-name).
2. **`Lift/Reduction.lean` — witness and protocol layer.** Transcribe Part C:
   `LiftedWitness.ρ : Fin n → CPolynomial R` with `hρ` `toPoly`-stated (D9); `checkAt` gains
   `.toPoly` at its three read sites; `recover`, `escEvent`, `treeExtractor`, `package`,
   `coordinateWiseSpecialSoundWithEscape` keep their statements with `hd` in the
   `P.modulus.toPoly.natDegree = d` spelling (E31). The prover's `computeW` is type-level only.
   Gate: green.
3. **The Hachi instantiation.** `Hachi/RingSwitch/Reduction.lean`: `cyclotomicPresentation`
   becomes `{ modulus := Φ.φ, rep := fun a => a.1 }` and **drops its `noncomputable` marker**
   (E32); `cyclotomicPresentation_modulus_natDegree` keeps its statement (same proposition —
   the old `modulus` was literally `Φ.φ.toPoly`); `isPresentation_cyclotomic` keeps its proofs
   verbatim; `RhoShort` is textually unchanged (its `(ρ i).coeff k` now reads the computable
   `CPolynomial.coeff`); `liftShort`, `liftCheckAt`, `relLift` unchanged. The one `w.ρ` read
   site outside this file, `ZeroCheck/Constraints.lean:175`'s `evalAt φF α (w.ρ i)`, gains
   `.toPoly`. Gate: green; IR gate on `cyclotomicPresentation`.

- **Exit gate:** `./scripts/validate.sh` green; IR gates per step; `recover` and the engine
  theorems are **proved, not sorried** (`#print axioms` on `recover` free of `sorryAx` — the
  laws restatement must not silently weaken the algebra); the E33 runtime demo reproduces
  (concrete `LiftedWitness` constructs and `#eval`s). The per-declaration markers on
  `Lift.treeExtractor`/`Lift.package` stay for now — their other root falls in M5, and M6
  removes them.
- **Abort if** an engine proof does not survive the mechanical rename (E30 says all of them do
  — a failure means the repo's `Presentation.lean` diverged from the vendored copy; re-check
  against the prototype before improvising), or if a `Hachi/**` site outside step 3's census
  turns out to *read* `w.ρ` or `P.rep`/`P.modulus` in a data position — that is a new root,
  re-report. Do **not** use `decide` on `Array`-backed values in any gate or demo (E33): kernel
  reduction sticks on `Array`/`USize` internals; `#eval` + IR gates are the instruments.

### M2 — the rename and the generic notion (9–13 h)

*Read first: §4.1–§4.2 (the notion and why its shape is load-bearing), §4.5;
`TranscriptTree/Basic.lean`, `CWSS/Basic.lean`, `Escape.lean` (the rename's blast radius —
§4.5's grep enumerates the rest); `prototypes/CM_gates.lean` (the transcription source);
§9 note 8.*

*Entry probe (M0 landed):* §1 rule 2's `BASELINE` is filled in, and
`rg -w onlyTranscript ArkLib/` returns nothing.

One commit per step; `lake build` green after each. The ∃-form rule below governs 2b as well
as M3/M4's retypes — read it before starting.

**The ∃-form rule (from D2 = Inherit):** the existential/forgetful declarations
(`treeSpecialSound`, `treeSpecialSoundEscape`, `coordinateWiseSpecialSound`,
`coordinateWiseSpecialSoundEscape`, `toTreeSpecialSound` / `toCWSS` / `toEscape` /
`_iff_exists` — `TranscriptTree/Basic.lean:373-394, 438-453`; `CWSS/Basic.lean:244-264,
284-298, 366-381, 398-417`) are **retyped, not deleted** (in 2b and 3a respectively):
`Verifier.specialSound` is *defined as* the ∃-form at `distinctShape`, so the ∃-form must
survive. What changes is their role: the eight append theorems (`CWSS/Composition.lean:335,
389, 441, 463, 504, 532`; `Guarded.lean:151, 167`) move their right factor
**existential → named**, because the composed extractor must *contain* `E₂` (4a's job).

- **2a — the rename commit (mechanical; 3–4 h).** Suffix the outgoing layer with `Classical` per
  §4.5's table (which includes `Verifier.specialSound:68-71` and
  `OracleVerifier.specialSound:89-93` in `Security/SpecialSoundness.lean`), and rename — do not
  delete — the `▷` table's constant literals (`Escape.lean:360-377`). Include *tactic-block*
  occurrences (`unfold Verifier.coordinateWiseSpecialSound Verifier.specialSound` at
  `Implications.lean:261` — renames reach into `unfold`/`simp only` name lists). Add nothing to
  the `*Classical` copies (§1 rule 7).
  Gate: green build + a word-boundary grep (`rg -w`) over §4.5's table names shows no
  un-suffixed occurrence outside this plan and comments, **allowing two known-good homonyms**:
  `CoordinateWise.CommittedScalar.coordinateWiseSpecialSoundWithEscape`
  (`CommittedScalar.lean:238`) and `RingSwitching.Lift.coordinateWiseSpecialSoundWithEscape`
  (`Lift/Reduction.lean:186`) are component theorems carrying the notion's name in their own
  namespace; rename them too if you prefer a clean grep — M6 restates both.
- **2b — the generic notion commit (additive; 6–9 h).** Transcribe `CM_gates.lean` **in full**: the
  notion layer into `TranscriptTree/Basic.lean` under the canonical names, and the purity-data
  layer into its §4.1 homes (`Verifier.PureForm` + forgetful + `pureFormOfIsPure` beside
  `Verifier.IsPure` in `OracleReduction/Basic.lean`; `PureForm.append` beside `IsPure.append`
  in `Composition/Sequential/IsPure.lean`; `Verifier.GuardedForm` + `PureForm.toGuardedForm`
  beside `IsGuardedWith` in `CWSS/Guarded.lean` — the latter lands with 3a/4a if import order
  prefers). Ordering constraint: `Verifier.Outputs` must precede `LeafWitnesses.IsValid` (which
  now mentions it), and the target file opens `namespace Extractor` at `:305` before
  `namespace Verifier` at `:323` — hoist `Outputs` accordingly.
  The `TranscriptTree/Basic.lean` declarations: `ChallengeTree.LeafWitnesses`,
  `LeafWitnesses.IsValid` (verifier-relative, ∃-form), `Extractor.TreeBased` (bare function,
  indices `StmtIn WitIn WitOut`), `Verifier.Outputs`, `Verifier.treeSpecialSoundWith` (one
  clause), the escape twin, `withEscape`, `_false_iff`, `mono`, the two `_congr` transports,
  the `Outputs`-level support lemmas `mem_outputs_iff`, `mem_language_of_mem_outputs`,
  `not_isAccepting_of_no_outputs`, `outputs_nonempty_of_isAccepting`,
  `support_init_nonempty_of_accepting`, `outputs_pure_subsingleton`,
  `pure_verdict_mem_outputs`, `isValid_iff_pure` (all consumed by later steps — 4a's
  composition needs the fifth through eighth, M5's engine certificates the last),
  `canonWitnesses` + validity, `old_of_new`, **and the ∃-forms** `Verifier.treeSpecialSound`,
  `treeSpecialSoundEscape`, `treeSpecialSound_iff_exists`,
  `treeSpecialSoundWith.toTreeSpecialSound`, `treeSpecialSoundWithEscape.toEscape` (see the
  ∃-form rule above). Plus the regression-gate file
  `ArkLib/OracleReduction/Security/TranscriptTree/NonVacuity.lean` (the E1–E7 and E20 gates +
  the `coinVerifier`/`pureVerifier` fixtures, transcribed from `CM_gates.lean`). That file
  owns **private** copies of the rejected alternatives (`IsValidUnclaimed`,
  `treeSpecialSoundWithUnclaimed`, `isValidUnclaimed_false_of_two_outputs`, `IsValidFree`,
  `treeSpecialSoundWithFree`) and of the classical form (`oldStatement`) purely so E1/E2/E5 can
  be stated; they are not part of the public notion and M9's shim deletion does not touch
  them — mark them `private` and say so in the module docstring. `git add` the new file, run
  `./scripts/update-lib.sh`.
  The transports are transcription too (E26, from `CM_gates.lean`'s three transport theorems):
  TODAY's `mono`/`_congr` proofs at the widened type — `subst` at the shape homogenizes the
  extractor types before the single `HEq` is consumed. Gotchas: the
  `omit […] in` must precede each transport's docstring — between docstring and `theorem` is a
  parse error; `canonWitnesses` needs decidability of its `∃` — mark it `noncomputable def`
  preceded by `open scoped Classical in`, scoped to that declaration;
  `TranscriptTree/Basic.lean` must not gain a file-wide `noncomputable section`.
  Work order inside the commit (dependency-safe): (1) the purity-data layer in its §4.1 homes
  (`PureForm` is import-upstream of everything else; `GuardedForm` may defer per the note
  above); (2) hoist `Verifier.Outputs`; (3) the notion layer (`LeafWitnesses` → `IsValid` →
  `Extractor.TreeBased` → `treeSpecialSoundWith` + escape twin); (4) the `Outputs`-level
  support lemmas + `isValid_iff_pure`; (5) the ∃-forms and forgetfuls; (6) the transports;
  (7) `canonWitnesses` + validity + `old_of_new`; (8) `NonVacuity.lean` (`git add`, then
  `./scripts/update-lib.sh`); (9) the `omit` sweep for §9 note 8's twelve flagged
  declarations.
  Gate: green + gates pass in-library + IR gate on `PureForm.append` applied to a toy pair
  (the `CM_gates.lean` `appendedPF` pattern).

- **Exit gate:** `./scripts/validate.sh` green; 2a's word-boundary grep clean; the NonVacuity
  gates pass in-library; IR gate on `PureForm.append` (the `appendedPF` pattern).
- **Abort if** a transcribed statement fails to elaborate after adapting namespaces and imports
  *and* the failure names a repo declaration whose signature differs from the one the prototype
  imported (check with `#check`). A tactic that merely needs re-tuning is not an abort. This
  abort rule is shared by every transcription milestone (M3–M6); they cite it as "M2's rule".

### M3 — CWSS notion and path glue (5–7 h)

*Read first: `CWSS/Basic.lean`, `TranscriptTree/Composition.lean`; `prototypes/CM_gates.lean`
(for 3a), `prototypes/CM_append.lean` Part A (for 3b); §9 notes 5, 7, 9.*

*Entry probe (M2 landed):* `rg -l 'TreeBasedClassical' ArkLib/` is non-empty (the rename), and
`rg -n 'def LeafWitnesses' ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean` is
non-empty (the notion).

One commit per step; `lake build` green after each.

- **3a — the CWSS notion commit (additive; 2–3 h).** Re-land, in `CWSS/Basic.lean` at the new
  `Extractor.TreeBased`: `coordinateWiseSpecialSoundWith`, `coordinateWiseSpecialSoundWithEscape`,
  `coordinateWiseSpecialSound`, `coordinateWiseSpecialSoundEscape`,
  `coordinateWiseSpecialSound_iff_exists`, `coordinateWiseSpecialSoundWith.toCWSS`,
  `coordinateWiseSpecialSoundWithEscape.toEscape`, `.withEscape`, `.mono`, and the
  `OracleVerifier` mirrors — all as CWSS-shape instances of 2b's generics, so no new proofs.
  There is no CWSS-level `_congr` to re-land: the only two transports are tree-level (2b's),
  and the CWSS append theorems consume those directly (`CWSS/Composition.lean:445, :467`).
  Also prove here the positivity lemma the guarded-left theorems need — `toShape`'s `arity`
  field is literally `D.arity` (`Basic.lean:184-185`), and `arity_eq` gives `ℓᵢ·(kᵢ−1)+1`:

  ```lean
  theorem CWSSStructure.toShape_arity_pos (D : CWSSStructure pSpec) :
      ∀ i, 0 < D.toShape.arity i := fun i => by
    show 0 < D.arity i
    rw [congrFun D.arity_eq i]; omega
  ```

  Without this step nothing creates the new-typed `isCWSS` that 4b's package fields require.
  Gate: green.
- **3b — the glue commit (additive; 3–4 h).** Transcribe `CM_append.lean` Part A into
  `TranscriptTree/Composition.lean`: `LeafPath.embedRight`, `SplitData.gluePath` + transcript
  spec (`LeafPath.transcript_embedRight`, `SplitData.transcript_gluePath`),
  `LeafPath.transport` + `fullTranscript_transport`, `AppendSplit.gluePath` +
  `fullTranscript_gluePath` — ~140 lines of dependent-index work, all transcription (the glue
  is the ONLY path machinery composition needs; nothing un-glues a path). Known frictions:
  §9 notes 7 and 9.
  Gate: green + **IR gate on `AppendSplit.gluePath`** (runs at runtime in every composed
  extractor).

- **Exit gate:** `./scripts/validate.sh` green; IR gate on `AppendSplit.gluePath`.
- **Abort if** a transcription fails per M2's rule.

### M4 — composition and packages (8–10 h)

*Read first: §4.3 (the composition design and its proof skeleton); `CWSS/Composition.lean`,
`Package.lean`, `Escape.lean`, `Guarded.lean`; `prototypes/CM_append.lean` Parts C–F (the
transcription source); §9 notes 6–8 (note 6 is the dominant friction in these proofs).*

*Entry probe (M3 landed):* `rg -n 'toShape_arity_pos' ArkLib/` is non-empty, and
`rg -n 'gluePath' ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean` is
non-empty.

One commit per step; `lake build` green after each.

- **4a — the composition commit(s) (5–6 h).** Transcribe from `CM_append.lean` Parts C–E, with these
  homes (the import DAG makes the choice load-bearing — `NoChallenge.lean` imports only
  `CWSS/Basic.lean`, so anything M5 step 4 needs must sit no deeper than
  `TranscriptTree/Basic.lean`): `Extractor.TreeBased.append` (`verify₁`-parameterized) and
  `somePath` → `TranscriptTree/Composition.lean`;
  `support_init_nonempty_of_prob_one`/`not_accepting_of_failure` →
  `TranscriptTree/Basic.lean` (their tree-level companion
  `support_init_nonempty_of_accepting` landed in 2b); the verifier-append lemmas
  `append_run_outputs`, `append_run_guardedLeft`, `append_run_outputs_guardedLeft`,
  `outputs_guarded_subsingleton`, `guarded_accepting_of_mem`, `guarded_verdict_mem_outputs` →
  `CWSS/Composition.lean`. `GuardedForm.append` (data half computable; its `verify_eq`
  obligation IS today's sorried `IsGuarded.append`, `Guarded.lean:113` — the sorry relocates,
  census unchanged) → `Guarded.lean`. Then retype the **six** append-soundness theorems in
  `CWSS/Composition.lean` — `append_treeSpecialSoundWith` (`:327`),
  `append_treeSpecialSoundWithEscape` (`:379`), and the four
  `append_coordinateWiseSpecialSound*` across the `Verifier` and `OracleVerifier` namespaces
  (`:433, :453, :494, :518`) — and the **two** in `Guarded.lean` (`:141`, `:161`), with right
  factors **named** (M2's ∃-form rule), instantiating the four generic theorems E12–E15.
  Everything else in those files (shape congruence, `append_run_pure_left`,
  `pure_accepting_of_mem`, `mem_of_pure_accepting`, `IsGuarded*` classes) is untouched.
  **Restate `Guarded.lean:141` in the new form and PROVE it** from E15 (today's `sorry`
  disappears), and **redo its proved corollary** at `:161-181` (its `rcases … with (hf | ⟨_,
  hf⟩) | hwit` at `:178` destructures the composed event's exact shape, so the old proof cannot
  survive the retype). Both guarded-left theorems **gain** the `∀ i, 0 < S₂.arity i` hypothesis
  they do not carry today (D5); discharge it at every downstream call site — the `:161`
  corollary, `GCWSSPackage.append` (`Guarded.lean:241`) and `EscapeGCWSSPackage.append`
  (`Escape.lean:172`, certificate at `:189`) — with 3a's `toShape_arity_pos`. The twelve mixed
  appends (ten in `Escape.lean`, two in `Guarded.lean` — `CWSSPackage.appendGuarded` at `:283`,
  `GCWSSPackage.appendPure` at `:295`) delegate to those and need no change.
  Gate: green + **IR gate on `Extractor.TreeBased.append`** + `#print axioms` on the restated
  `Guarded.lean:141` shows no `sorryAx`.
- **4b — the package commit(s) (3–4 h).** The four package structures at the new extractor/notion types
  under canonical names, with the purity fields at their data forms (§4.4:
  `isPure : verifier.PureForm`, `isGuarded : verifier.GuardedForm` — names kept, types
  bundled). The composed fields read the data: `isPure := L₁.isPure.append L₂.isPure`
  (`PureForm.append`), `extractor := L₁.extractor.append L₁.isPure.verify L₂.extractor`
  (guarded kinds: `L₁.isGuarded.out`), `esc := L₁.esc.append L₂.esc L₁.isPure.verify` — the
  `isPure.is_pure.choose` laundering sites in `Escape.lean` disappear. `toGuarded` conversions
  ride `PureForm.toGuardedForm`. `ofClassical` per kind: the extractor lift is the one-line
  wrapper (E8, instance-free); the package lift fills the purity field via `pureFormOfIsPure`
  (choice — shim-only). The right factor's certificate is passed **named** — the four
  `have h₂ := L₂.isCWSS.to{CWSS,Escape}` lines (`Package.lean:108`, `Guarded.lean:255`,
  `Escape.lean:113`, `Escape.lean:187`) are deleted, since extracting `E₂` from an `∃` is
  `Exists.choose`, noncomputable; the twelve mixed appends delegate to these four and need no
  change. Add the second `▷` dispatch table and the `packageKindOf` widening (§4.5). Wrap
  **nothing yet** — consumers still reference the `Classical` names from 2a and stay green.
  Gate: green + IR gate on the four `*.append`s + an `#eval` smoke test of a toy package built
  **directly at the new types** (calibrate with E25). Do **not** gate on an
  `ofClassical`-lifted package: its purity field goes through `pureFormOfIsPure`
  (`Classical.choice`) and `PureForm.verify` is a *data* field — so a lifted package has no IR
  even when the classical extractor it wraps is computable. Expected, not a regression; record
  it so a later IR sweep does not misread it.

- **Exit gate:** `./scripts/validate.sh` green; IR gates on `Extractor.TreeBased.append` and
  the four package `*.append`s; the toy-package `#eval` smoke test passes; the restated
  `Guarded.lean:141` is `sorryAx`-free.
- **Abort if** a transcription fails per M2's rule.

### M5 — migrate `Security/**` consumers + the two core engines + runtime demo (5–8 h)

*Read first: `SingleRound.lean`, `ScalarRound.lean`, `CommittedScalar.lean`,
`NoChallenge.lean`, `SpecialSoundness.lean`, `Implications.lean`;
`prototypes/CM_enginecerts.lean` (Parts B–E, the engine + certificate source);
`prototypes/CM_append.lean` Part F (the chain-demo calibration); §9 notes 11–13.*

*Entry probe (M4 landed):*
`rg -n 'TreeBased.append' ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean` is
non-empty, and
`rg -n 'PureForm' ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean`
is non-empty (the packages carry the data forms).

File-by-file, green after each; each file's own definitions move off the `Classical` names:

1. **`SingleRound.lean`** — all transcription (E18 + E27). Transcribe the engine and
   certificate layer `CMSR` (`CM_enginecerts.lean` Part C): `branchPathOf` (+ aux layers),
   `collect`, and the new `treeExtractor` — a bare function, `collect` over branches into
   `mkWitness`, reading the witnessing at `branchPathOf`-paths only (no inverse path readers,
   no star-path classification). The component's structural statement readers are its
   verifier's `PureForm.verify` data (E9). Then the lemma layer and BOTH certificates:
   `collect_eq_some`; `fullTranscript_branchPathOf` (closes by bare `rfl`);
   `collect_branch_data`; then `coordinateWiseSpecialSoundWith_of_mkWitness` and the escape
   twin — TODAY's `hpure`/`hmk` hypotheses, the UNCHANGED `escEvent`, the named engine,
   `[Nonempty WitOut]` **dropped** from engine and both certificates; the validity premise
   collapses to per-verdict witnesses via `isValid_iff_pure` (`hpure` +
   `support_init_nonempty_of_accepting` at one branch path), and the readers compute
   definitionally on the star tree, zero cast fixups. The escape disjunction is decided before
   seeing `o` by a classical `by_cases` on the event; in the no-escape branch `hmk`'s escape
   conclusion is refuted because the collected response family is itself an event witness.
   Three frictions are pre-solved (§9 notes 11–13). **Do not reach for
   `Verifier.mem_of_pure_accepting`** (`CWSS/Composition.lean:288`): it concludes `out ∈ lang`
   at a generic language set — a different obligation, only relevant on the `relOut` side.
2. **`ScalarRound.lean`** — transcribe `CMSC` (`CM_enginecerts.lean` Part D): the scalar
   witness-only engine `treeExtractorScalar` (drops the classical `relOut` inversion and the
   `[Nonempty WitOut]` instance) and both certificates at the unchanged `escEventScalar`, with
   `hmk` at `Function.Injective fam` via `injective_of_nodeOk` (E28).
3. **`CommittedScalar.lean`** — delegate: retype the signature; body stays a single
   application.
4. **`NoChallenge.lean`** — the witnessing-agnostic bridges (M0's `onlyPath` step did the root;
   this hooks it to the new notion: the validity premise collapses through purity via
   `isValid_iff_pure` at the component's verdict on `onlyPath`'s transcript). Mind the
   `Verifier`/`OracleVerifier` same-name pair.
5. **`SpecialSoundness.lean`** — D2 = Inherit. Re-introduce `Verifier.specialSound` /
   `OracleVerifier.specialSound` under the canonical names with their *same* defining equations
   — `treeSpecialSound init impl (distinctShape k) relIn relOut` at `:68-71` for `Verifier`,
   the `toVerifier` delegation at `:89-93` for `OracleVerifier` — which now resolve to 2b's
   `treeSpecialSound`. The `*Classical` twins stay until M9. Then add the textbook recovery
   corollary (unconditioned, extractor closed by `canonWitnesses`, via `old_of_new`) so the
   classical reading survives as a theorem.
6. **`Implications.lean`** — the CWSS↔SS bridges (`:255`, `:278`) are ∃-form and
   **shape**-level; neither proof mentions an extractor. Statement updates, not proof work.

7. **The runtime demo (constraint 2's only honest demonstration)** — the milestone's one
   constructive (non-transcription) deliverable; budget accordingly. In a scratch file:
   1. Build `singleRoundPkg` wrapping this milestone's real `SingleRound.treeExtractor`: a
      concrete `pSpec`, a `CWSSStructure` satisfying `arity_eq`, a purity witness, `mkWitness`
      data, and a certificate through the retyped `*_of_mkWitness*`. E29 calibrates the
      engine — including its `Fin` numeral friction (branch indices need
      `Fin.cast foldStructure_arity.symm`; there is no `OfNat` at the unreduced arity
      projection).
   2. Build `tailPkg`, a **synthetic zero-round closing package** (verifier + structure +
      purity + certificate from `coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`). Do
      not reuse `SendWitness` — `SingleRound.treeExtractor` is by design an *open* extractor,
      so the closing factor must be on the right.
   3. Compose `singleRoundPkg ▷ tailPkg` (E19's chains calibrate the wiring); `#eval` the
      chain's `extractor.extract` to `some w`; discharge `(stmt, w) ∈ relIn` by `simp`/`rfl`
      against a concretely-defined `relIn` (relations stay `Set`-valued, so `decide` would
      need a `DecidablePred` instance nobody supplies); kernel-`rfl` the `#eval`.
   4. Vendor the demo into `prototypes/` when it passes.

- **Exit gate:** the step-7 demo passes and is vendored; IR gates over both engines + both
  delegates **+ `CommittedScalar.package`**; delete each `noncomputable section` in this file
  set that comes clean — **for `CommittedScalar.lean` (`:113`) this is mandatory**: after this
  milestone nothing in that file is legitimately noncomputable, and the section is the only
  thing making `CommittedScalar.treeExtractor` and `CommittedScalar.package` noncomputable
  (neither carries a per-declaration marker), so leaving it hides both from every later gate.
  (`NoChallenge`'s section fell in M0; `SpecialSoundness`, `Implications` stay candidates.)
- **Abort if** a transcription fails per M2's rule.

### M6 — components and the `Lift` marker sweep (9–13 h)

*Read first: `ReduceClaim.lean`; `prototypes/CM_enginecerts.lean` Part B; then per-file.*

*Entry probe (M1 + M5 landed):*
`rg -n 'branchPathOf' ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean`
is non-empty (M5's engine), and `rg -n 'noncomputable def cyclotomicPresentation' ArkLib/`
returns nothing (M1's marker drop).

`ReduceClaim` (both engines — transcribe `CMEngines.rcTreeExtractor` **and its full
certificate** `rc_coordinateWiseSpecialSoundWith` from `CM_enginecerts.lean` Part B, adapting
the oracle variant; the certificate consumes validity via `isValid_iff_pure` at the verifier's
statement map), `SendWitness`, `SendClaim`, `CheckClaim`,
`RingSwitching/Lift/Reduction.lean` (delegate) — plus each file's package/statement sites move
off `ofClassical`/`Classical` names.

**Strip the per-declaration `noncomputable` markers** on `RingSwitching.Lift.treeExtractor`
(`Lift/Reduction.lean:174`) and `RingSwitching.Lift.package` (`:204`) while retyping them: no
milestone removes markers implicitly, the file has no `noncomputable section`, and a surviving
marker means IR=N no matter what the body computes. Both roots below them are gone by now —
ScalarRound's engine (M5) and the presentation data (M1) — so the markers come off
unconditionally; this sweep is why the milestone waits on M1.

**Sizing note (measured):** each component inlines its extractor lambda *twice* — once in the
`def`, once re-inlined inside the accompanying proof (`ReduceClaim.lean:190-192` vs `:208-210`;
the oracle variant repeats it at `:413-414` and `:434-435`). Count both.

- **Exit gate:** green; IR gate over `ReduceClaim.treeExtractor`/`.oracleTreeExtractor` **and**
  axiom prints free of `Classical.choice` (E17) — not merely IR-present; retyped delegates;
  `noncomputable section`s deleted where clean; IR gate additionally over
  `RingSwitching.Lift.treeExtractor` and `RingSwitching.Lift.package` (their roots fell in M1
  and M5).
- **Abort if** `ReduceClaim.treeExtractor` / `.oracleTreeExtractor` — the *definitions*, not
  their certificates — need `Classical.choice`. E17 says they do not, so that would mean the
  transcription diverged from the prototype. (The certificates legitimately do; see E17.)

### M7 — Hachi purity data (5–8 h; additive)

*Read first: `Hachi/Composition.lean` module header; §4.4's Hachi bullet; then per-file.*

*Entry probe (M4 landed):* same probe as M5's —
`rg -n 'PureForm' ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean`
is non-empty.

Purely additive preparation, so its session may be slotted anywhere among M5–M6's: it needs 2b's
`PureForm`/`GuardedForm` structures and 4b's data-typed package fields as *targets*, and
nothing later. Extractors attribute no statements (D7); what each Hachi package needs instead
is its `isPure`/`isGuarded` field at the data form. For each package verifier behind the
seven packages named in M8 (plus `handoffPackage`'s, `TraceHandoff.lean:222`), land a named
`PureForm` (guarded kinds: `GuardedForm`) beside the existing `IsPure`/`IsGuarded` instance:
`PureForm.verify` is the verify function already sitting inside that instance's proof —
mechanical relocation, one per package verifier. M8 fills the retyped package fields with
these.

Those `PureForm.verify` data fields must **not** reach for `ZeroCheck/Constraints.lean`'s
noncomputable tables (`wTable`, `wTableMleEval`, `hAlphaEvals`, `hZero`, `hAlpha`) — today
those are `Set`-reachable only, and a verdict function calling one would create a new root of
exactly the shape M1 removed (the packaged verify data is on the runtime path of every
composed extractor).

- **Exit gate:** green; IR gate over every `PureForm`/`GuardedForm` value added (their
  `verify`/`check`/`out` data is runtime-path, §10 R3).
- **Abort if** any package verifier's verdict function cannot be written without a
  noncomputable table — that is a new classical root of the §5 shape, re-report.

### M8 — Hachi retype and computability sweep (9–12 h)

*Read first: §4.4's Hachi bullet, §4.6 (the open recursion seam — what NOT to wander into);
`Hachi/Composition.lean` module header; M7's landed purity data; then per-file.*

*Entry probe (M1 + M6 + M7 landed):* `rg -l 'PureForm' ArkLib/Commitments/Functional/Hachi/`
is non-empty (M7's data), `rg -n '[A-Za-z_]+Classical\b' ArkLib/ProofSystem/Component/ReduceClaim.lean`
returns nothing (M6's migration), and `rg -n 'noncomputable def cyclotomicPresentation' ArkLib/`
returns nothing (M1).

The 12 noncomputable definitions, by name: packages `ZeroCheck/Batch.batchPackage`,
`Recursion/ZBatchBridge.zBatchPackage`, `Sumcheck/Bridge.sumcheckBridgePackage`,
`QuadEval/Bridge.bridgePackage`, `QuadEval/Soundness.quadEvalPackage`,
`RingSwitch/Reduction.liftPackage`, `RingSwitch/Rlin.rlinPackage`; chains
`Sumcheck/Rounds.roundsChainAux`, `.roundsChain`, `Composition.evalChain`, `.openCore`,
`.openingChain`. (A bare `noncomputable` grep over `Hachi/` finds seven more: five table/aux
defs in `ZeroCheck/Constraints.lean` and `InnerOuter/Security.lean:424`'s `advantage` are
reachable only through `Prop`/`Set` positions — genuinely out of scope. The seventh,
`RingSwitch/Reduction.lean:101`'s `cyclotomicPresentation`, was the presentation root — M1
already removed it, which is what makes this milestone's three hardest IR gates
(`liftPackage`, `openCore`, `openingChain`) unconditional.)

Witness assembly unchanged (§4.4). The five sorried leaf extractors (`zeroCheckExtractor`,
`roundExtractor`, `finalEvalExtractor`, `partialEvalExtractor`, `handoffExtractor`) and their
paired certificates are `sorry` on *both* sides, so the retype is free there; four of the five
get *easier* to eventually fill, since the response becomes readable from the witnessing —
`handoffExtractor` does not (§4.6). Each package's `isPure`/`isGuarded` field is filled with
M7's data. Drop each of the 12 definitions' `noncomputable` markers as part of its retype — no
milestone removes markers implicitly, and a surviving marker fails the IR gate below
(`liftPackage`/`openCore`/`openingChain`'s markers lost their last root when M1 landed).

One extractor site carries no name and no `def` of its own: `roundsChainAux`'s zero-count base
case supplies `ReduceClaim.treeExtractor (mapStmt := id) …` inside an **anonymous**
`EscapeCWSSPackage` literal (`Sumcheck/Rounds.lean:290`). A name-navigated sweep cannot find
it, but it is covered mechanically: it must be retyped with the rest of `roundsChainAux`'s body
for the build to stay green, the retyped `ReduceClaim.treeExtractor` it applies arrives with
M6, and `roundsChainAux`'s IR gate certifies it.

- **Exit gate:** green; IR gate over all 12 definitions (unconditional — every root is gone by
  now); every remaining `noncomputable section` in the blast radius deleted; and
  `rg -n '\b[A-Za-z_]*Classical\b' ArkLib/Commitments/Functional/Hachi/` returns nothing beyond
  the legitimate `Classical.choice` / `Classical.ofNonempty` / `open Classical` uses and
  `QuadEval/Basic.lean:38`'s axiom note. (A narrow alternation like `SoundClassical` misses
  `treeSpecialSoundWithClassical`, `toCWSSClassical` and most of the renamed layer.)
- **Abort if** any of the 12 still fails its IR gate once all of its package's dependencies are
  IR-clean: that means a *new* classical root, not a retype, and needs re-reporting rather than
  a local fix.

### M9 — shim removal, validation, docs (6–8 h)

*Read first: §4.5 (the complete inventory of what the shim consists of — the rename table,
`ofClassical`, the second `▷` table); `docs/wiki/repo-map.md` and
`docs/skills/make-computable.md` (the docs-contract targets).*

*Entry probe (M2–M8 landed):* §11 shows M2–M8 green, and
`rg -l '[A-Za-z_]+Classical\b' ArkLib/ProofSystem ArkLib/Commitments` returns nothing (every
consumer is off the shim; the `*Classical` definitions themselves still live in `Security/**`
— deleting them is this milestone).

1. **Delete the shim** (non-optional; D3 was accepted *with* a time-boxed removal, and this is
   the box). Reaching this milestone *is* the entry condition: every notion, package and
   certificate now exists under its canonical name at the computable types, and M5–M8 moved
   every consumer onto them. Delete: the `*Classical` layer from 2a, the four `ofClassical`s,
   the second `▷` table and the `packageKindOf` lift cases (leaving one 16-entry table over the
   canonical packages).
   Gate: `rg -n '\b[A-Za-z_]*Classical\b' ArkLib/` returns nothing beyond genuine `Classical.*`
   library uses — a suffix pattern, because a narrow alternation misses
   `treeSpecialSoundWithClassical`, `coordinateWiseSpecialSoundEscapeClassical`,
   `toCWSSClassical`, `withEscapeClassical`, `toGuardedClassical` and the rest of §4.5's table.
   The vendored prototypes under `docs/plans/prototypes/` are out of scope.
2. `./scripts/validate.sh --lint --docs`.
3. Docs contract (the PR must carry its own docs updates; M9 closes it): update
   `docs/wiki/repo-map.md` and `docs/skills/make-computable.md`; flip this plan's status line
   and `docs/plans/README.md`'s entry to **landed**; note in `prototypes/README.md` that
   `TranscriptTree/NonVacuity.lean` is now the living copy of the gates.

- **Abort if** deleting the `*Classical` layer leaves any consumer red — re-report rather than
  reinstating the shim, since a straggler means an M2–M8 site was never migrated.

**Total (M0–M9): 69–99 h ≈ 9–12 working days; no milestone above 13 h.** The estimate assumes
transcription, not proof search, and that assumption is uniform: the notion, the transports,
purity-as-data, all four composition theorems, and all four engine certificates are vendored
and green, so no milestone carries a substantial unprototyped proof.

### Scope boundary (verified inert — no milestone touches these)

`ArkLib/OracleReduction/Composition/Sequential/{Append,General,IsPure}.lean` contain no
`TreeBased`/`treeSpecialSound` code (one doc mention); `Extractor.RoundByRound` and
`Extractor.Straightline` are unaffected (the `*RbrExtractor` families under
`ProofSystem/Binius/**` and `RingSwitching/Packing/**` are a different type and a different
project); `SendChallenge.lean` is `CWSSStructure`-only; `EscapeEvent` and the escape events
freeze (§4.4, D4).

**Existing `sorry`s in the blast radius — census** (measured against the baseline, so new
regressions are distinguishable from existing gaps):

- the five files defining the six noncomputable extractors: **0** `sorry`;
- `CoordinateWiseSpecialSoundness/` + `TranscriptTree/` + `SpecialSoundness.lean`: **2**, both
  in `Guarded.lean` — `IsGuarded.append` (decl `:113`; non-blocking, no extractor, untouched)
  and `append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft` (decl `:141`) — **which this
  plan proves** (E15) in 4a; its proved corollary at `:161-181` must be redone;
- the seven direct Hachi consumers: **18** (PartialEval 6, TraceHandoff 4, FinalEval 3,
  Rounds 2, ZeroCheck/Reduction 2, Sumcheck/Bridge 1; `RingSwitch/Rlin.lean` is sorry-free) —
  restated, not proved, and not in the hours above;
- `Implications.lean`: 12 live occurrences, none in its CWSS section.

The refactor's core is `sorry`-free going in and comes out with one *fewer* `sorry`.

## 8. Decisions (all resolved — do not reopen)

| # | Decision | Resolution | Rationale |
| --- | --- | --- | --- |
| D1 | Accept "closed relative to a terminal link" for Hachi (§4.6)? | **Accept** | The alternative — a `WitOut` payload on `ChallengeTree.leaf` — is killed on vacuity grounds, moves the blast radius into `Composition.lean`'s dependent-index work, and makes correctness hypothesis-bound. No alternative clears the Ajtai barrier: the per-link leaf-witness input is unavoidable, while the closed chain extracts from the tree alone. |
| D2 | May `Verifier.specialSound` change shape? | **Inherit the new form** | One notion everywhere beats a parallel notion + bridge: `specialSound` *is* `treeSpecialSound (distinctShape k)` and stays so. The textbook unconditioned statement is recovered as a corollary via `canonWitnesses`/`old_of_new` (M5 step 5). |
| D3 | Red branch for ~2 weeks, or fund a shim? | **Shim, with time-boxed removal (M9)** | §4.5. The import DAG cooperates; `ofClassical` rides on the machine-checked `new_of_old` (E8). The `*Classical` names are transition scaffolding, never a permanent parallel API. |
| D4 | Does the escape layer freeze (§4.4)? | **Freeze** | Both escape appends are proved at today's `verify₁`/`out₁`-indexed `EscapeEvent.append` byte-for-byte (E13, E15), and the event's `verify₁` index is natural here — packages feed it `isPure.verify` (data), no choice laundering. Widening the event is the worthless-certificate failure mode its own docstring warns about. |
| D5 | Carry `∀ i, 0 < arity i` explicitly, or rely on CWSS shapes? | **Carry on the guarded-left append theorems only** (`harity₂`); the generic notion stays unconditioned, with the arity-0 edge documented (E20) | The guarded-left proof genuinely needs it (`somePath` must produce a suffix leaf) and nothing else does. This is an **added** hypothesis: today's `Guarded.lean:141`/`:161` carry no positivity condition, so 4a must discharge it at every downstream call site via `toShape_arity_pos`. |
| D6 | Land `onlyPath` + witnessing-agnostic bridges first, before the notion work? | **Yes** | Independent of the notion change; removes the fifth classical root; shrinks every later diff; vendored and IR-checked (E24). |
| D7 | How is the witness input typed, and where do validity's statements and composition's seam statement come from? | **Witness-only extractor + reachability-∃ validity + purity as data.** `LeafWitnesses` is witness-typed (`LeafPath → Option WitOut`); `IsValid` demands each witness certify *some verifier-reachable* statement (∃ over `Verifier.Outputs`, not ∀ — the ∀-form is the G0 kill); the notion has ONE clause; `Extractor.TreeBased` stays a bare function (indices `StmtIn WitIn WitOut`); packages retype `isPure`/`isGuarded` to the data-carrying `PureForm`/`GuardedForm`, whose `verify`/`out` feeds `TreeBased.append` and the escape events | The extractor extracts, the verifier attributes statements — responsibilities uncrossed. Honesty is the validity premise's reachability condition (teeth: E5's G3 pair) and collapses to per-verdict witnessing at pure verifiers (`isValid_iff_pure`, E35), so engine certificates keep TODAY's `hpure`/`hmk`. Composition reads the seam statement off `PureForm.verify` — named data on the verifier, no choice — and needs no path splitting (only `gluePath`, E10). Rejected alternatives: a claim map stored in the *extractor* (solves the seam but crosses responsibilities — the extractor is not the statement authority); statement-keyed `Option (StmtOut × WitOut)` witnessings (no consumer needs to *read* statements from the witnessing — composition reads `PureForm.verify`, engines read their own transcripts). The leaf-witness input itself is unavoidable (§4.6). Costs: the packages' purity fields become data (one-field retype; instance bodies already contain the function), and `ofClassical` package lifts pay `pureFormOfIsPure` (shim-only). |
| D8 | How does `cyclotomicPresentation` become computable — an adapter, or a rewrite of the structure? | **Rewrite**: `Presentation` keeps its name and fields but carries `CPolynomial` data; `IsPresentation` states the laws as the `toPoly` semantics | The adapter leaves a noncomputable `cyclotomicPresentation` and contorts every signature around an erasure accident. The rewrite is the repo's own `CyclotomicModulus`/`IsCyclotomic` idiom, instance proofs land verbatim on QuotientLift lemmas (E32), the engine rename is mechanical (E30). The Hachi data was computable all along. |
| D9 | Does `LiftedWitness.ρ` move to `CPolynomial` too? | **Yes** (with D8), `hρ` stated via `toPoly` | The complete `w.ρ` read census in `Hachi/**` is two sites; everything else is type-position. It kills the constructibility barrier: no Mathlib `Polynomial` value compiles at all, so at the old type no concrete witness or demo could exist (E33). |

## 9. Implementer notes

1. **No single automated test is sound; the decisive probe is `def probe := @X` outside any
   `noncomputable section`.** That either compiles or names the first blocker. The two cheaper
   tests each fail in one direction:
   - `Lean.isNoncomputable` (and the keyword) **under**-report: codegen failures inside a
     `noncomputable section` are swallowed without setting the flag.
   - `Lean.IR.findEnvDecl` **over**-reports: type aliases, `Set`-valued relations, structure
     projections and matchers legitimately have no IR (a repo-wide scan found 661 such
     perfectly-computable definitions). Restrict IR checks to data-valued definitions you care
     about.
2. **The inventory probe** (M0 step 2) — enumerates the population §2 counts:

   ```lean
   import ArkLib
   open Lean in
   run_cmd do
     let env ← Lean.getEnv
     let targets := [``Extractor.TreeBased, ``CoordinateWise.CWSSPackage,
       ``CoordinateWise.GCWSSPackage, ``CoordinateWise.EscapeCWSSPackage,
       ``CoordinateWise.EscapeGCWSSPackage]
     for (nm, info) in env.constants.toList do
       if !nm.isInternal && Lean.isNoncomputable env nm
           && targets.any (fun t => info.type.find? (·.isConstOf t) |>.isSome) then
         Lean.logInfo m!"{nm}"
   ```

   Pass = the logged list matches the expected 20 (and the 6 narrowly extractor-typed ones).
   `isNoncomputable` under-reports, so treat a *shorter* list as a signal to spot-check with
   `def probe := @X`, not as good news.
3. **The IR-gate template** (live examples at the end of every `CM_*` file) — copy into a
   scratch file, edit the name list per milestone, `lake env lean` it:

   ```lean
   import ArkLib.<the module under test>
   open Lean in
   run_cmd do
     let env ← Lean.getEnv
     for nm in [``Foo.bar, ``Foo.baz] do  -- the milestone's target definitions
       match Lean.IR.findEnvDecl env nm with
       | some _ => Lean.logInfo m!"IR PRESENT: {nm}"
       | none   => Lean.logWarning m!"NO IR (noncomputable): {nm}"
   ```

   Pass = every target logs `IR PRESENT`. For extractors additionally check the axiom print
   (`#print axioms Foo.bar`) — M6's `ReduceClaim` targets must be `Classical.choice`-free
   (E17), not merely IR-present.
4. **`noncomputable section` is a fallback, not a blanket.** A computable `def` inside one is
   still compiled; what the section does is silently swallow codegen failures — which is how
   this stack rotted unnoticed. Delete the section when a file is clean.
5. **Hoist the induction hypothesis before any `subst` on a tree index.** `subst` reverts and
   reintroduces the child, severing it from the termination argument. Corollary: do **not**
   hand the equation compiler a `termination_by sizeOf` — plain structural recursion through
   `children j` is accepted (as in `SplitData.sndAt_isStructured`), and the explicit measure
   *breaks* it.
6. **The `(S₁.append S₂).arity` / `appendArity S₁.arity S₂.arity` mismatch is the dominant
   friction in composition proofs** — defeq at default transparency, distinct at `rw`'s keyed
   matching. The pattern that works (used throughout `CM_append.lean`): (a) re-type incoming
   hypotheses **once** by a defeq `have` into `appendArity`-land; (b) assemble the desired fact
   entirely inside a `have` whose statement you author at the `appendArity` forms, where every
   `rw` is syntactic; (c) close against the goal with `exact` or `▸` (full definitional
   transparency). Never `rw` against the goal's notion-typed forms. The friction surfaces in
   *transcript* position (validity mentions `p.fullTranscript`): the worked example is
   `CM_append.lean`'s `key`-`have` inside each `hsuffValid` — a ∀-quantified transfer authored
   over `appendArity`-typed trees, applied to the notion-typed tree by `exact`.
7. **Instantiated `∀`-hypotheses may hold un-beta-reduced lambdas**
   (`(fun p => …) (gluePath …)`), on which `rw` cannot match. Re-type by a defeq `have` with
   the beta-reduced statement before rewriting.
8. **Section-variable instances are auto-included in theorem statements even when unused**
   (the `unusedSectionVars` linter flags them). A helper lemma that silently carries
   `[∀ i, SampleableType (pSpec.Challenge i)]` fails with `synthInstance` errors when applied
   at a spec with no such instance (the fold/scalar `pSpec`s). Keep the notion-layer helper
   lemmas in instance-free sections or `omit` the instance per declaration. The prototypes are
   only *mostly* clean here: their compile output carries `unusedSectionVars` warnings on 12
   declarations (10 in `CM_gates.lean`, 2 in `CM_append.lean` — `mem_outputs_iff`,
   `pure_verdict_mem_outputs`, `new_of_old`, `PureForm.isPure` among them), so 2b/4a must add
   the `omit`s the prototypes skipped — a verbatim copy lands those warnings in the repo.
9. **Pattern-variable capture:** in any file where `SplitData` is in scope, a match pattern
   variable named `msg` resolves to the constructor `SplitData.msg` and fails; rename the
   binder (`msg₂`).
10. See [`../skills/make-computable.md`](../skills/make-computable.md) for the full triage
    workflow.
11. **Support-membership goals under the current VCVio API** (worked examples:
    `CM_gates.lean`, `pure_verdict_mem_outputs`; `CM_append.lean`,
    `guarded_verdict_mem_outputs`): a `rw`/`simp only [support_bind_const, support_pure]`
    route does not key when the goal spells the computation through projections. Prove the
    membership at a spelling you author (a `have` + `congr 1`, the note-6 move), then close
    term-style with
    `(mem_support_bind_iff init _ _).2 ⟨s, hs, (mem_support_pure_iff _ _).2 rfl⟩` — term mode
    is defeq-tolerant where `simp` keying fails.
12. **A `refine`-introduced un-beta-reduced redex in the goal** blocks `rw`/`▸`; `change` to
    the beta-reduced form fixes it (the style linter wants `change`, not `show`). Worked
    example: `CM_enginecerts.lean`, `collect_branch_data`.
13. **After `rw` at a `collect` equation, finish with `rfl`**: the `Option.map`/reader collapse
    is defeq at default transparency but not syntactic.

## 10. Risks

| # | Risk | Gate |
| --- | --- | --- |
| R1 | The CWSS-shape instantiation of the four generic append theorems (via `CWSSStructure.toShape_append` congruence) is transcription-adjacent but not itself prototyped — the prototypes prove the shape-generic statements. If it fights the shape-congruence transports, 4a (M4) inflates. | The repo's existing append theorems already do the identical `toShape_append` dance, and the `_congr` transports exist for exactly this; budget one extra compile cycle, abort and re-report if the `HEq` transport pattern genuinely fails. |
| R2 | The `▷` elaborator change is not machine-checked (the `ofClassical` lift and certificate are, E8). A surprise inflates 4b (M4). | The certificate is `new_of_old` (E8) modulo the escape/guarded disjunction — if 4b needs more, abort and re-report. The elaborator change is ~1 h against a dispatch that already reads head constants (`packageKindOf`, `Escape.lean:380`), and the lift expression it wraps is instance-free. |
| R3 | A green `lake build` never certifies computability (nine `noncomputable section` files swallow codegen failures silently). The refactor could "succeed" without achieving its goal. | IR gate per milestone (§9 note 3); delete each `noncomputable section` as its file comes clean. `AppendSplit.gluePath` and the packages' `PureForm` data (`verify` runs at every seam; `PureForm.append`'s composed verdict in every ≥3-fold chain) are on the runtime path — they are in every gate list from 3b/4b onward. |
| R4 | M1 states the presentation laws via `toPoly`, so the engine keeps working at the `Polynomial` level — but any *future* lemma wanting CPolynomial-level algebra leans on CompPoly's thinner lemma surface. Separately, kernel `decide` on `Array`-backed values does not reduce. | The prototype needed only `natDegree_toPoly`, `toPoly_zero`, `natDegree_C` — all present (E30–E33); new CompPoly lemmas arise only if someone *changes* the engine. M1's abort bans `decide` on `Array`-backed values; gates use `#eval` + IR. |

## 11. Execution log

The cross-session ledger (§7 session protocol steps 2 and 5). One row per milestone; a
session may not start unless every row its milestone waits on is **green**. Fill rows with
real output, not summaries: paste the gate lines (grep hits, `IR PRESENT` lines, axiom
prints) or cite the commit whose message carries them. Statuses:
`pending` → `in progress (through step …)` → `green` | `aborted (<trigger>)`.

| Milestone | Status | Commits | Gate evidence / deviations |
| --- | --- | --- | --- |
| M0 | green | `329ff98d554bb459892ff5dea99e8c0c6363cea0` (steps 1–2, the baseline); `2b22cbe0733689c46f48d5905e2aa092b5e64289` (step 3, `onlyPath`) | **Step 2 inventory probe** (§9 note 2) logged exactly **20** noncomputable definitions and **6** narrowly extractor-typed, matching §2: roots `CoordinateWise.SingleRound.treeExtractor`, `CoordinateWise.ScalarRound.treeExtractorScalar`, `ReduceClaim.treeExtractor`, `ReduceClaim.oracleTreeExtractor`; delegates `CoordinateWise.CommittedScalar.treeExtractor`, `RingSwitching.Lift.treeExtractor`; packages/chains `CommittedScalar.package`, `RingSwitching.Lift.package` + M8's 12 under `ArkLib.Lattices.Ajtai.InnerOuter` (`batchPackage`, `zBatchPackage`, `sumcheckBridgePackage`, `bridgePackage`, `quadEvalPackage`, `liftPackage`, `rlinPackage`, `roundsChainAux`, `roundsChain`, `evalChain`, `openCore`, `openingChain`) — M8's named list confirmed against the baseline. **`./scripts/validate.sh`**: `Build completed successfully (4148 jobs)`; `No ArkLib/Data non-sorry warnings found.`; `✓ All imports are up to date!` over `324 imports`; `All documentation integrity checks passed.`; `Knowledge base lint passed.` **IR gate:** `IR PRESENT: ProtocolSpec.ChallengeTree.onlyPath` and `'ProtocolSpec.ChallengeTree.onlyPath' does not depend on any axioms` (strictly better than the `Exists.choose`-backed `onlyTranscript` it replaces); the §9 note 1 decisive probe `def probe := @ProtocolSpec.ChallengeTree.onlyPath` compiles outside any `noncomputable section`. **Root removed:** `rg -w onlyTranscript ArkLib/` returns nothing. **Runtime:** on a concrete one-message `SendWitness` tree, `#eval tree.onlyPath.fullTranscript 0` prints `42`, kernel-`rfl`-checked (`onlyPath_reads_message`, axioms `[propext, Quot.sound]`) — the `msgNode` branch, not just the `leaf` one, is on the executable path. **Deviations:** (a) `onlyPath` is homed in `TranscriptTree/Basic.lean` beside `LeafPath` (the structure it constructs) rather than in `NoChallenge.lean` where `onlyTranscript` lived, per `make-computable.md` step 4's rule that a new executable algorithm belongs next to its structure, never in the consumer file; `NoChallenge.lean` keeps `transcripts_eq_singleton`/`fullTranscripts_eq_singleton` and loses its `noncomputable section`. (b) Only the two `SendWitness` statements needed touching, as predicted: the other four bridge consumers (`CheckClaim`, `SendClaim`, `ReduceClaim` ×2) pass an `e` that ignores its transcript argument, so their applications stay defeq across the `onlyTranscript → onlyPath.fullTranscript` swap. (c) `docs/kb/_generated/declarations.json` still lists `onlyTranscript`; per `docs/wiki/generated-files.md` that file is refreshed by `.github/workflows/kb-generated.yml`, not by feature PRs — deliberately left alone. |
| M1 | green | one commit, `feat(Lift): computable presentation layer (CPolynomial data, toPoly laws)` — SHA to be filled by the repository owner (committing is disabled in-session; see the session-global note below) | **Prototype reproduced first** (`lake env lean docs/plans/prototypes/CM_presentation.lean`): `2, 3, 5, 2, 2, some 2`, four axiom prints free of `sorryAx`, six `IR PRESENT`, `NO IR AS EXPECTED (the negative control): CMP.liftPackageLikeM` — exactly §6's predicted output. **Step 1 gate** (`Lift/Presentation.lean`): green, and the declaration list is **identical name-for-name** (17 declarations, `diff` of the extracted `structure`/`class`/`def`/`theorem` names against `HEAD` is empty); every proof body survived the mechanical `P.modulus ↦ P.modulus.toPoly`, `P.rep x ↦ (P.rep x).toPoly` rename verbatim, confirming E30. **Step 2 gate** (`Lift/Reduction.lean`): green. **Step 3 gate** (`Hachi/RingSwitch/Reduction.lean`): green; **IR gate** `IR PRESENT: ArkLib.Lattices.Ajtai.InnerOuter.cyclotomicPresentation`, and §9 note 1's decisive probe `def probeCyclotomicPresentation := @…cyclotomicPresentation` compiles outside any `noncomputable section` (`IR PRESENT` too). **Exit gate — `./scripts/validate.sh`**: `Build completed successfully (4148 jobs)`; `No ArkLib/Data non-sorry warnings found.`; `✓ All imports are up to date!` over `324 imports`; `All documentation integrity checks passed.`; `Knowledge base lint passed.` **Engine proved, not sorried:** `#print axioms` on `RingSwitching.Lift.recover`, `Presentation.mulVec_eq_of_evalAt_rowSum`, `exists_rowSum_eq_of_mulVec_eq`, `mulVec_eq_of_rowSum_eq`, `rep_add`, `rep_sum`, `cyclotomicPresentation`, `isPresentation_cyclotomic` — all `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**. (`Classical.choice` here is E25's calibration point, reproduced identically by the prototype: it enters through `Prop`-side instance arguments — `Rq`'s `CommRing` borrows its laws from the noncomputable quotient bridge — and is erased at codegen; the IR gate, not the axiom print, is the computability judge.) **E33 runtime reproduced in-repo** at `Phi17 := powTwoCyclotomic 1` over `ZMod 17`: `#eval pres17.modulus.natDegree` → `2`, `(pres17.rep x17).coeff 0/1` → `3`/`5`, `(w17.ρ 0).coeff 0` → `2`, `CPolynomial.eval 3 (w17.ρ 0)` → `2`, with `IR PRESENT` on `pres17`, `x17`, `w17` — a concrete `LiftedWitness` now *constructs*, which was impossible at the Mathlib carrier. Kernel-`rfl`-checked structure (`pres17.rep x17 = x17.1`, `pres17.modulus = Phi17.φ`); no `decide` on `Array`-backed values anywhere (M1 abort rule / R4). **Sorry census unchanged**: 12 in `ZeroCheck/Constraints.lean`, 0 in the other three touched files, both before and after. **Markers**: `cyclotomicPresentation` drops `noncomputable`; `Lift.rowSum` keeps its marker **by design** (a `Polynomial`-valued spec object reachable only through `Prop`s — its docstring now says so, so a later sweep does not misread it); `Lift.treeExtractor`/`Lift.package`/`liftPackage` keep theirs, as the exit gate prescribes (their other root falls in M5, removed in M6/M8). **Deviations:** (a) M1 lands as **one commit**, not three. The carrier change is a single type-level move that cascades across the three files (`Lift/Reduction.lean` reads `P.modulus.natDegree` in five signatures), so no intermediate step can build; §1 rule 5's per-commit rule names *lettered* steps (2a, 2b, …) and M1's are numbered, so this preserves §4.5's stronger always-green-at-every-commit invariant. (b) `Lift/Presentation.lean` gains two imports — `CompPoly.Univariate.Basic`, `CompPoly.Univariate.ToPoly` — the minimal pair putting `CPolynomial`/`toPoly` in scope (the same pair `ArkLib/ToCompPoly/Univariate/Basic.lean` uses), deliberately **not** the prototype's `Data/Lattices/CyclotomicRing/QuotientLift` import, which would drag the cyclotomic layer into the file whose whole point is that cyclotomic rings are one instance and not the definition; `open … CompPoly` added in the three touched Lean files. (c) `isPresentation_cyclotomic`'s `natDegree_rep_lt` keeps the **repo's existing `simpa` proof verbatim** (verified to still elaborate) rather than the prototype's `rwa` spelling — same QuotientLift lemmas, smaller diff, and step 3's "keeps its proofs verbatim" read literally. (d) `RhoShort`'s binder retypes to `Fin n → CPolynomial (ZMod q)` (its *body* is textually unchanged, and `(ρ i).coeff k` now reads the computable `CPolynomial.coeff`, as predicted). (e) The `Nonempty (LiftedWitness …)` instance's `hρ` proof changes from `by simp` to `rw [CPolynomial.toPoly_zero, Polynomial.natDegree_zero]; exact Nat.zero_le _`: CompPoly marks `toPoly_zero` `@[simp]` only at `Raw`, not at `CPolynomial`. (f) `ZeroCheck/Constraints.lean`'s single census site is the *statement* of `hAlphaEvals_rowPoint`, spanning `:172-175`; all three reads in it (`.rep`, `.modulus`, `w.ρ i`) gain `.toPoly`. The theorem was and stays `sorry`. **Abort criteria not triggered:** every engine proof survived the rename; `rg -n '\.ρ\b' ArkLib/` confirms the complete read census is exactly three sites — `Lift/Reduction.lean:116` (step 2), `Hachi/RingSwitch/Reduction.lean:149` (step 3's `RhoShort ρBound w.ρ`), `ZeroCheck/Constraints.lean:175` (the one predicted outside site) — so no `Hachi/**` site reads `w.ρ`/`P.rep`/`P.modulus` in a data position. |
| M2 | green | two commits, `refactor(CWSS): suffix the outgoing tree-soundness layer with `Classical`` (2a) and `feat(CWSS): witness-only tree special soundness and purity as data` (2b) — SHAs to be filled by the repository owner (committing is disabled in-session; the session hands over `scratchpad/m2/commit-m2.sh`, which reverse-applies `2b-notion.patch` to recover the 2a tree, commits 2a, re-applies it, commits 2b; the split was verified to reproduce the working tree byte-for-byte) | **Prototypes reproduced first, then kept live** (§1 rule 3: *apply the rename inside `docs/plans/prototypes/`* — chosen over re-running at `BASELINE`, so the vendored evidence stays checkable by M3–M6). Three edits, all mechanical: `Extractor.TreeBased ↦ Extractor.TreeBasedClassical` (4 sites in `CM_gates.lean`), `nonempty_leafPath` re-proved as `⟨onlyPath tree⟩` (M0 deleted `onlyTranscript_mem`; the `IsEmpty` instance moved above it), and `CM_enginecerts.lean`'s **inlined** `ProtocolSpec.ChallengeTree.onlyPath` deleted in favour of M0's in-library one (it had collided since M0 — `has already been declared`). All four then reproduce §6 exactly: `CM_gates` → `some 42`, `some 5`, `some 4`, five `IR PRESENT`; `CM_append` → `some 11`, `some 211`, ten `IR PRESENT` (`SplitData.gluePath`, `AppendSplit.gluePath`, `somePath` among them); `CM_enginecerts` → `some 21`, `none`, seven `IR PRESENT`; `CM_presentation` → `2, 3, 5, 2, 2, some 2`, six `IR PRESENT` + `NO IR AS EXPECTED (the negative control): CMP.liftPackageLikeM`; **zero `sorryAx` mentions in all four**. **Step 2a gate:** `Build completed successfully (4148 jobs)`; the word-boundary grep (`rg -nw`) over §4.5's table names returns **nothing** across every `.lean` file under `ArkLib/` — the only un-suffixed occurrence left anywhere in `ArkLib/` is one prose mention, `hachi-overview.html:458` (`EscapeCWSSPackage.esc`, a rendered overview doc, i.e. the gate's comment carve-out). Both known-good homonyms were renamed too (the clean-grep option §4.5 offers): `CommittedScalar.coordinateWiseSpecialSoundWithEscapeClassical` and `RingSwitching.Lift.coordinateWiseSpecialSoundWithEscapeClassical` — M6 restates both. **Step 2b gate — IR:** `IR PRESENT` on `Verifier.PureForm.append`, `Verifier.PureForm.toGuardedForm`, `Extractor.TreeBased.ofClassical`, the `appendedPF` toy pair, its `toGuardedForm`, `ofClassicalDemo`, `fwdExtDemo`, and the three §9-note-1 decisive probes (`def probePureFormAppend := @Verifier.PureForm.append`, …) — ten lines, no `NO IR`. **Runtime:** the composed seam verdict runs (`#eval appendedPF.verify () …` → `false`; `appendedGF.check`/`.out` → `true`/`false`), `ofClassicalDemo … → some 5`, `fwdExtDemo … (fun _ => some 42) → some 42`. **Axioms:** `#print axioms` on all 31 new declarations is free of `sorryAx` (`Verifier.PureForm.isPure` and `GuardedForm.isGuarded` depend on *no* axioms; `PureForm.toGuardedForm` on `[propext]`; `NonVacuity.isValid_none_false` on `[propext, Quot.sound]`; the rest carry `Classical.choice` through `Prop`-side instance arguments — E25's calibration point, erased at codegen, which is why the IR gate is the computability judge). **NonVacuity gates pass in-library:** all nine (G0–G4 + `classical_refutable` + the two E20 lemmas) compile in `Security/TranscriptTree/NonVacuity.lean`. **Exit gate — `./scripts/validate.sh`:** `Build completed successfully (4149 jobs)`; `No ArkLib/Data non-sorry warnings found.`; `✓ All imports are up to date!` over `325 imports`; `All documentation integrity checks passed.`; `Knowledge base lint passed.` **Sorry census unchanged** (327 `sorry` tokens under `ArkLib/` before and after). **Deviations:** (a) *Suffix placement.* The `Classical` suffix goes on the notion root **and** on dotted children / before flat qualifiers, so that §4.5's grep is literally clean: `treeSpecialSoundWithClassical.withEscapeClassical`, `…EscapeClassical.monoClassical`, `…WithClassical.toCWSSClassical`, `…EscapeClassical.toEscapeClassical`, `toTreeSpecialSoundClassical`, `toGuardedClassical`, `treeSpecialSoundClassical_iff_exists`, `treeSpecialSoundWithClassical_congr`, `treeSpecialSoundWithEscapeClassical_false_iff`, `append_coordinateWiseSpecialSoundWithClassical_of_guardedLeft`, `coordinateWiseSpecialSoundWithEscapeClassical_of_mkWitness`. Package *members* (the 16 appends) are renamed by namespace only. (b) *Sanctioned shim additions* (§4.5's bridge, deleted by M9 with the rest): `Extractor.TreeBased.ofClassical` and `Verifier.treeSpecialSoundWith.new_of_old`, both in an explicitly-labelled shim docstring; `old_of_new` is stated with its conclusion **written out** (§4.1) rather than through the classical notion, so it survives M9 unchanged. (c) *Homes.* `Verifier.Outputs` + its seven support lemmas sit in a fresh `namespace Verifier` block hoisted above the leaf-witnessing block (the ordering constraint 2b names); `LeafWitnesses`/`IsValid`/`isValid_iff_pure`/`canonWitnesses` live in `namespace ProtocolSpec.ChallengeTree` (so `o.IsValid …` and `tree.LeafWitnesses …` dot-notation work), and the whole new support layer is **instance-free**: `ChallengeTree.IsAccepting` turns out not to take `[∀ i, SampleableType (pSpec.Challenge i)]`, so §9 note 8's `omit` sweep was discharged by dropping the section variable instead — only `old_of_new` needed an `omit`. Zero `unusedSectionVars` warnings in the touched files. (d) *Line-length hygiene.* `linter.style.longLine` **is** active in this build (it is not merely a `--lint` check), and a 9-character suffix pushed 139 lines past 100 columns; all were rewrapped/broken, so the milestone adds **zero** new long-line warnings (74 remain repo-wide, all pre-existing and outside the diff). A token-stream diff against a freshly-renamed `HEAD` proves the rewrap lost nothing: every touched file differs from renamed-`HEAD` by *insertions only*, the single exception being the one deliberate docstring edit in `Composition/Sequential/IsPure.lean` (its prose now names the canonical `append_treeSpecialSoundWith`, which 4a re-introduces). (e) `GuardedForm`/`PureForm.toGuardedForm` landed in `CWSS/Guarded.lean` now (2b's stated option) rather than deferring to 3a/4a. **Abort criteria not triggered:** every transcribed statement elaborated after adapting namespaces; the only proof adaptations were (i) `init`/`impl` binder explicitness per declaration (the prototype's own pattern: implicit where inferable from `hacc`, explicit otherwise) and (ii) `NonVacuity`'s `pureVerifier_accepting`, which the prototype proved via `Verifier.pure_accepting_of_mem` — unavailable here, since that lemma lives in `CWSS/Composition.lean` and importing it into `TranscriptTree/` would close an import cycle through the folder umbrella. It is replaced by a local `pureRun` unfolding lemma in the `coinRun` style, 6 lines, no new assumptions. |
| M3 | green | two commits, `feat(CWSS): coordinate-wise special soundness at the witness-only extractor` (3a) and `feat(CWSS): leaf-path glue for the tree append` (3b) — SHAs to be filled by the repository owner (committing is disabled in-session; the session hands over `scratchpad/m3/commit-m3.sh`, which reverse-applies the three M3 patches to recover the M2 end state, commits **M2 step 2b** — still uncommitted at session start, see the note below — then 3a, then 3b, then this log update, taking each message from a `msg-*.txt` beside it via `-F`; the split was verified to reproduce the working tree byte-for-byte and the rewind/replay round trip was dry-run in place, and the 3a-only tree was built separately so the two commits bisect) | **Entry probe:** `rg -l 'TreeBasedClassical' ArkLib/` returns 18 files; `rg -n 'def LeafWitnesses' …/TranscriptTree/Basic.lean` → `491:def LeafWitnesses (tree : ChallengeTree pSpec arity 0) (WitOut : Type) : Type :=`. Ground green before the first edit: `Build completed successfully (4149 jobs)`. **Step 3a gate** (`CWSS/Basic.lean`): `Build completed successfully (4149 jobs)` — verified on the 3a-only tree (3b reverse-applied), so the two commits bisect. All **17** re-landed declarations `#check`, and `#print axioms` on the eight new theorems is free of `sorryAx` (`CWSSStructure.toShape_arity_pos` on `[propext, Quot.sound]`; the rest carry `Classical.choice` through `Prop`-side instance arguments — E25's calibration point, as at 2b). `lake env lean` on the file emits **zero** messages. **Step 3b gate** (`TranscriptTree/Composition.lean`): `Build completed successfully (4149 jobs)`; `lake env lean` on the file emits **zero** messages; **IR gate** — `IR PRESENT` on `ProtocolSpec.ChallengeTree.{LeafPath.embedRight, SplitData.gluePath, LeafPath.transport, AppendSplit.gluePath}` plus the two §9-note-1 decisive probes (`def probeSplitDataGluePath := @…`, `def probeAppendSplitGluePath := @…`, elaborated outside any `noncomputable section` — `Composition.lean` has none), six lines, no `NO IR`; `#print axioms` on the four glue theorems free of `sorryAx` (`LeafPath.fullTranscript_transport` on `[propext, Quot.sound]`). **Prototypes re-run, all four green** (§1 rule 3's choice: patch the prototypes): `CM_gates` → `some 42`, `some 5`, `some 4`, five `IR PRESENT`; `CM_append` → `some 11`, `some 211`, ten `IR PRESENT`; `CM_enginecerts` → `some 21`, `none`, seven `IR PRESENT`; `CM_presentation` → `2, 3, 5, 2, 2, some 2`, six `IR PRESENT` + `NO IR AS EXPECTED (the negative control): CMP.liftPackageLikeM`; **zero `sorryAx` mentions in all four**. The `CM_append` demos are now the strongest 3b evidence: with Part A deleted from the prototype, `CMDemo.chain`/`chain₃` run through the **library's** `AppendSplit.gluePath`, so `some 11` / `some 211` are kernel-`rfl` receipts for the transcribed glue, and the prototype's own IR gate reports `IR PRESENT: ProtocolSpec.ChallengeTree.{SplitData,AppendSplit}.gluePath` against the library declarations. **Exit gate — `./scripts/validate.sh`:** `Build completed successfully (4149 jobs)`; `No ArkLib/Data non-sorry warnings found.`; `✓ All imports are up to date!` over `325 imports`; `All documentation integrity checks passed.`; `Knowledge base lint passed.` **Sorry census unchanged** (the M3 diff adds zero `sorry` tokens; no file in the diff gains or loses one). **Zero new long lines** (all four touched files ≤ 100 codepoints per line; note the linter counts codepoints, not bytes — `CWSS/Basic.lean` carries eleven *pre-existing* lines that are >100 **bytes** but ≤ 100 characters, so a byte-based check misreads them as regressions). **Deviations / notes:** (a) 3a additionally re-lands `Verifier.coordinateWiseSpecialSoundWithEscape_false_iff`, which 3a's literal list omits: §4.5's rename table suffixes `*_false_iff` and §1 rule 7 requires every renamed name back under its canonical spelling before M9 deletes the twin. It has no code consumers today (only a docstring mention in `Escape.lean:214`), so this is API completeness, not a new obligation. (b) The `OracleVerifier` mirrors are exactly the six the `*Classical` layer has (`With`, plain, `toCWSS`, `WithEscape`, `Escape`, `toEscape`); the oracle level never carried `withEscape`/`mono`/`_false_iff`/`_iff_exists`, and M3 does not add them. (c) `toShape_arity_pos` is placed inside `namespace CWSSStructure` using the section variable `D` rather than re-binding it, and its `show 0 < D.arity i` is spelled `change` (§9 note 12's style preference); the proof is otherwise the plan's verbatim `rw [congrFun D.arity_eq i]; omega`. (d) Part A's home is a new `section LeafPathGlue` in `Composition.lean` placed **after** `section Membership` — `LeafPath.transcript_embedRight` needs `rightPrefix_concat` and `SplitData.transcript_gluePath` needs `leftPrefix_concat`, both of which live in `Membership`; every statement and proof is the prototype's verbatim, only docstrings were expanded to the file's house style (continuation lines flush-left, as elsewhere in `Composition.lean`). (e) Two docstring updates ride along, both made stale by the code they describe: `Composition.lean`'s `## Main definitions`/`## Main theorems` gain the glue, and `CoordinateWiseSpecialSoundness.lean`'s `Basic` bullet now names the canonical notion instead of only the `*Classical` one. The `Composition`/`NoChallenge` bullets stay on the `*Classical` names — still accurate, those files migrate in M4/M5. (f) `CWSS/Basic.lean` keeps its `noncomputable section` (`:137` region): 3a adds only `Prop`-valued declarations, and the section's deletion belongs to the milestone that cleans the file (M8's sweep). **Abort criteria not triggered:** no transcription failed. §9 note 9's `msg`-capture hazard did not fire (the prototype already spells the message binder `message` in `transcript_embedRight` and `_` in `gluePath`), and note 7's un-beta-reduced-`rw` hazard did not fire (the prototype's `have key … ; rw [hpre] at key ; exact key` route sidesteps it). R1's shape-congruence risk is untouched by M3 — 3a instantiates only the *notion*, not the append theorems, so no `HEq` transport was needed. |
| M4 | pending | | |
| M5 | pending | | |
| M6 | pending | | |
| M7 | pending | | |
| M8 | pending | | |
| M9 | pending | | |

Session-global facts worth one line each as they are learned (record here, not in prose):
the `BASELINE` SHA (also goes in §1 rule 2), the 2a prototype-reproduction choice (§1 rule 3:
re-run at `BASELINE` vs. rename inside `docs/plans/prototypes/`), and any `pureFormOfIsPure`
organic uses found by M9's grep.

- `BASELINE = 329ff98d554bb459892ff5dea99e8c0c6363cea0` (M0 step 1; also recorded in §1 rule 2).
- `ChallengeTree.onlyPath` lives in `TranscriptTree/Basic.lean`, not `NoChallenge.lean` (M0 step 3).
- The import pair that puts `CPolynomial`/`toPoly` in scope without dragging in the cyclotomic
  layer is `CompPoly.Univariate.Basic` + `CompPoly.Univariate.ToPoly`, plus `open … CompPoly`
  (M1; `natDegree_toPoly` additionally needs `CompPoly.Univariate.ToPoly.Impl`, which the two
  `Lift` files do not require but `Hachi/RingSwitch/Reduction.lean` gets transitively).
- Committing is disabled in this environment's agent settings, so each session must hand the
  repository owner its commit commands rather than running them; the milestone's steps are staged
  in order so the split survives (M0). For a multi-step milestone, hand over one patch per step
  plus a script that reverse-applies the later patches to recover each intermediate tree (M2).
- **The §1 rule 3 prototype choice is: patch `docs/plans/prototypes/*.lean`** (not: re-run at
  `BASELINE`), made at M2 step 2a. The prototypes therefore track the repo's current names and stay
  runnable; every milestone that renames a declaration the prototypes import must patch them in the
  same commit and re-run all four.
- The mechanical rename convention for the outgoing layer: `Classical` is suffixed onto the notion
  root **and** onto dotted children / before flat qualifiers
  (`treeSpecialSoundWithClassical.withEscapeClassical`, `treeSpecialSoundWithClassical_congr`);
  package members are renamed by namespace only (M2 step 2a).
- `linter.style.longLine` is active in `lake build`, not only under `--lint`: a rename that
  lengthens names needs a rewrap pass in the same commit (M2).
- `ChallengeTree.IsAccepting` does **not** take `[∀ i, SampleableType (pSpec.Challenge i)]`, so the
  notion-support layer can be kept instance-free by omitting the section variable rather than by
  `omit`-ing per declaration (M2 step 2b; §9 note 8).
- `linter.style.longLine` counts **codepoints, not bytes**. `CWSS/Basic.lean` and the other
  `ℓ`/`≡ᵢ`-heavy files carry lines that a byte-based check (`awk 'length($0)>100'`) reports as long
  and the linter does not; use a codepoint count when checking a diff for new long lines (M3).
- Any milestone that moves a prototype declaration **into** the library must delete the prototype's
  copy in the same commit — the prototypes import the library, so a surviving copy fails with
  `has already been declared` (M0's `onlyPath`, M2's `CM_enginecerts` copy, M3's whole `CM_append`
  Part A). The payoff is free evidence: the prototype's demos and IR gates then run against the
  *library* declarations. 4a should expect the same for Part E's `ChallengeTree.somePath`.
- **M2 step 2b was still uncommitted when M3 started** (`aee95607` = 2a, `424eddf8` = the log,
  `76a3d1ee` = M1's content under the message "milestone 2"). M3's handover therefore commits 2b
  first, using the message from the M2 session's `commit-m2b.sh`, and only then 3a/3b/the log.
