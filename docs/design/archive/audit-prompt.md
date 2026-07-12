# AUDIT REQUEST: Proposed canonical oracle-reduction design for ArkLib

You are auditing a design proposal for ArkLib's new `Interaction` framework (this repo = ArkLib-core-rebuild, branch quang/core-rebuild). Your job: a thorough, adversarial review. Find type-theoretic infeasibilities, security-definition mistakes, protocols that don't fit, composition laws that won't actually be provable in Lean 4, universe problems, migration risks, and blind spots. Be concrete; read the actual code before objecting or approving. Do NOT rubber-stamp: your value is in what the proposal gets wrong or leaves underspecified.

## Background reading (all readable from this sandbox)

Current framework (the thing being refined):
- ArkLib/Interaction/Oracle/Spec.lean — Oracle.Spec free-monad tree, .public/.oracle nodes, PublicTranscript, QueryHandle/toOracleSpec/answerQuery
- ArkLib/Interaction/Oracle/Core.lean — Prover/Verifier/Reduction; note `Verifier.WithMonads.simulate : (shared, pt) → QueryImpl [OStatementOut shared pt]ₒ (OracleComp ([OStatementIn shared]ₒ + (Context shared).toOracleSpec (OracleDeco shared) pt))`
- ArkLib/Interaction/Oracle/Security/Basic.lean — InputImpl (Id-valued), OutputImpl (OracleComp-valued), OutputRealizes, InputRelation/OutputRelation over impls, Straightline extractor
- ArkLib/Interaction/Oracle/Composition.lean — Reduction.comp, retargetMonads, routeLeft/routeMid/routeRight
- ArkLib/Interaction/Oracle/Reification.lean — optional Option-valued reify + correctness; duplicated verifier-side API
- ArkLib/Interaction/Boundary/{Core,Oracle,Reification,OracleSecurity}.lean — lens/boundary layer
- ArkLib/Interaction/Oracle/{Chain,Telescope,BCS}.lean, ArkLib/Interaction/Choreo.lean
- ArkLib/Interaction/Reduction.lean and Security/*.lean — plain layer (has composition security theorems; oracle layer does not)

Old design (main branch, at /Users/quangdao/Documents/Lean/ArkLib) for contrast: ArkLib/OracleReduction/Basic.lean (embed/hEq output; commented-out simOStmt suggestion at lines 277-293), Composition/Sequential/Append.lean (OracleVerifier.append verify = sorry; all 5 append security theorems sorry), LiftContext/Lens.lean (OracleStatement.Lens never figured out).

Prior analyses (read these; you may disagree with them):
- /private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-oracle-sim.md — code-grounded design analysis
- /private/tmp/claude-501/-Users-quangdao-Documents-Lean/bc3013d1-d973-4d8f-bbd7-7cb34fadd1aa/scratchpad/gpt-literature.md — 35-requirement literature catalog
- /Users/quangdao/Documents/paper-note/notes/ArkLib-Refactor_oracle_reduction_as_ior.md — author's design-consensus note (SharedIn spine; impl-based primary; reification optional)
- /Users/quangdao/Documents/paper-note/notes/arklib-ior-knowledge-soundness-survey.md — KS literature survey (extractor signatures in BCS16/BGTZ23/CDHZ 2025-2166/FICS-FACS)
- /Users/quangdao/Documents/paper-note/notes/ArkLib-Refactor_raw_append_spec_exploration.md — Spec.Presentation layer prototype

## THE PROPOSAL UNDER AUDIT

Keep unchanged: Oracle.Spec tree (.public/.oracle), PublicTranscript indexing, SharedIn spine, transcript-indexed output families, plain Reduction layer, execution kernel.

Core change — the canonical output claim of an oracle verifier/reduction becomes a provenance-carrying virtual oracle instead of a detached raw QueryImpl:

```lean
structure VirtualOracle (Src : OracleSources) (Out : OracleFamily) where
  denote : Src.Data → Out.Data          -- mathematical meaning (absorbs Reification.reify, total)
  query  : QueryImpl [Out.Obj]ₒ (OracleComp Src.spec)   -- current `simulate`
  query_correct : ∀ src i q,
    simulateQ (Src.impl src) (query ⟨i, q⟩) = pure (OracleInterface.answer (denote src i) q)

structure OracleClaim (Src) (Stmt : Type) (Out) where
  stmt : Stmt
  oracles : VirtualOracle Src Out
```

where for a reduction at (shared, pt), Src is structurally `inputSources (OStatementIn shared) ++ transcriptSources (Context shared) (OracleDeco shared) pt` — i.e. the existing `[OStatementIn]ₒ + toOracleSpec od pt` sum, recognized as a provenance-bearing source context. Points:

1. Verifier output = one OracleClaim (indexed by PublicTranscript). `Verifier.simulate` becomes projection `.oracles.query`. Construction sites (ofChain, Choreo) supply one claim-producing field instead of separate oStmtResult + simulate.
2. Security relations return to mathematics: OutputRelation : stmt → Out.Data → wit → Prop, evaluated through `denote` under realized environment (concrete input data; Spec.answerQuery on full transcript — always exists since prover physically sends messages). Impl-level relations survive as derived black-box layer with explicit `Respectful` (observational-equivalence-respecting) condition.
3. Composition = VirtualOracle.bind (Kleisli on query, function composition on denote, query_correct via simulateQ_compose), with bind_assoc/bind_id proven once. retargetMonads + routeLeft/Mid/Right become the sequential-composition instance of bind; boundary pullback another instance. Enables an associativity story for Reduction.comp.
4. Lenses: pointer/selection lenses = leaf constructors of virtual oracles; folds/linear combinations/quotients/WHIR constraints = smart constructors proven once. Escape hatch: generic (query plan + denotation + proof) constructor stays canonical; algebraic constructors added on demand — the generality lives in the record, not a closed DSL grammar.
5. Two equalities maintained: extensional (semantics) vs intensional/provenance (compilation cost) — no quotient.
6. Compilation: per-handle decision — inline query plan into next verifier vs materialize (denote) + commit. BCS needs cost/provenance, hence no quotient.
7. Extractor: default gets output query access; full-transcript strength as separately-named stronger variant. Matches BCS16/BGTZ23/CDHZ extractor signatures.
8. Honest prover output unchanged (concrete StatementWithOracles + witness). Completeness compares prover data to verifierClaim.oracles.denote of realized sources; OutputRealizes obligation dissolves into query_correct.
9. Migration order: (i) VirtualOracle+OracleClaim+bind+laws over existing source spec; (ii) merge verifier endpoint, simulate = projection; (iii) rewrite Reduction.comp routing as bind, then state oracle-level security composition theorems; (iv) OutputRelation to data level via denote, impl relations demoted with Respectful; delete duplicated reification; (v) BCS per-handle policy; RBRTE (FICS/FACS Def 4.4) later.

## AUDIT QUESTIONS (address each)

A. Type-theoretic feasibility. Does `denote : Src.Data → Out.Data` typecheck as stated for the actual source context? Src.Data for the transcript part = what exactly — full transcript restricted along pt? Is `Src.Data` even well-defined when input oracles are given only behaviorally (InputImpl : QueryImpl ... Id) in the current soundness games? Universe issues (Oracle.Spec pinned at Type 1)? Does making query_correct intrinsic force DecidableEq or noncomputability anywhere it hurts?
B. Is `denote` total in reality? Reification.lean uses Option — find out why (read the code) and determine whether the proposal's total denote breaks those use cases or whether Option was only an artifact. Are there legit protocols where the output oracle has NO canonical concrete denotation (relational/ideal oracles, degree claims not query-observable, code-proximity claims)? If so, is the escape hatch sufficient or does the core need a weaker/optional denotation after all — and what does that do to the well-definedness argument for relations?
C. Security definitions. Is stating OutputRelation on Out.Data via denote actually equivalent (or safely stronger/weaker) than current impl-level statements for: soundness, knowledge soundness, RBR variants? Does the malicious-prover case really always have a realized source environment (prover sends concrete messages — but input oracles in soundness are quantified how)? Check current Soundness.lean/KnowledgeSoundness.lean quantification precisely.
D. Composition laws. Will bind_assoc actually hold definitionally or only propositionally (simulateQ over reassociated sums; left-associated OracleSpec sums; VerifierAccess "standard left-associated" note)? Does the proposal actually deliver associativity of Reduction.comp, or only of the oracle part while transcript/statement indexing still blocks it (PublicTranscript.split nesting)? What would the honest associativity statement look like?
E. Expressiveness stress-test against protocols: FRI/STIR/WHIR folds & out-of-domain samples, sumcheck claim reduction, Spartan-invoking-sumcheck via lenses, Ligero row checks, Marlin holographic index oracles, Nova/ProtoStar folding (relaxed R1CS, committed instances), batching with shared challenges, virtual polynomials in Binius/Lasso style. Any of these NOT expressible as (denote, query, query_correct) over input+transcript sources? Where do public *scalar* outputs computed from oracle queries (e.g. STIR's shift-check values) live?
F. The Respectful/black-box layer: is keeping impl-level relations as a secondary layer coherent, or does it create two sources of truth that drift? Which one do RBR state functions use?
G. Migration risk & effort: which existing files/theorems break at each step; is the proposed order right; what's the single riskiest step; can step (iii) really delete retargetMonads or does it still need strategy-level monad rewriting for the *interactive* part (not just the output claim)?
H. Anything the proposal misses that the literature catalog (R1-R35) says is essential — esp. provenance-as-DAG vs the proposal's lighter "sources = the sum spec" stance; state-restoration; shared-prefix batching; holographic origins.

## OUTPUT FORMAT

Markdown. Sections: (1) Executive verdict with severity-ranked findings list; (2) per-question A–H analysis with file:line evidence; (3) concrete amendments to the proposal (Lean sketches where relevant); (4) revised migration plan if needed; (5) what you'd cut from the proposal as overengineering, if anything. Write the complete document as your final answer.
