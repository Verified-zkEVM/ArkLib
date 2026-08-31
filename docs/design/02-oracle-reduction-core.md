# 02 — Oracle Reduction Core: Claims, Closing, and Composition

**Normative.** The Δ-side design: what an oracle reduction is, what its output claim is, how claims
close and compose. Supersedes the round-3 document's §§0–6.8 with the round-4 repairs applied; the
raw history remains on the preserved
[`archive/oracle-reduction-v2-pre-split`](https://github.com/Verified-zkEVM/ArkLib/tree/archive/oracle-reduction-v2-pre-split/docs/design/archive)
branch.

## 1. Ontology

An oracle reduction transforms claims about oracles into new claims about (possibly derived) oracles. Four layers, four purposes:

| Layer | Object | Records | Consumed by |
|---|---|---|---|
| backing | `SourceCtx` env/handler | what this execution can query | executor, composer, extractor |
| derived view | `VirtualOracle`; `eval` | typed query program; behavior by interpretation | verifier, composer, compiler |
| relation boundary | `ClosedClaim` | statement + output behavior | relations/games |
| representation | `Materialization`, commitments | concrete storage, binding, cost | honest prover, compiler |

Three objects around any oracle, never conflated: **(1)** concrete data (a polynomial), **(2)** arbitrary behavior (answers to all queries), **(3)** a query program deriving answers from other resources. The verifier defines (3); relations consume (2); the honest prover often has (1). The stable point:

> the plan is the operational representation; behavior is its mathematical meaning; concrete data is an optional witness to that behavior.

**The running example** (one FRI round) and the full motivation (why selection-only and data-only designs fail; the `main`-branch autopsy) are preserved in the archive; the two sentences that matter: a real FRI round contains *both* a derived virtual fold view *and* a fresh prover-sent word `g`, checked against each other by sampling — so output schemas must record which slots are derived and which are fresh; and the old `embed`-only design is why `main` could never state lenses, verifier append, or any composition security theorem.

## 2. Representation-indexed claims

One intended claim shape, three representations (round-4 unification). These snippets are design
equations; exact universes and implicit arguments remain provisional until AR-4A through AR-7 in
`01a` elaborate:

```lean
structure ClaimWith (Rep : OracleFamily → Type) (Stmt : Type) (Out : OracleFamily) where
  stmt    : Stmt
  oracles : Rep Out

abbrev OracleClaim (srcSpec) Stmt Out := ClaimWith (VirtualOracle srcSpec) Stmt Out  -- open
abbrev ClosedClaim Stmt Out          := ClaimWith OracleFamily.Behavior Stmt Out    -- closed
abbrev DataClaim Stmt Out            := ClaimWith (fun O => ∀ i, O.Obj i) Stmt Out  -- honest data
-- HonestProverOutput = DataClaim × Witness
```

Representation morphisms into behavior: `eval` (open → closed, per handler) and `answerData` (data → closed). `ProverOutputRealizes` is the statement that the honest prover's `DataClaim` and the verifier's closed claim map to the same point — naturality, not a bespoke condition. `stmt` is produced by the verifier's own (possibly query-dependent) terminal computation; scalar outputs computed from oracle queries (sumcheck's `Tᵢ := sᵢ(rᵢ)`, STIR shift values) live in `stmt`, never in the oracle component. `stmt` is *run*-determined, not env-determined — the joint execution artifact (`03` §2) ties them; there is no theorem "`ClosedClaim` is a function of `Env`" and none should be attempted.

## 3. Core objects

### 3.1 Families and behavior

```lean
structure OracleFamily where
  ι      : Type
  Obj    : ι → Type
  oracle : ∀ i, OracleInterface (Obj i)

abbrev OracleFamily.Behavior (Out : OracleFamily) := QueryImpl ([Out.Obj]ₒ' Out.oracle) Id
```

(Repair C5: interface instances are explicit structure data; use ArkLib's explicit-instance spec notation `[…]ₒ'` throughout — a structure field is not a typeclass instance.)

Structured semantics is an optional presentation (`SemanticPresentation`: `Sem`, `behavior : Sem → Behavior`), with injectivity (`FaithfulPresentation`) opt-in. Relations authored on a presentation owe behavioral invariance.

### 3.2 Source contexts

```lean
structure SourceCtx where
  ι    : Type
  spec : OracleSpec ι          -- the *signature* (call it srcSpec when passed alone)
  Env  : Type                  -- what realizes it
  impl : Env → QueryImpl spec Id
```

`SourceCtx` is deliberately extensional. Pure `SourceHom` routes handlers and is the only morphism
needed by semantic substitution. A separate `ResourceSchema` records stable identity, origin,
aliasing/sharing, and reified ideal guarantees; each guarantee has a witness connecting its
descriptor to the actual slot object/refined type. `SchemaHom` lies over a `SourceHom` and proves
schema coherence. A later `BackendAssignment` is indexed by the schema. This keeps semantic
substitution independent of compiler metadata without leaving provenance prose-only.

For a reduction at ambient `shared` and branch path `path`, the source context has **three** parts:

```lean
def sourcesAt (shared) (path) : SourceCtx :=
  (setupSources shared).tensor ((inputSources shared).tensor (messageSources shared path))
```

- **Setup part:** preprocessing/indexer oracles, CRS handles, correlated public parameters. Each setup source is classified in the companion `ResourceSchema` as public data (in `shared`), read-only Δ behavior (here), or a persistent Γ runtime (`03` §1). Systems without setup take this part empty.
- **Input part:** `InputImpl` — arbitrary deterministic behavior for the input-oracle interfaces. Soundness quantification is unchanged and unweakened.
- **Execution-path part:** the structural hidden-message fiber

```lean
def Oracle.TypeTree.OracleMessagesAt :
    (s : Oracle.TypeTree) → Oracle.TypeTree.BranchPath s → Type
  | .done, _ => PUnit
  | .public _ rest, ⟨x, tail⟩ => OracleMessagesAt (rest x) tail
  | .oracle X cont, ⟨_, tail⟩ => X × OracleMessagesAt (cont ⟨⟩) tail
```

with `answerAt` (taking the `OracleDeco`) the structural sibling of `answerQuery`. Not "always
inhabited": the correct statement is that **every realized execution path canonically produces
one** — the conversion is the theorem the execution layer exports.

### 3.3 Guarantees travel with oracles (D1 — normative)

Prover-sent oracle message types **may be refined**: sumcheck's round message is `degree ≤ d` polynomials; an IOP proof slot may be typed as a codeword. This is the ideal model working as intended: the verifier can never inspect the underlying object, so the slot's *type is the interface guarantee* — the same way the literature hands the IOP verifier oracles *promised* to satisfy a predicate, with soundness stated against the promise. Consequences:

1. `OracleMessagesAt` stores concrete typed payloads. Malicious execution-path oracle behavior
   ranges over *representable* values of the declared message type. This is faithful to both the
   runtime (the prover physically sends a value) and the textbook (IOP strings are literal strings).
2. Behavior-generality applies where it must: input oracles in games, and closed output claims. A *promise-free* slot is declared by choosing an unrefined message type; the two styles coexist per-slot.
3. **The compiler owes GuaranteeTransport** (`04` §2): each type-level guarantee on an oracle slot becomes, under compilation, an explicit obligation of the commitment scheme's commit/open phases (degree enforcement, proximity testing, well-formedness proofs). A guarantee that no backend can discharge blocks compilation of that slot — by design, loudly.
4. Relations still carry *claim-level* validity (proximity parameters, admissibility); the type carries *slot-level* interface promises. Rule of thumb: if the honest prover establishes it by construction and the ideal verifier consumes it as an interface assumption, it may live in the type; if it is what the protocol *establishes or tests*, it lives in the relation.

### 3.4 Virtual oracles

```lean
structure VirtualOracle (srcSpec : OracleSpec ι) (Out : OracleFamily) where
  query : QueryImpl ([Out.Obj]ₒ' Out.oracle) (OracleComp srcSpec)

def VirtualOracle.eval (v) (ρ : QueryImpl srcSpec Id) : Out.Behavior :=
  fun q => simulateQ ρ (v.query q)
```

No stored denotation, no stored coherence: `eval` *is* the denotation; smart constructors ship `eval`-simplification lemmas; coherence is by construction. This is the algebraic-effects reading of the existing `simulate` field — `OracleComp` the free program, handlers the models, `simulateQ` interpretation, substitution handler-composition.

### 3.5 Closing

```lean
def OracleClaim.closeWith (c) (ρ : QueryImpl srcSpec Id) : ClosedClaim Stmt Out :=
  ⟨c.stmt, c.oracles.eval ρ⟩
```

`closeWith` is a semantic helper. Games never let a prover pair an arbitrary claim with an unrelated handler: the **joint execution artifact** (`03` §2) produces the claim and its closing handler together, and closing is a projection. (Round-4 repair C1/C2: the former `AcceptedRun`/`runClosed` sketches are replaced by the artifact; both were untyped as written — the branch-path index, prover payload, and Γ trace all live in the artifact.) Closing forgets the *presentation*, never needed resources: anything a later stage needs is an exported output slot (identity view); a fused implementation may optimize through old sources beneath the interface.

## 4. Constructors

Minimal set: `id`/passthrough, `reindex`, `tensorWeaken`, `rebase`, `subst`, and the escape hatch `ofQuery`. Algebraic constructors (`linComb`, `fold`, `quotient` with its validity predicate in the relation) land when a protocol port first needs them, each with its `eval` lemma and, where applicable, a `Materialization`. Boundaries ("lenses", historically): projection direction = a virtual view + `subst`; reverse direction = materialization/witness transport with its own coherence — call them dependent refinement boundaries unless lens laws are actually proved.

## 5. Composition

Handler substitution with explicit interfaces:

```lean
def SourceCtx.tensor (S T : SourceCtx) : SourceCtx          -- disjoint sources
def OracleFamily.asSource (A : OracleFamily) : SourceCtx    -- Env := A.Behavior, impl := id

def VirtualOracle.subst
    (v : VirtualOracle S.spec A)
    (w : VirtualOracle (A.asSource.tensor T).spec B) :
    VirtualOracle (S.tensor T).spec B

theorem eval_subst : (subst v w).eval (ρS + ρT) = w.eval (v.eval ρS + ρT)
```

Stage two sees the *declared middle interface* (`A.asSource` — behavior only) plus its own suffix resources; never stage one's hidden environment. Sharing/renaming/weakening are explicit context morphisms; duplicating a handle is contraction along a resource identity, not tensoring. Laws (`subst_assoc`, identities) are stated up to `SourceEquiv` (spec iso + env equiv + naturality), under **two named equivalences**: `≈sem` (same behavior under every handler) and `≈op` (typed trace equivalence preserving order/multiplicity/cost). Semantic laws need `≈sem`; compiler theorems need `≈op`, witnessed through VCVio runtime artifacts and resource transport. **Reduction-level operational associativity is not promised.** A three-stage client first uses PolyFun's existing `TypeTree.Chain.then`, path equivalence, and `reassoc` laws. Only a concrete failure of that API justifies a smaller upstream extension; a new presentation datatype remains the last fallback.

What `subst` does *not* subsume: interactive-phase monad retargeting (`retargetMonads` / `retargetAmbientWithRoute`) remains — it rewrites receiver-node access during interaction, not terminal claims. Sequential execution decomposition must be proved order-preserving (no generic commutativity for `OracleComp` worlds); the commutative-monad proof from the plain layer is scoped to the pure stateless case.

Deliberately separate (not `subst`): shared-prefix products, lock-step repetition, batched shared challenges — later combinators with their own challenge scoping.

## 6. Core security shape (Δ side; games live in 03)

```lean
structure ClaimSchema where
  PublicCtx : Type
  Claim     : PublicCtx → Type

structure Problem (S : ClaimSchema) where
  Witness        : ∀ ctx, S.Claim ctx → Type      -- claim-dependent (committed relations!)
  admissible     : ∀ ctx, S.Claim ctx → Prop
  rel            : ∀ ctx claim, Witness ctx claim → Prop
  rel_admissible : ∀ ctx claim wit, rel ctx claim wit → admissible ctx claim

def Problem.language (P) (ctx) (claim) : Prop := ∃ w, P.rel ctx claim w
abbrev Relation (S) := { P : Problem S // P.admissible = fun _ _ => True }  -- promise-free
```

(Repair C4: one object; `Relation` is the degenerate case; oracle schemas are the specialization `Claim ctx := ClosedClaim (Stmt ctx) (Out ctx)`.) Relations receive public context, a **closed claim**, and a witness — never the environment, the plan, or provenance. `admissible` covers promises, well-formedness, size bounds, and accumulator invariants (input promise / output-admissibility obligation / inductive invariant are different *proof roles* of the same mechanism, kept as named aliases). Impl-facing predicates are **generated adapters** by evaluation + closing; legacy handwritten predicates owe a two-way equivalence proof, per protocol (repair C6 — there is no generic bridge, and the legacy namespace survives until every consumer is bridged).

Completeness = statement agreement + `ProverOutputRealizes` + `rel_out` on the closed claim; the old `OutputRealizes` is a derived interpreter lemma; literal data equality only under `Faithful` interfaces. Soundness/KS/RBR games, extractors, outcomes (`accept/reject/fault`), and error accounting are `03`'s subject — they require the execution layer.

## 7. Materialization

```lean
structure Materialization (Src : SourceCtx) (v : VirtualOracle Src.spec Out)
    (ConcreteSrc OutData : Type) where
  forget      : ConcreteSrc → Src.Env
  materialize : ConcreteSrc → OutData
  answerData  : OutData → Out.Behavior
  correct     : ∀ src, answerData (materialize src) = v.eval (Src.impl (forget src))
-- ExecutableMaterialization extends it with cost.
```

Total (all real uses in the repo are); never load-bearing for security; the honest home of the two retired reification APIs; the attachment point for L6 refinement work.

## 8. Universe and notation discipline

Pinned universes matching the current stack (`Oracle.TypeTree : Type 1`, families in `Type`,
`OracleSpec.{0,0}`); polymorphization is a tracked follow-up. Naming: `srcSpec` for bare
signatures, `Src : SourceCtx` for contexts; `OStatementIn/Out` spellings per the consensus note;
declaration-name references, not line numbers.
