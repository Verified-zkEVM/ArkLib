# Hachi Sumcheck Track — Implementation Plan: B4 → F2 → F3 → F4

Sequential, implementation-ready plan for the first four milestones of the sumcheck track of
[`HACHI_RING_SWITCHING_PLAN.md`](HACHI_RING_SWITCHING_PLAN.md) (v2). Every anchor below was
re-verified against the working tree on **2026-07-10**; where v2's anchors are stale (the
QuadEval layer moved to `Hachi/QuadEval/` + `Hachi/Composition.lean` and grew the
`CWSSPackage`/`▷` idiom), this file supersedes them. Paper: Hachi (NOZ26, ePrint 2026/156).

Scope: **B4** (guarded CWSS composition), **F2** (Eq. (20) → `R^lin` adapter), **F3**
(quotient-lift algebra), **F4** (HMZ25 lift, Fig. 4 / Lemma 9). Out of scope, unchanged from v2:
knowledge-error accounting, Fiat–Shamir, completeness beyond prover skeletons (D12/R6), and
anything oracle-verifier-level (see G4).

---

## 0. Verified current state (the substrate these milestones build on)

### 0.1 The finished chain and its composition idiom

- `CWSSPackage` ([Package.lean:54](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean#L54)):
  bundles `verifier`, `struct : CWSSStructure`, `relIn`, `relOut`, **`isPure`**, `isCWSS`.
  Composition `CWSSPackage.append` = infix `▷` (:79-102), seam `hseam : L₁.relOut = L₂.relIn`
  discharged **by `rfl`** — so every new stage must define its `relIn` as *literally the same
  term* as its predecessor's `relOut`.
- Finished chain `evalChain = bridgePackage ▷ quadEvalPackage`
  ([Composition.lean:117](ArkLib/Commitments/Functional/Hachi/Composition.lean#L117)), theorem
  `eval_coordinateWiseSpecialSound` (:138). The TODO block (:155-165) reserves exactly this
  track's slot: *"§4.3 Eq.(20) ⇒ R^lin ⇒ HMZ25 lift ⇒ …"* and *"Guarded subprotocols need a
  guarded variant of `▷`"* (that variant is B4.6).
- QuadEval: statement/response/witness at
  [QuadEval/Reduction.lean:68/84/100](ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L68);
  `relOut` (Eq. (20) + ranges) at :199-223; `relIn` (with the `opening/msisB/msisD` escape
  cases) at :229-239. The extraction core is factored as the standalone lemma
  **`buildWitness_mem_relIn`**
  ([QuadEval/Soundness.lean:386](ArkLib/Commitments/Functional/Hachi/QuadEval/Soundness.lean#L386))
  — F2.0 reuses it verbatim (no edits to done proofs).

### 0.2 CWSS framework facts that fix B4's design

- Verifier monad is **`OptionT (OracleComp oSpec)`**
  ([OracleReduction/Basic.lean:243-245](ArkLib/OracleReduction/Basic.lean#L243)) — `failure` is
  native; no new machinery needed to *express* a guarded verifier.
- Acceptance is probability-phrased: `IsAccepting … = ∀ tr ∈ tree.fullTranscripts, Pr[…] = 1`
  ([TranscriptTree/Basic.lean:252-257](ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean#L252)).
- Purity is load-bearing in exactly **two** places:
  `append_run_pure_left` ([Composition.lean:311](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L311))
  and `pure_accepting_of_mem` (:325) / `mem_of_pure_accepting`
  ([SeqCompose.lean:53](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SeqCompose.lean#L53)).
  B4 = guarded analogues of these two + re-running the (structurally unchanged) append/seqCompose
  proofs ([Composition.lean:366-428](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L366),
  [SeqCompose.lean:364-404](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SeqCompose.lean#L364)).
- The no-challenge bridge is already failure-tolerant (probability-phrased hypothesis,
  [NoChallenge.lean:104-127](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/NoChallenge.lean#L104)).
- `CWSSStructure.ofSpecialSound k` ([Basic.lean:181](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L181))
  and `isSpecialSoundFamily_one_iff_injective` (:111) give the `ℓ = 1` currency F4 needs.
- `CoordinateWise.SingleRound` is pinned to `(ℓ, k) = (2^r, 2)` with vector challenges
  ([SingleRound.lean:51,231,370](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L51));
  F4.1 builds its scalar-`k` twin.
- **`OracleVerifier.append` is `sorry`**
  ([Composition/Sequential/Append.lean:149](ArkLib/OracleReduction/Composition/Sequential/Append.lean#L149))
  → G4 below.

### 0.3 Lattice/algebra facts that fix F3's design

- `Rq Φ = {p : CPolynomial R // Φ.reduce p = p}` ([Rq.lean:77](ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L77));
  `reduce = modByMonic Φ.φ` ([Core/Basic.lean:67](ArkLib/Data/Lattices/CyclotomicRing/Core/Basic.lean#L67));
  `equivQuotient : Rq Φ ≃+* Φ.CyclotomicRing` ([Rq.lean:209](ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L209));
  `quotientHom_apply`, `quotientHom_reduce` ([Core/Basic.lean:86/91](ArkLib/Data/Lattices/CyclotomicRing/Core/Basic.lean#L86)).
  The quotient-witness identity is already in the tree:
  `Polynomial.modByMonic_eq_sub_mul_div` is invoked at Core/Basic.lean:97, and
  `Rq.toQuotient_injective` ([Rq.lean:107](ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L107)) does
  the degree-forcing argument. Degree bound on representatives: `natDegree_val_toPoly_lt`
  ([Rq.lean:298](ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L298)).
- Interpolation kernel exists in pinned Mathlib:
  `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` (+ `'` Finset form),
  `.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Roots.lean:690/718`.
- Vectors: `PolyVec P k = Fin k → P`, `PolyMatrix = Matrix (Fin r) (Fin c) P`, **custom
  computable** `dot`/`*ᵥ`/`matMul` (NOT `Matrix.mulVec`), `dot_eq_sum`, `matVecMul_matMul`,
  `flattenBlocks` ([Vectors.lean:39-179](ArkLib/Data/Lattices/Vectors.lean#L39)).
- Norms used by `relOut` c6: `vecLInftyNorm`
  ([NormBounds/Basic.lean:95](ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L95)) —
  not `cInfNorm`.
- Base-`b` digits: `DigitDecomposition` / `zmodDigitDecomposition` / `gadgetDecompose`
  ([Hachi/Gadget/Basic.lean:95/113/207](ArkLib/Commitments/Functional/Hachi/Gadget/Basic.lean#L95)).
- No lift/HMZ25 formalization exists anywhere (grep-verified) — F3 is greenfield.

### 0.4 Protocol-spec facts that fix F4's shape

- 2-round pSpec idiom: `⟨!v[.P_to_V, .V_to_P], !v[Msg, Chal]⟩`
  ([SingleRound.lean:51](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L51));
  per-index instances by `| ⟨0,h⟩ => nomatch h | ⟨1,_⟩ => infer_instance` matching
  ([Sumcheck/Structured/SingleRound.lean:106-116](ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L106)).
- Pass-through verifier idiom: `fun stmt tr => pure (stmt, tr.messages ⟨0,rfl⟩, tr.challenges ⟨1,rfl⟩)`
  ([QuadEval/Reduction.lean:251](ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L251));
  prover skeleton with `computeV`/`computeResp` params (:265-298).
- `SampleableType`: `FinEnum (ZMod n)` instance exists (VCVio `SampleableType.lean:332`), so
  `SampleableType (ZMod q)` is derivable; for an abstract field take `[SampleableType F]` as a
  hypothesis (v2's D10).
- Weak binding: `VerifiedOpening` / `outputToModuleSIS_valid_of_verified`
  ([InnerOuter/Security.lean:163/332](ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L163)) —
  the pattern (not necessarily the instance) F4's collision escape follows.

---

## 1. Global design decisions (new in this plan; supersede v2 where they conflict)

**G1 — Escape threading via `⊕` (the one v2 under-specified point).** Once F4's extractor can
hit a *binding break of the new `w̃`-commitment*, that escape must flow **backwards** through
every seam up to the chain head (composed extraction: `E₂` feeds `E₁`). Today's
`relOut`/`relRlin` seams have no home for it. Fix: thread a single **escape budget type** `E`
through the chain as a plain `Sum`:

```lean
-- sketch (F2.0); Set.withEscape is ~5 lines
def Set.withEscape (rel : Set (S × W)) (esc : Set E) : Set (S × (W ⊕ E)) :=
  {p | match p with
       | (s, .inl w) => (s, w) ∈ rel
       | (_, .inr e) => e ∈ esc}
```

Crucially `esc` is **statement-independent** (an MSIS/collision solution is checkable against
the parametric commitment key alone), so pass-through across statement maps is trivial. The
threaded variants of the finished theorems are built in **new files** by wrapping the exported
extraction cores (`buildWitness_mem_relIn`, `ReduceClaim.verifier_coordinateWiseSpecialSound`)
— zero edits to sorry-free proofs. Concrete instantiation: `E := LiftEscape` (F4.2).

**G2 — the `w̃`-commitment key is a *parameter*, not a statement field.** `ReduceClaim.mapStmt`
is a pure function `StmtIn → StmtOut`, so F2 cannot conjure a fresh commitment key into the
`R^lin` statement. Instead the key rides as a section `variable` of the F2/F4 files (repo
precedent: relations already take `base ω γ` as plain arguments). F4's verifier never reads it
(pure pass-through); only the relations do.

**G3 — guards are `Bool`-valued.** `Verifier.IsGuardedWith V check verify` with
`check : StmtIn → FullTranscript pSpec → Bool` and body
`if check s tr then pure (verify s tr) else failure`. Consumers with decidable Prop checks use
`decide`. Purity is the `check := fun _ _ => true` special case.

**G4 — plain `Verifier` only.** `OracleVerifier.append` is sorried; all B4/F2/F4 statements stay
at the plain-`Verifier` level (exact precedent: the comment before `quadEvalPackage`,
Soundness.lean:451-453). Oracle wrappers are deferred, tracked in the B4 file header.

**G5 — field abstraction (v2's D10, made concrete).** F3/F4 are stated over
`{F : Type} [Field F]` plus an embedding `φF : ZMod q →+* F` (injective for free:
`RingHom.injective` from a field domain) and `[SampleableType F]` where challenges are drawn.
No dependence on `fixedSubring`/`GaloisField`/`no_selfReciprocal_factor`.

**G6 — seams are definitional.** Because `▷`'s `hseam` is by `rfl`, each milestone *exports* its
`relOut` as a named `def` and the next milestone's `relIn` *is that name*. Never restate a seam
relation.

**Standing hypotheses** (unchanged from v2's D11): `[Fact (Nat.Prime q)]`, `Φ := 𝓜(q, α)` with
`1 ≤ α` (so `d = 2^α ≥ 2`), plus `hq5 : q % 8 = 5`, `hκ : (2ω)² < q`, `hτ : 0 < zDigits`
wherever the QuadEval layer is consumed.

**Validation protocol per milestone** (CLAUDE.md guardrails): `git add` new files, then
`./scripts/validate.sh` (add `--lint` before PR); never hand-edit `ArkLib.lean`; update
`docs/wiki/repo-map.md` in the same PR that creates a new directory.

---

## 2. Milestone B4 — guarded CWSS composition (~2.5–3.5 d)

**Goal.** `append`/`seqCompose` CWSS theorems whose *left* factors may reject at runtime, plus
the guarded `▷`. Generic security infrastructure — **coordinate with maintainers before
starting** (v2's R3); no existing theorem changes byte-wise.

**New file** `ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean`
(imports `Composition`, `SeqCompose`, `Package`).

### B4.1 The guard predicate and rejection lemmas (0.5 d)

```lean
-- sketches; binders as in Composition.lean's section variables
def Verifier.IsGuardedWith (V : Verifier oSpec StmtIn StmtOut pSpec)
    (check : StmtIn → FullTranscript pSpec → Bool)
    (verify : StmtIn → FullTranscript pSpec → StmtOut) : Prop :=
  ∀ stmt tr, V.verify stmt tr = if check stmt tr then pure (verify stmt tr) else failure

class Verifier.IsGuarded (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop where
  is_guarded : ∃ check verify, V.IsGuardedWith check verify

instance : V.IsPure → V.IsGuarded          -- check := fun _ _ => true
```

Rejection lemma (the guarded half of `pure_accepting_of_mem`'s dichotomy):

```lean
theorem Verifier.failure_not_accepting (lang : Set StmtOut) :
    Pr[(· ∈ lang) | OptionT.mk do
      (simulateQ impl ((failure : OptionT (OracleComp oSpec) StmtOut)).run' (← init))] = 0
```

*Proof plan:* the computation's support contains no `some` outcome; unfold as in
`pure_accepting_of_mem`'s step (a) (Composition.lean:333-362) with `simulateQ_failure` /
`OptionT.run_failure` simp lemmas in place of `simulateQ_pure`. Then the two directional
workhorses (both ~10-line wrappers over the existing pure lemmas after an `if`-split):

```lean
theorem Verifier.guarded_accepting_of_mem (hV : V.IsGuardedWith check verify)
    (hcheck : check stmt tr = true) (hout : verify stmt tr ∈ lang) : Pr[…] = 1
theorem Verifier.check_eq_true_of_guarded_accepting (hV : V.IsGuardedWith check verify)
    (hacc : Pr[…] = 1) : check stmt tr = true
theorem Verifier.mem_of_guarded_accepting … : verify stmt tr ∈ lang
    -- mirrors mem_of_pure_accepting (SeqCompose.lean:53-84), incl. its nonempty-init-support step
```

### B4.2 Guarded left-run lemma (0.25 d)

```lean
theorem Verifier.append_run_guardedLeft (hV₁ : V₁.IsGuardedWith check₁ verify₁) :
    (V₁.append V₂).run stmt (tr₁ ++ₜ tr₂) =
      if check₁ stmt tr₁ then V₂.run (verify₁ stmt tr₁) tr₂ else failure
```

*Proof plan:* mirror `append_run_pure_left` (Composition.lean:311-319): `simp [Verifier.append_run,
Verifier.run, hV₁]`, split the `if`; the `false` branch is `failure_bind`.

### B4.3 Guarded append theorem (1–1.5 d; the core)

```lean
theorem Verifier.append_treeSpecialSound_of_guardedLeft
    (hV₁ : V₁.IsGuardedWith check₁ verify₁)
    (h₁ : V₁.treeSpecialSound init impl S₁ rel₁ rel₂)
    (h₂ : V₂.treeSpecialSound init impl S₂ rel₂ rel₃) :
    (V₁.append V₂).treeSpecialSound init impl (S₁.append S₂) rel₁ rel₃

theorem Verifier.append_coordinateWiseSpecialSound_of_guardedLeft
    (D₁ : CWSSStructure pSpec₁) (D₂ : CWSSStructure pSpec₂) … -- same corollary shape as :414-428
```

*Proof plan* — transplant Composition.lean:366-407 with two deltas:
1. Where the pure proof rewrites the composed run via `append_run_pure_left`, use
   `append_run_guardedLeft` and case-split on `check₁`. In the `false` branch the composed run
   is `failure`, so the leaf's acceptance (`Pr = 1`) contradicts `failure_not_accepting`
   (`Pr = 0`, and `0 ≠ 1`) — the branch is vacuous. Every surviving leaf has `check₁ = true`
   and the proof is *literally* the pure proof from there.
2. Where the pure proof certifies each left-leaf output in `rel₂.language` via
   `pure_accepting_of_mem`, use `guarded_accepting_of_mem` fed by the `check₁ = true` fact of
   delta 1 (the tree machinery — `appendSplit`, `appendSplit_fst_isStructured`,
   `appendSplit_sndAt_isStructured`, `appendSplit_fullTranscripts_append_of_mem` — is untouched).

Watch: each left leaf needs *some* suffix transcript to learn `check₁ = true` from; that is the
same nonemptiness the pure proof already extracts via `LeafPath.exists_of_mem_fullTranscripts`
(used at Composition.lean:393). No new tree lemma expected.

### B4.4 Guarded n-ary composition (0.5 d)

```lean
theorem Verifier.seqCompose_treeSpecialSound_of_guarded
    (hV : ∀ i, (V i).IsGuarded) …    -- otherwise verbatim SeqCompose.lean:364-386
theorem Verifier.seqCompose_coordinateWiseSpecialSound_of_guarded …
```

*Proof plan:* same induction as SeqCompose.lean:364-386 (base `Verifier.id` is pure hence
guarded; step uses B4.3 with `(hV 0).is_guarded`). Also the closure lemma the induction needs:

```lean
theorem Verifier.IsGuarded.append : V₁.IsGuarded → V₂.IsGuarded → (V₁.append V₂).IsGuarded
-- composite check := fun s tr => check₁ s tr.fst && check₂ (verify₁ s tr.fst) tr.snd
```

(mirror of `IsPure.append`, [IsPure.lean:37](ArkLib/OracleReduction/Composition/Sequential/IsPure.lean#L37)).

### B4.5 Guarded package and `▷ᵍ` (0.5 d)

```lean
structure GCWSSPackage … where          -- CWSSPackage with isPure ↝ isGuarded
  verifier … struct … relIn … relOut …
  isGuarded : verifier.IsGuarded
  isCWSS : …

def CWSSPackage.toGuarded : CWSSPackage … → GCWSSPackage …
def GCWSSPackage.append (L₁ L₂ : GCWSSPackage …) (hseam := by rfl) : GCWSSPackage …
scoped infixr:65 " ▷ᵍ " => GCWSSPackage.append
```

`GCWSSPackage.append` mirrors Package.lean:79-97 with B4.3/B4.4's theorem and `IsGuarded.append`.
This discharges the Hachi TODO's "guarded variant of `▷`" (Composition.lean:163).

### B4 acceptance

- `Guarded.lean` compiles sorry-free; `./scripts/validate.sh` green; existing files byte-identical.
- A minimal `example`: a 1-message guarded verifier (`check := fun s tr => decide (tr 0 = s)`,
  over `⟨!v[.P_to_V], !v[Nat]⟩`) `▷ᵍ`-composed with a pure identity package, its CWSS certificate
  obtained via the no-challenge bridge + B4.3.
- File-header note: oracle-level composition deferred (G4); `docs/wiki/repo-map.md` updated.

---

## 3. Milestone F2 — Eq. (20) → `R^lin` adapter (~3–4.5 d, incl. F2.0)

**Goal.** A zero-round `ReduceClaim` package `rlinPackage` with
`relIn = relOutE (QuadEval, escape-threaded)` and `relOut = relRlinE`, `▷`-appended onto the
(escape-threaded) finished chain. New directory
`ArkLib/Commitments/Functional/Hachi/LinSumcheck/` (F2, F4, and later F5–F9 live here).

### F2.0 Escape threading (1–1.5 d) — `LinSumcheck/Escape.lean`

Per G1. Deliverables:

1. `Set.withEscape` (+ 3 simp lemmas: `mem_withEscape_inl/inr`, `withEscape_language`), placed
   in the CWSS folder (it is protocol-agnostic): new small file
   `CoordinateWiseSpecialSoundness/Escape.lean`, or the top of `LinSumcheck/Escape.lean` if
   maintainers prefer zero framework surface — decide at PR time, default the former.
2. Threaded ReduceClaim: **no new framework lemma** — instantiate the existing
   `ReduceClaim.verifier_coordinateWiseSpecialSound`
   ([ReduceClaim.lean:186](ArkLib/ProofSystem/Component/ReduceClaim.lean#L186)) at witness types
   `WitIn ⊕ E` / `WitOut ⊕ E` with `mapWitInv' := Sum.map (mapWitInv s) id` and the case-split
   `hRel`.
3. Threaded QuadEval, in `LinSumcheck/Escape.lean` (all *new* declarations):

```lean
def relInE  (esc : Set E) := (relIn Φ base βSq γ κ).withEscape esc      -- witness: QuadEvalWitness ⊕ E
def relOutE (esc : Set E) := (relOut Φ base ω γ).withEscape esc         -- witness: QuadEvalResponse ⊕ E

noncomputable def buildWitnessE … :        -- branch responses now `QuadEvalResponse ⊕ E`
  (Fin (2^r + 1) → QuadEvalResponse … ⊕ E) → … → QuadEvalWitness … ⊕ E
-- if ∃ j, resp j = .inr e (pick least j): output .inr e; else delegate to buildWitness

theorem buildWitnessE_mem_relInE …        -- hmk: escape branch = pass-through (relOutE gives e ∈ esc);
                                          -- all-inl branch = `buildWitness_mem_relIn` verbatim
theorem quadEval_coordinateWiseSpecialSound_withEscape …   -- via coordinateWiseSpecialSound_of_mkWitness
def quadEvalPackageE … : CWSSPackage … ; def bridgePackageE … ; def evalChainE := bridgePackageE ▷ quadEvalPackageE
```

*Proof plan for the hmk:* case-split on `∃ j, (resp j).isRight`. Escape case: the chosen
branch's `relOutE`-membership is exactly `e ∈ esc`, and `relInE`'s `.inr` case is the same
`e ∈ esc` — done. All-`inl` case: strip the `Sum.inl`s and apply `buildWitness_mem_relIn`
unchanged. `Nonempty (QuadEvalWitness … ⊕ E)` from the existing `Nonempty` instance via `.inl`.

*Faithfulness note:* `relInE/relOutE` at `E := Empty` are equivalent to `relIn/relOut` — state
this as two one-line lemmas so nothing is lost.

### F2.1 Block-vector/matrix helpers (0.5–1 d) — extend `ArkLib/Data/Lattices/Vectors.lean`

All generic over `[NonUnitalNonAssocSemiring P]` (or whatever `dot` currently assumes):

```lean
def PolyVec.finAppend (u : PolyVec P a) (v : PolyVec P b) : PolyVec P (a + b) := Fin.append u v
def PolyMatrix.stackRows (M₁ : PolyMatrix P n₁ c) (M₂ : PolyMatrix P n₂ c) : PolyMatrix P (n₁+n₂) c
  -- Fin.addCases on the row index
def PolyMatrix.pasteCols (M₁ : PolyMatrix P n c₁) (M₂ : PolyMatrix P n c₂) : PolyMatrix P n (c₁+c₂)
def vecMatMul (u : PolyVec P n) (M : PolyMatrix P n c) : PolyVec P c   -- row-vector · matrix

theorem dot_finAppend  : dot (finAppend u₁ u₂) (finAppend v₁ v₂) = dot u₁ v₁ + dot u₂ v₂
theorem matVecMul_stackRows : (stackRows M₁ M₂) *ᵥ v = finAppend (M₁ *ᵥ v) (M₂ *ᵥ v)
theorem matVecMul_pasteCols : (pasteCols M₁ M₂) *ᵥ (finAppend v₁ v₂) = M₁ *ᵥ v₁ + M₂ *ᵥ v₂
theorem dot_matVecMul : dot u (M *ᵥ v) = dot (vecMatMul u M) v        -- splitForm associativity
```

`dot_finAppend` reduces via `dot_eq_sum` (Vectors.lean:112) + `Fin.sum_univ_add`. Also the norm
splitter in `NormBounds/Basic.lean`:

```lean
theorem vecLInftyNorm_finAppend :
    vecLInftyNorm Φ (finAppend u v) = max (vecLInftyNorm Φ u) (vecLInftyNorm Φ v)
```

and two rewriting lemmas in `QuadEval/Gadgets.lean`'s namespace (new file
`LinSumcheck/Rows.lean` if maintainers prefer not to touch Gadgets.lean):

```lean
theorem tensorG1_eq_dot_vecMatMul : tensorG1 Φ base δ c x = dot (vecMatMul c (gadgetMatrix …)) x
theorem tensorG_eq_matVecMul_flattenBlocks :
    tensorG Φ base k δ c x = (tensorGMatrix Φ base k δ c) *ᵥ PolyVec.flattenBlocks x
  -- tensorGMatrix := the k × (blocks·k·δ) block-row [c₁·G | … | c_{2^r}·G], defined via finProdFinEquiv
```

**Convention pin (v2's A1/R4, scoped down):** one `example` block with `decide` fixing the
`Fin.addCases` orientation of `stackRows`/`finAppend` and the `finProdFinEquiv` block order of
`flattenBlocks` at a `2×2` toy instance. Do this *first*; never resolve an index cast mid-proof.

### F2.2 `RlinStatement`, `relRlin(E)`, the adapter (1.5–2 d) — `LinSumcheck/Rlin.lean`

Column layout of the stacked witness `ζ := ŵ ++ flatten t̂ ++ ẑ`, row layout c1–c5:

```
μ := (2^r · messageDigits) + (2^r · (innerRows · innerDigits)) + ((2^m · messageDigits) · zDigits)
n := dRows + (outerRows + (1 + (1 + innerRows)))            -- fix associativity once, in this order

           ŵ                    flatten t̂            ẑ                    rhs
c1   [ D                    |  0                 |  0            ]   =    v
c2   [ 0                    |  B                 |  0            ]   =    u
c3   [ (bᵀG_{2^r,δ}) row    |  0                 |  0            ]   =    y
c4   [ (cᵀ⊗G₁) row          |  0                 | −(aᵀG_{2^m}J) ]   =    0
c5   [ 0                    |  tensorGMatrix c   | −(A·J)        ]   =    0
```

```lean
structure RlinStatement (Φ) (n μ : ℕ) where
  M     : PolyMatrix (Rq Φ) n μ
  yvec  : PolyVec (Rq Φ) n
  bound : ℕ

def relRlin : Set (RlinStatement Φ n μ × PolyVec (Rq Φ) μ) :=
  {p | p.1.M *ᵥ p.2 = p.1.yvec ∧ vecLInftyNorm Φ p.2 ≤ p.1.bound}
def relRlinE (esc : Set E) := relRlin.withEscape esc

def rlinStmt (X : QuadEvalStatement … × CarrierCom Φ dRows × (Fin (2^r) → ShortChallenge Φ ω)) :
    RlinStatement Φ n μ     -- assemble via stackRows/pasteCols; bound := γ
def unstack : PolyVec (Rq Φ) μ → QuadEvalResponse …   -- Fin.addCases splits + finProdFinEquiv un-flatten
```

Key lemma (state as an **iff** — the `→` direction is F2's pull-back, the `←` direction is the
honest-prover side needed later):

```lean
theorem mem_relRlin_iff_mem_relOut :
    (rlinStmt X, ζ) ∈ relRlin ↔ (X, unstack ζ) ∈ relOut Φ base ω γ
```

*Proof plan:* `matVecMul_stackRows` + `matVecMul_pasteCols` split `Mζ = yvec` into five
`finAppend`-component equations; c3/c4 via `dot_matVecMul`/`tensorG1_eq_dot_vecMatMul`; c5 via
`tensorG_eq_matVecMul_flattenBlocks` + `matVecMul_matMul` (for `A·J`); move `−` blocks across
(`sub_eq_zero`); the norm conjunct by `vecLInftyNorm_finAppend` (`max ≤ γ ↔` three `≤ γ`);
`unstack ∘ stack = id` component lemmas from the F2.1 convention pins. This is pure index
bookkeeping — the budgeted risk item (R-F2 below).

Package and composition:

```lean
def rlinPackage … : CWSSPackage init impl
    (QuadEvalStatement … × CarrierCom … × (Fin (2^r) → ShortChallenge …)) (QuadEvalResponse … ⊕ E)
    (RlinStatement Φ n μ) (PolyVec (Rq Φ) μ ⊕ E) !p[] :=
  -- ReduceClaim.verifier (mapStmt := rlinStmt); struct := CWSSStructure.ofIsEmpty
  -- isCWSS via ReduceClaim.verifier_coordinateWiseSpecialSound,
  --   hRel := Sum-case-split: .inl from (mem_relRlin_iff_mem_relOut).mp; .inr pass-through
def evalRlinChain := evalChainE ▷ rlinPackage
theorem evalRlin_coordinateWiseSpecialSound := evalRlinChain.isCWSS
```

### F2 acceptance

- `Escape.lean`, `Rlin.lean` (+ `Rows.lean`, Vectors additions) compile sorry-free;
  `evalRlin_coordinateWiseSpecialSound` end-to-end from `relPolyEvalE` to `relRlinE`.
- The `E := Empty` degeneration lemmas compile.
- `decide` convention examples compile; validate.sh green; repo-map entry for `LinSumcheck/`.

---

## 4. Milestone F3 — quotient-lift algebra (~2–3 d)

**Goal.** The generic `Rq ↔ (ZMod q)[X] ↔ F` bridge Lemma 9 consumes. **New file**
`ArkLib/Data/Lattices/CyclotomicRing/QuotientLift.lean` (generic over `R` where possible; no
Hachi imports — this is reusable, LatticeFold-adjacent material). Everything below is stated
against `Polynomial R` via `(a : Rq Φ).1.toPoly`; write the one-line abbreviation
`Rq.rep (a : Rq Φ) : Polynomial R := a.1.toPoly` first and use it throughout.

### F3.1 Scalar quotient-witness lemma (0.5–1 d)

```lean
-- d := Φ.φ.toPoly.natDegree (= 2^α for powTwoCyclotomic); hypothesis hd : 2 ≤ d
theorem exists_quotient_witness_of_quotient_eq
    (hS : S.natDegree ≤ 2*d - 2) (hy : y.natDegree < d)
    (h : Ideal.Quotient.mk Φ.modIdeal S = Ideal.Quotient.mk Φ.modIdeal y) :
    ∃ ρ : Polynomial R, ρ.natDegree ≤ d - 2 ∧ S = y + Φ.φ.toPoly * ρ

theorem quotient_eq_of_eq_add_mul   -- the trivial converse: apply mk, mk φ = 0
```

*Proof plan:* `Ideal.Quotient.eq` + `Ideal.mem_span_singleton` give `Φ.φ.toPoly ∣ (S − y)`
(exactly the step inside `Rq.toQuotient_injective`, Rq.lean:107-121 — imitate, don't reuse, its
proof body); set `ρ := (S − y) /ₘ Φ.φ.toPoly`; the identity from `Polynomial.modByMonic_add_div`
+ `(Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr`; the degree bound from
`Polynomial.natDegree_divByMonic` and `natDegree (S − y) ≤ 2d − 2` (max of `hS`, `hy`).
Monicity: the `IsCyclotomic` field. Mind ℕ-subtraction: `hd : 2 ≤ d` keeps `d - 2`, `2*d - 2`
well-behaved; add the `powTwoCyclotomic` corollary with `hα : 1 ≤ α` discharging `hd`.

### F3.2 Row form over `Rq` (0.5 d)

```lean
theorem Rq.dot_eq_iff_exists_quotient (Mrow z : PolyVec (Rq Φ) μ) (y : Rq Φ) :
    dot Mrow z = y ↔
    ∃ ρ : Polynomial R, ρ.natDegree ≤ d - 2 ∧
      (∑ j, (Mrow j).rep * (z j).rep) = y.rep + Φ.φ.toPoly * ρ
```

*Proof plan:* `dot_eq_sum`; equality in `Rq` ↔ equality of `equivQuotient` images
(`RingEquiv.injective`) ↔ `mk (∑ reps·reps) = mk y.rep` (push `mk`/`toPoly` through sum and
product: `map_sum`, `map_mul`, `quotientHom_apply`); then F3.1 with
`hS := natDegree_sum_le + natDegree_mul_le + natDegree_val_toPoly_lt` (each `rep` has
`natDegree < d`) and `hy := natDegree_val_toPoly_lt`. Matrix corollary
`Rq.matVecMul_eq_iff_exists_quotient` (row-indexed `ρ : Fin n → Polynomial R`) by
`funext`-style row aggregation + `Classical.choice`/`Finset` packaging.

### F3.3 Evaluation and interpolation (1 d)

```lean
variable {F : Type} [Field F] (φF : ZMod q →+* F)     -- injective: RingHom.injective

abbrev evalAt (a : F) : Polynomial (ZMod q) →+* F := Polynomial.eval₂RingHom φF a

-- completeness direction: ring-hom push-through, `map_sum/map_mul/map_add`
theorem evalAt_row_eq_of_lift (h : S = y + φ * ρ) (a : F) :
    evalAt φF a S = evalAt φF a y + evalAt φF a φ * evalAt φF a ρ

-- soundness kernel (the Lemma 9 engine):
theorem lift_eq_of_eval_eq_at_distinct
    (hdeg : (S - y - φ * ρ).natDegree < N) (A : Fin N ↪ F)
    (h : ∀ i, evalAt φF (A i) S = evalAt φF (A i) y + evalAt φF (A i) φ * evalAt φF (A i) ρ) :
    S = y + φ * ρ
```

*Proof plan:* let `defect := Polynomial.map φF (S − y − φ*ρ)`; `eval₂ = eval ∘ map`
(`Polynomial.eval₂_eq_eval_map`), so `h` says `defect.eval (A i) = 0`;
`natDegree defect ≤ natDegree (S − y − φρ) < N` (`Polynomial.natDegree_map_le`); Mathlib's
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` (Roots.lean:690) with the embedding
`A` kills `defect`; `Polynomial.map_injective φF (RingHom.injective φF)` transfers `= 0` back;
`sub_eq_zero`. Degree arithmetic for the intended use: `S` at `≤ 2d−2`, `φρ` at `≤ d + (d−2)`,
so `hdeg` holds with `N := 2*d` — record this as the packaged corollary:

```lean
theorem Rq.dot_eq_of_eval_rows_at_distinct   -- 2d distinct α's + per-α row equations
    (hρdeg : ρ.natDegree ≤ d - 2) … : dot Mrow z = y     -- composes F3.3 + F3.2 (←)
```

### F3.4 (thin, optional — may slide to F5) digit decomposition of ρ (0.5 d)

`ρ = ∑ u, (b^u : ZMod q) • ρdig u` with per-digit coefficient bounds, as a `Polynomial`-level
wrapper over `zmodDigitDecomposition` (Gadget/Basic.lean:113) applied coefficient-wise
(`Polynomial.ofFinsupp`/`∑ k, C (digit …) * X^k` over `Finset.range d`). Only F5's `w̃`-table
needs it; F4 carries `ρ` whole. Implement only if time permits inside F3's budget.

### F3 acceptance

- `QuotientLift.lean` sorry-free, no Hachi imports, validate.sh green.
- A `powTwoCyclotomic`-instantiated `example` at `q = 5, α = 1` (degree-2 ring) checking F3.1's
  statement shape by `decide`/`native_decide` on a concrete instance, plus one `example`
  instantiating F3.3 at `F := ZMod 5`, `φF := RingHom.id` (sanity: the abstraction admits the
  base field itself).

---

## 5. Milestone F4 — HMZ25 lift, Fig. 4 / Lemma 9 (~4–5.5 d)

**Goal.** The two-round reduction (`t = Com(w̃)` then `α ← F`), CWSS at `k = 2d`, output
relation `relLiftE`, packaged and `▷`-appended onto `evalRlinChain`.

### F4.1 Scalar single-round CWSS lemma (1.5–2 d) — generic framework

**New file** `ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean`,
the `(ℓ = 1, k)` twin of `SingleRound.lean` (which stays untouched at `(2^r, 2)`):

```lean
@[reducible] def pSpecScalar (Msg C : Type) : ProtocolSpec 2 := ⟨!v[.P_to_V, .V_to_P], !v[Msg, C]⟩

@[reducible] def scalarStructure (k : ℕ) (hk : 2 ≤ k) : CWSSStructure (pSpecScalar Msg C) :=
  CWSSStructure.ofSpecialSound (fun _ => k) (fun _ => hk)     -- arity k

theorem coordinateWiseSpecialSound_of_mkWitness_scalar
    (V : Verifier oSpec StmtIn (StmtIn × Msg × C) (pSpecScalar Msg C))
    (hpure : ∀ s tr, V.verify s tr = pure (s, tr.messages ⟨0,rfl⟩, tr.challenges ⟨1,rfl⟩))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set ((StmtIn × Msg × C) × WitOut)) [Nonempty WitOut]
    (mkWitness : StmtIn → Msg → (Fin k → C) → (Fin k → WitOut) → WitIn)
    (hmk : ∀ s v (fam : Fin k → C) resp,
      (∀ j, ((s, v, fam j), resp j) ∈ relOut) → Function.Injective fam →
      (s, mkWitness s v fam resp) ∈ relIn) :
    V.coordinateWiseSpecialSound init impl (scalarStructure k hk) relIn relOut
```

*Proof plan:* transplant SingleRound.lean:345-410. The tree at arity `k` has one message node
and one challenge node with `k` children; `readPre`/`readChallenges`/`tree_shape` re-derive with
`Fin.cast` along `scalarStructure`'s `arity = 1*(k−1)+1 = k` (one `Nat` simp lemma). The star
machinery collapses: `nodeOk` at `ℓ = 1` is injectivity by `isSpecialSoundFamily_one_iff_injective`
(Basic.lean:111) composed with the `Equiv.funUnique` decomposition — so `hmk` receives plain
`Function.Injective fam` instead of `StarAt`. Branch acceptance → `relOut`-membership via the
same `branch_relOut_language` pattern (uses `mem_of_pure_accepting`). This lemma is also the
substrate for F6/F7's rounds later — build it clean.

### F4.2 Witness, commitment abstraction, relations (1–1.5 d) — `LinSumcheck/Lift.lean`

```lean
/-- Eq. (21)'s committed data in polynomial form: the R^lin witness plus the per-row
quotient polynomials with their structural degree bound. (Digit form arrives in F5.) -/
structure LiftedWitness (Φ) (μ n : ℕ) where
  z   : PolyVec (Rq Φ) μ
  ρ   : Fin n → Polynomial (ZMod q)
  hρ  : ∀ i, (ρ i).natDegree ≤ d - 2

/-- Abstract binding commitment for `w̃` (G2: instantiated later; Lemma 9 needs only binding). -/
structure LiftCom (W E : Type) where
  TCom : Type
  com  : W → TCom
  esc  : Set E
  escOfCollision : W → W → E
  collision_mem  : ∀ w w', w ≠ w' → com w = com w' →
                     Short w → Short w' → escOfCollision w w' ∈ esc
  -- `Short` = the relLift range predicate below, threaded as a parameter of the structure
  -- (weak binding is norm-conditioned — Lemma 7 / `outputToModuleSIS_valid_of_verified` pattern)

variable (K : LiftCom (LiftedWitness Φ μ n) E) (φF : ZMod q →+* F)

def LiftStatement := RlinStatement Φ n μ × K.TCom × F        -- pass-through shape

def relLift : Set (LiftStatement × LiftedWitness Φ μ n) :=
  {p | let ((s, t, a), w) := p
       K.com w = t ∧
       (∀ i, evalAt φF a (rowSum s.M w.z i) =
             evalAt φF a ((s.yvec i).rep) + evalAt φF a Φ.φ.toPoly * evalAt φF a (w.ρ i)) ∧
       vecLInftyNorm Φ w.z ≤ s.bound ∧ RhoShort w.ρ}
def relLiftE := relLift.withEscape K.esc
```

where `rowSum s.M w.z i := ∑ j, (s.M i j).rep * (w.z j).rep` (definition shared with F3.2) and
`RhoShort` is the coefficient-range predicate on `ρ` (bounded by the digit range; exact constant
pinned here, feeding F5). Decision recorded in the file header: `LiftCom` stays **abstract**
in F4; the concrete inner-outer instantiation (paper §4.5 "commit without re-decomposition") is
a Phase-G/F5 deliverable, and `collision_mem` is exactly the obligation
`outputToModuleSIS_valid_of_verified` will discharge there.

### F4.3 pSpec, prover, verifier (0.5 d)

```lean
-- pSpec := pSpecScalar K.TCom F ; instances by the ⟨0,h⟩/⟨1,_⟩ matching idiom;
-- SampleableType F is a section hypothesis (G5)
def liftVerifier : Verifier oSpec (RlinStatement Φ n μ) (LiftStatement …) (pSpecScalar K.TCom F) where
  verify := fun stmt tr => pure (stmt, tr.messages ⟨0,rfl⟩, tr.challenges ⟨1,rfl⟩)
def liftProver (computeW : …) : Prover …   -- QuadEval Reduction.lean:265-298 skeleton, honest w̃
```

### F4.4 Extraction — Lemma 9 (1.5–2 d)

```lean
noncomputable def liftBuildWitness
    (s : RlinStatement Φ n μ) (t : K.TCom) (fam : Fin (2*d) → F)
    (resp : Fin (2*d) → LiftedWitness Φ μ n ⊕ E) : PolyVec (Rq Φ) μ ⊕ E
-- (a) some branch is .inr e            → .inr e
-- (b) two branches carry w ≠ w'        → .inr (K.escOfCollision w w')
-- (c) all branches carry the same w    → .inl w.z

theorem liftBuildWitness_mem_relRlinE
    (hd : 2 ≤ d) (hresp : ∀ j, ((s, t, fam j), resp j) ∈ relLiftE) (hinj : Function.Injective fam) :
    (s, liftBuildWitness …) ∈ relRlinE K.esc
```

*Proof plan* (the paper's Lemma 9, case-faithful):
- (a): pass-through, as in F2.0.
- (b): both branches' `relLift` give `K.com w = t = K.com w'` and both `Short`;
  `K.collision_mem` puts the escape in `K.esc` — `relRlinE`'s `.inr` case. (This is Remark 2's
  weak-binding route.)
- (c): the shared `w` satisfies, for each row `i`, the `evalAt`-equation at all `2d` **distinct**
  (injective `fam`) points; `(rowSum − yvec.rep − φ·ρ i).natDegree ≤ 2d − 2 < 2d` from `w.hρ` +
  representative degree bounds; `lift_eq_of_eval_eq_at_distinct` (F3.3, `N := 2d`) yields the
  `(ZMod q)[X]`-identity per row; `Rq.dot_eq_iff_exists_quotient` (F3.2, `←` direction — or
  directly the packaged `Rq.dot_eq_of_eval_rows_at_distinct`) yields `s.M *ᵥ w.z = s.yvec`;
  the norm conjunct of `relLift` is already `vecLInftyNorm w.z ≤ s.bound`. Both `relRlin`
  conjuncts hold — `.inl` case.

Then:

```lean
theorem lift_coordinateWiseSpecialSound … :
    liftVerifier.coordinateWiseSpecialSound init impl (scalarStructure (2*d) (by omega))
      (relRlinE K.esc) (relLiftE …)
  -- coordinateWiseSpecialSound_of_mkWitness_scalar with mkWitness := liftBuildWitness,
  -- hmk := liftBuildWitness_mem_relRlinE
```

Note `2 ≤ 2*d` from `hd`; no field-size hypothesis is needed for CWSS (an injective
`Fin (2*d) ↪ F` family is the *tree's* problem — knowledge error, out of scope, only needs
`2d ≤ |F|` which the eventual instantiation satisfies).

### F4.5 Package and chain (0.5 d)

```lean
def liftPackage … : CWSSPackage init impl (RlinStatement Φ n μ) (PolyVec (Rq Φ) μ ⊕ E)
    (LiftStatement …) (LiftedWitness Φ μ n ⊕ E) (pSpecScalar K.TCom F)
def evalLiftChain := evalRlinChain ▷ liftPackage       -- seam relRlinE, by rfl (G6)
theorem evalLift_coordinateWiseSpecialSound := evalLiftChain.isCWSS
```

`evalLift_coordinateWiseSpecialSound` is this plan's end-to-end deliverable: CWSS from
`relPolyEvalE` all the way to `relLiftE` — i.e. paper Figures 3 + 4 (Lemmas 8 + 9) composed,
escape-threaded, ready for F5/F6 to consume `relLiftE` as their `relIn`.

### F4 acceptance

- `ScalarRound.lean` and `Lift.lean` sorry-free; `evalLift_coordinateWiseSpecialSound` compiles;
  validate.sh green (`--lint` before PR).
- Prover skeleton `liftProver` compiles (completeness stays a skeleton, D12).
- An `example` instantiating `F := ZMod q`, `φF := RingHom.id` and a trivial `LiftCom`
  (`TCom := LiftedWitness …`, `com := id`, `esc := ∅` unreachable since `com` injective) —
  proving the abstraction is inhabitable without any Phase-B–E material.
- File-header faithfulness notes: (i) Fig. 4 sends `(z, r)` in the clear — here they are the
  never-sent output witness (v2's D6, QuadEval precedent); (ii) `Com` abstract pending the
  §4.5 inner-outer instantiation.

---

## 6. The sub-chain after these four milestones

| # | Stage | pSpec | Verifier | CWSS structure | relIn → relOut | Status after this plan |
|---|---|---|---|---|---|---|
| 1 | bridge (threaded) | `!p[]` | pure | `ofIsEmpty` | `relPolyEvalE → relInE` | F2.0 |
| 2 | QuadEval (threaded) | msg + vector chal | pure | `foldStructure` | `relInE → relOutE` | F2.0 |
| 3 | R^lin adapter | `!p[]` | pure | `ofIsEmpty` | `relOutE → relRlinE` | F2 |
| 4 | HMZ25 lift | `t` + scalar `α` | pure | `ofSpecialSound k = 2d` | `relRlinE → relLiftE` | F4 |

All four verifiers are pure — **B4 is not consumed inside this plan's chain**; it is the
groundwork the *next* milestones (F7 sumcheck loop, F8 final eval, G3 handoff) compose with,
built first per the agreed ordering while its design is fresh from the framework recon.
Escape budget `E` is a single parameter threaded through rows 1–4, instantiated at `K.esc`.

## 7. Effort summary and sequencing

| Milestone | Estimate | Hard prerequisites |
|---|---|---|
| B4 | 2.5–3.5 d | maintainer ping (R3) |
| F2 (incl. F2.0) | 3–4.5 d | none |
| F3 | 2–3 d | none (parallelizable with F2 if desired; sequential per instruction) |
| F4 | 4–5.5 d | F2 (seam), F3 (F3.2/F3.3), F4.1 |
| **Total** | **~12–16.5 d** | |

## 8. Risks

- **R-B4-a (VCVio probability plumbing).** `failure_not_accepting` needs the right
  `simulateQ`/`OptionT` simp set; the pure proofs (Composition.lean:333-362, SeqCompose.lean:70-82)
  are the map. Budgeted inside B4.1; if it fights back, extract the acceptance-probability facts
  as standalone `OracleComp` lemmas and ask maintainers where they belong.
- **R-B4-b (framework churn).** Same mitigation as v2's R3: everything in new files, existing
  theorems byte-identical, PR flagged as security-infrastructure.
- **R-F2-a (index bookkeeping).** The block-matrix equivalence is the milestone's real cost.
  Mitigation: F2.1's `decide` convention pins *first*; every cast through `Fin.addCases`/
  `finProdFinEquiv` gets its own simp lemma; treat any mid-proof `Fin.cast` as a red flag (v2 R4).
- **R-F2-b (escape-threading reception).** The `withEscape` design changes no existing
  declaration but *does* add a parallel chain (`evalChainE`). Alternative if maintainers object:
  make `E` an argument of the original relations with `E := Empty` as the old theorems — more
  invasive; keep as fallback only.
- **R-F3-a (CPolynomial ↔ Polynomial friction).** All identities are stated over
  `Polynomial R` via `.rep`; the only CompPoly surface is `toPoly` of ring operations
  (`ringEquiv` handles it). Half-day slack budgeted.
- **R-F4-a (arity-`k` re-derivation).** `ScalarRound.lean` re-derives SingleRound's tree readers
  at arity `k`; the `(2^r, 2)` proofs are the template but `Fin.cast` normalization along
  `1*(k−1)+1 = k` needs one careful simp lemma. Budgeted in F4.1.
- **R-F4-b (commitment abstraction).** If F5 later needs `TCom` data F4 hid (e.g. homomorphic
  structure for the avoid-re-decomposition trick), `LiftCom` grows fields — additive, not
  breaking. The abstract-now/instantiate-later split is deliberate (G2).

## 9. Documentation obligations (same PRs as the code — CLAUDE.md guardrail)

- `docs/wiki/repo-map.md`: `CoordinateWiseSpecialSoundness/{Guarded,Escape,ScalarRound}.lean`,
  `Hachi/LinSumcheck/`, `CyclotomicRing/QuotientLift.lean`.
- `docs/kb/papers/NOZ26.md`: mark Lemma 9 formalized; record the escape-threading design and
  the `LiftCom` abstraction decision.
- Blueprint: `blueprint/src/proof_systems/hachi_sumcheck.tex` stub covering Fig. 4 / Lemma 9
  (F6–F9 will extend it).
- Update `HACHI_RING_SWITCHING_PLAN.md` §4's F2/F3/F4 entries with a pointer to this file
  (anchors there are stale; this file is authoritative for the four milestones).
