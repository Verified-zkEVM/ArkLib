# Hachi Ring Switching + Sumcheck — Formalization Plan (v2)

Target: the complete interactive core of **Hachi** (NOZ26, ePrint 2026/156) beyond the finished
Fig. 3 / Lemma 8 layer, in two coupled tracks:

1. **Ring switching (§3)** — the packing reduction from extension-field evaluation claims to
   `R_q`-claims (Lemma 5, Theorem 2, Lemma 6, §3.1 generic, §3.2 base-field), realized by
   **generalizing `ArkLib/ProofSystem/RingSwitching/`** so that one packing-phase definition
   serves both Binius (DP24) and Hachi, instead of building a Hachi-only head.
2. **Sumcheck (§4.3, Figs. 4–7, Lemmas 9–11)** — the HMZ25 lift + zero-check + sumcheck chain
   that proves Eq. (20) + range constraints, built on the degree-generic
   `ArkLib/ProofSystem/Sumcheck/Structured` substrate.

Every Hachi subprotocol is proven **coordinate-wise special sound (CWSS)** and composes with the
existing chain (`eval_coordinateWiseSpecialSound`,
[Basic.lean:136](ArkLib/Commitments/Functional/Hachi/Basic.lean#L136)) through
`Verifier.append` / `Verifier.seqCompose` CWSS composition. The companion analysis of *why* the
existing `RingSwitching` protocol files don't fit Hachi as-is — and why the first message + first
check *do* — is [`HACHI_RING_SWITCHING_COMPARISON.md`](HACHI_RING_SWITCHING_COMPARISON.md); this
plan operationalizes that seam.

## 0. Disambiguation: three reductions called "ring switching"

| | Direction | Mechanism | This plan |
|---|---|---|---|
| **§3 packing** (Hachi) | `F_{q^k}`-claims → `R_q`-claims | pack via ψ, one message `Y`, deterministic trace check | Phases B–E (as an instance of the *generalized* packing phase) |
| **DP24 / Binius** | small field `B` → large field `L` | pack, send carrier `ŝ`, check, then batching challenge + relocation sumcheck | Phase B (kept working through the refactor) |
| **§4.3 HMZ25 lift** (Hachi) | `R_q`-linear relations → `F_{q^k}` sumcheck | lift `Mz = y` to `Z_q[X]`, evaluate at `α ← F_{q^k}` | Phase F |

Shared insight driving the generalization (verified against the code, see the comparison doc):
DP24's **steps 1–2** (send carrier element, deterministically reconstruct the original claim from
its packed coordinates) *are* Hachi §3's `(Y, trace check)` under the Hachi profile
(`A = L = R_q`, decompositions = ψ-coordinates, trace = the reconstruction functional). The
protocols diverge only *after* step 2: DP24 must interactively relocate the residual carrier
claim (batching challenge + sumcheck) because its carrier `L ⊗_K L` is strictly bigger than `L`;
Hachi's carrier *is* `L`, so the residual claim is already a native evaluation claim and goes
straight to the Fig. 3 chain. **Split the module at that seam.**

## 1. Verified current state (Lemma 5/6 status revalidated 2026-07-30)

### 1.1 Hachi chain — the consumer, done through Lemma 8

- `quadEval_coordinateWiseSpecialSound`
  ([QuadEval.lean:630](ArkLib/Commitments/Functional/Hachi/PolynomialQuadraticEq/QuadEval.lean#L630)),
  sorry-free. Statement/witness types: `QuadEvalStatement` (:69), `QuadEvalResponse` (:85, the
  never-sent `(ŵ, t̂, ẑ)` triple = output witness), `QuadEvalWitness` (:100, opening ∨ msisB ∨
  msisD), `ShortChallenge` (:124, norm carried by the subtype).
- **`relOut` = Eq. (20) + range checks** ([QuadEval.lean:214](ArkLib/Commitments/Functional/Hachi/PolynomialQuadraticEq/QuadEval.lean#L214)):
  with `z := J ẑ`, the six conjuncts c1 `D ŵ = v`, c2 `B (flatten t̂) = u`, c3 `bᵀ(G_{2^r} ŵ) = y`,
  c4 `(cᵀ ⊗ G₁) ŵ = aᵀ G_{2^m} z`, c5 `(cᵀ ⊗ G_{n_A}) t̂ = A z`, c6 `‖ŵ‖∞, ‖t̂‖∞, ‖ẑ‖∞ ≤ γ`.
  **This is exactly the §4.3 input** — the `R^lin` instance Phase F proves knowledge for.
- Zero-round bridge (`bridgeVerifier`, `bridge_coordinateWiseSpecialSound`,
  [PolyEvalReduction.lean:109/188](ArkLib/Commitments/Functional/Hachi/PolynomialQuadraticEq/PolyEvalReduction.lean#L109))
  via `ReduceClaim.verifier_coordinateWiseSpecialSound`
  ([ReduceClaim.lean:186](ArkLib/ProofSystem/Component/ReduceClaim.lean#L186)).
  `PolyEvalStatement` (:79): `pp, u, xl : Vector (Rq Φ) r, xh : Vector (Rq Φ) m, y : Rq Φ`.
  `relPolyEval` (:149): eval-consistent `VerifiedOpening` of `extractedPoly` (:131) ∨ MSIS escapes.
- Composed: `eval_coordinateWiseSpecialSound`
  ([Basic.lean:136](ArkLib/Commitments/Functional/Hachi/Basic.lean#L136)), sorry-free, via
  `Verifier.append_coordinateWiseSpecialSound` with structure
  `CWSSStructure.ofIsEmpty.append foldStructure`. TODO block at
  [Basic.lean:256-272](ArkLib/Commitments/Functional/Hachi/Basic.lean#L256) already names the
  §4.3+ subprotocols, the seqCompose migration, and the ring-switch head (mislabelled "§4.1";
  the paper section is §3 — fix in D2).
- `PolynomialEvalSplit.lean` is generic over `[CommSemiring R]` (core sections; only the
  Lagrange section at :267 needs `CommRing`): `splitEquiv`
  (:64, `Fin (2^nh) × Fin (2^nl) ≃ Fin (2^(nl+nh))`, low bits = first `nl` variables = rows/`b`),
  `toMatrix` (:140), `evalSplit_eq_eval` (:162), `toPolynomial` (:189), `eval_eq_sum` (:125),
  `monomialBasis_get` (:130). Reusable verbatim over the subring `B` below.

### 1.2 Lattice layer — Theorem 2 and Lemma 6 proved; one Lemma 5 gap

- `psi` ([Subfield/Packing.lean:61](ArkLib/Data/Lattices/CyclotomicRing/Subfield/Packing.lean#L61)),
  `psi_add` (:74), `psi_bijective`
  ([Subfield/Bijectivity.lean:34](ArkLib/Data/Lattices/CyclotomicRing/Subfield/Bijectivity.lean#L34);
  hypotheses `h2 : (2 : ZMod q) ≠ 0`, `hk : 2 * 2^κ ∣ 2^α`).
- **Theorem 2**: `traceH_psi_mul_conj`
  ([Subfield/TraceInnerProduct.lean:229](ArkLib/Data/Lattices/CyclotomicRing/Subfield/TraceInnerProduct.lean#L229)):
  `traceH α k (psi a * conjAut α (psi b)) = (2^α / k) • (Σ i, a i * b i : fixedSubring α k)`,
  hypotheses `(h2) (hk2pow : ∃ κ, k = 2^κ) (hk : 2 * k ∣ 2^α)`. Plus `traceH_smul_fixed` (:92),
  `traceH_mem_fixed` ([Galois/Trace.lean:104](ArkLib/Data/Lattices/CyclotomicRing/Galois/Trace.lean#L104)).
- `fixedSubring` is a `Subring`
  ([Galois/FixedSubring.lean:43](ArkLib/Data/Lattices/CyclotomicRing/Galois/FixedSubring.lean#L43)),
  `mem_fixedSubring_iff` (:47), `card_fixedSubring_eq`
  ([Subfield/Cardinality.lean:99](ArkLib/Data/Lattices/CyclotomicRing/Subfield/Cardinality.lean#L99)),
  `conjAut`/`conjExp` ([Galois/Group.lean:58/44](ArkLib/Data/Lattices/CyclotomicRing/Galois/Group.lean#L58)),
  `traceH`/computable `traceHComp` ([Galois/Trace.lean:68/73](ArkLib/Data/Lattices/CyclotomicRing/Galois/Trace.lean#L68)),
  Eq. (7) generators `fixedBasisMap` (Cardinality.lean:53), `vElt`
  ([Subfield/Basis.lean:419](ArkLib/Data/Lattices/CyclotomicRing/Subfield/Basis.lean#L419)).
- Remaining sorry: `no_selfReciprocal_factor`
  ([Subfield/Field.lean:207, sorry at :211](ArkLib/Data/Lattices/CyclotomicRing/Subfield/Field.lean#L207);
  gates only the Lemma 5 *field* upgrade of `fixedSubring`; **becomes load-bearing in Phase F**).
  Lemma 6 is now proved as `cInfNorm_psi_le`
  ([Subfield/NormBound.lean](ArkLib/Data/Lattices/CyclotomicRing/Subfield/NormBound.lean)) and is
  `sorryAx`-free.
- Missing glue (Phase A): `conjAut` involution, `conjAut` fixes `fixedSubring` pointwise,
  `psi_smul`, the `Algebra ↥(fixedSubring α k) (Rq …)` instance, unit-ness of `(2^α/2^κ : Rq)`.

### 1.3 `ProofSystem/RingSwitching/` — profile fits, protocol needs the split

- `RingSwitchingProfile B L κ` ([Profile.lean:63](ArkLib/ProofSystem/RingSwitching/Profile.lean#L63)),
  `CommRing`-only by design, documents the Hachi column of every field (:32-42) and the **law
  boundary** (:44-49): the reconstruction laws are profile data; the protocol-level identities
  connecting them to `packMLE`/`embedded_MLP_eval` are discharged per instance. No `hachiProfile`
  exists yet (KB gap, [NOZ26.md:63](docs/kb/papers/NOZ26.md#L63)).
- Wire/protocol layer (all Binius-flavored, oracle reductions over `AbstractOStmtIn`,
  [Prelude.lean:249](ArkLib/ProofSystem/RingSwitching/Prelude.lean#L249)):
  - `pSpecBatching : ProtocolSpec 2 := ⟨![P_to_V, V_to_P], ![P.A, Fin κ → L]⟩`
    ([Spec.lean:34](ArkLib/ProofSystem/RingSwitching/Spec.lean#L34)) — **splittable as a 1-message
    spec `++ₚ` a 1-challenge spec** (both `ProtocolSpec 1`; `1 + 1` is defeq `2`; the repo already
    lives with non-syntactic append forms, cf. [Basic.lean:62](ArkLib/Commitments/Functional/Hachi/Basic.lean#L62)).
  - Batching verifier: on a failed step-2 check it returns a **dummy state**, not `failure`
    ([BatchingPhase.lean:150-152, failureState :68](ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L150)).
  - Step-2 check `performCheckOriginalEvaluation`
    ([Prelude.lean:337](ArkLib/ProofSystem/RingSwitching/Prelude.lean#L337)) hardwires
    `eqTilde`-weights and `P.decomposeColumns`; carrier evaluation `embedded_MLP_eval` (:326);
    MLE-convention packing `packMLE`/`unpackMLE` (:111/:141) packs the **first** `κ` variables.
  - All five RBR soundness theorems `[IsDomain L]`-gated and sorried
    (BatchingPhase.lean:327/:344; SumcheckPhase.lean:274/:283, :470/:480, :590/:604;
    General.lean:145/:180-184); all three completeness leaves sorried (BatchingPhase.lean:315/:324,
    SumcheckPhase.lean:136/:147, :382/:394). **Consequence: re-plumbing statements is cheap; no
    proven Binius theorem is at risk.**
- External consumers (refactor blast radius, verified by grep): only
  `Binius/FRIBinius/{Prelude.lean:50, CoreInteractionPhase.lean:56, General.lean:84/98/184-215}`
  (`BinaryBasefold/Basic.lean:472`'s `SumcheckBaseContext` re-export is from
  `Sumcheck.Structured`, not this module). FRIBinius consumes
  `biniusProfile := binaryTowerProfile …`, the `Statement`/`RingSwitchingBaseContext` types,
  `sumcheckRoundRelation`, `RingSwitching_SumcheckMultParam`, and — in `General.lean` only —
  `BatchingPhase.oracleVerifier` / `batchingOracleReduction` / `batchingInputRelation` /
  `batchingReduction_perfectCompleteness` (the latter sorried). Two files to re-plumb.

### 1.4 `Sumcheck/Structured` substrate — degree-generic, context-generic, **zero soundness theorems**

- `SumcheckMultiplierParam L ℓ Context`
  ([Structured.lean:85-96](ArkLib/ProofSystem/Sumcheck/Structured.lean#L85)): `multpoly`,
  `combinator`, `degCombinator`; docstring (:79-80) names Hachi's range product. `Statement`
  (:223) carries `sumcheck_target`, `challenges`, and an **arbitrary** `ctx : Context`;
  `SumcheckWitness L ℓ i d` (:257) with explicit degree `d` (docstring :253: Binius `d := 2`,
  Hachi `d := 2b+1`). `sumcheckConsistencyProp` (:238), `computeRoundPoly` (:130),
  `projectToMidSumcheckPolyWithParam` (:155), `boolDomain`
  ([Domain.lean:180](ArkLib/ProofSystem/Sumcheck/Domain.lean#L180)).
- Per-round wire + machines ([Structured/SingleRound.lean](ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean)):
  `pSpecSumcheckRound L d : ProtocolSpec 2` (:102, one poly message, one **scalar** challenge),
  `roundOracleProver` (:199), `roundOracleVerifier` (:237), `roundOracleReduction` (:272),
  `getSumcheckRoundPoly` (:63), degree lemma `roundPoly_degreeLE_finset` (:52, proven).
  `Context` is a bare type variable; docstring (:125-126) says "Hachi will plug in its own".
- The round verifier is **pure-with-dummy**: on a failed `Σ_b h_i(b) = target` check it returns a
  dummy statement (`sumcheck_target := 0`, snoc'd challenge `0`) — no `failure` anywhere in the
  file. `Verifier.IsPure` therefore holds — but the dummy convention is **insufficient for a CWSS
  treatment** (the round check is challenge-independent, since the message `g_i` is shared by all
  siblings of a tree node; a failed check therefore collapses *every* sibling branch onto the
  same dummy statement, and extraction loses the `g_i(0)+g_i(1) = target` constraint entirely).
  F7 adds a **guarded** round-verifier variant for Hachi; see D6/R10.
- **No completeness/RBR/CWSS theorem exists on the substrate itself** (grep-verified). All
  soundness statements over it live in `RingSwitching/SumcheckPhase.lean`, pinned to `d := 2` and
  sorried. Hachi's per-round CWSS (F7) is new work, on purpose
  ([Structured.lean:25-29](ArkLib/ProofSystem/Sumcheck/Structured.lean#L25): the two proof modes
  are independent until a refinement theorem lands).

### 1.5 CWSS framework — what exists, the one genuine gap

- Notion: `CWSSStructure` ([Basic.lean:137](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L137)),
  `ofSpecialSound` (:182, `ℓᵢ = 1`, arity `k`), star predicate `IsSpecialSoundFamily` (:81),
  `isSpecialSoundFamily_one_iff_injective` (:111 — `ℓ = 1` ⇒ `k` **distinct** challenges, exactly
  paper Lemma 9/11's shape), `Verifier.coordinateWiseSpecialSound` (:212) + oracle variant (:234).
- Composition:
  - binary append `Verifier.append_coordinateWiseSpecialSound`
    ([Composition.lean:414](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L414))
    requires the **left verifier pure**:
    `hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr)` (:419); helpers
    `append_run_pure_left` (:311) and `pure_accepting_of_mem` (:325) are where a guarded variant
    generalizes. Oracle-verifier wrapper at :451.
  - n-ary `Verifier.seqCompose_coordinateWiseSpecialSound`
    ([SeqCompose.lean:391](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SeqCompose.lean#L391),
    tree form :364): per-factor `IsPure`, seam relations `rel i.castSucc ↦ rel i.succ`,
    `hWit : Nonempty (Wit (Fin.last m))`. Fits the *challenge-only* zero-check rounds as-is;
    the guarded sumcheck rounds need the guarded n-ary variant (B4).
- No-challenge bridge `coordinateWiseSpecialSound_of_isEmpty_challengeIdx`
  ([NoChallenge.lean:117](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/NoChallenge.lean#L117);
  tree form :103, oracle form :144, `ofIsEmpty` :45):
  hypothesis is **probability-phrased** (`Pr[accept] = 1 → extraction`), so it already covers
  *rejecting* verifiers standalone. The gap is **only** in composition: a rejecting verifier on
  the **left** of an append (B4).
- Single-round star machinery `coordinateWiseSpecialSound_of_mkWitness`
  ([SingleRound.lean:363](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L363))
  is pinned to the QuadEval shape (message + vector challenge, statement-*extending* pure
  verifier) — reusable for F4's lift (after generalizing the challenge to a scalar / `2^0`
  vector), **not** for sumcheck rounds (their verifier transforms the statement) — F7 adds the
  missing lemma.
- No CWSS↔RBR bridge and no CWSS→knowledge-error theorem (FMN24 Lemma 4) anywhere
  ([Implications.lean](ArkLib/OracleReduction/Security/Implications.lean) bridges CWSS↔plain-SS
  only). Knowledge-error accounting stays out of scope (R6, tracked in the Hachi TODO block,
  [Commitments/Functional/Hachi/Basic.lean:209-211](ArkLib/Commitments/Functional/Hachi/Basic.lean#L209)).

## 2. Target architecture

### 2.1 The generalized ring-switching module (Phase B)

```
RingSwitching/
  Profile.lean            -- unchanged (RingSwitchingProfile)
  PackingScheme.lean      -- NEW: weights + pack + decomp-choice (data), laws as Props
  Packing.lean            -- NEW: the shared 1-message PackingPhase reduction (guarded verifier)
                          --      + generic CWSS theorem (law-hypothesized)
  Relocation.lean         -- NEW (extracted): batching challenge + s₀ (DP24-only, stays RBR)
  Prelude / Spec / SumcheckPhase / General
                          -- re-plumbed: pSpecBatching := pSpecPacking ++ₚ pSpecBatchChal,
                          --   batchingOracleReduction := packing.append relocation,
                          --   sorried RBR/completeness statements restated at same boundaries
```

`FullRingSwitching = PackingPhase ++ RelocationPhase ++ sumcheck loop ++ mlIOPCS` (Binius,
unchanged semantics); `Hachi §3.1 = PackingPhase[hachi instance] ++ (σ₋₁-adapter) ++ Fig. 3 chain`.

### 2.2 The full Hachi verifier chain (one iteration; seam-by-seam in §5)

```
 §3.2/§4.5 partial-evals head (Phase E/G, pure, 1 msg)          — optional outermost head
   → §3.1 packing head (Phase C/D: PackingPhase[hachi], guarded, 1 msg: Y)
     → σ₋₁ statement adapter (zero-round ReduceClaim)
       → bridge → QuadEval (DONE)                               — Fig. 3 / Lemma 8
         → Eq.(20) → R^lin adapter (F2, zero-round)
           → HMZ25 lift (F4: commit w̃, challenge α; k = 2d special sound)
             → zero-check challenge (F6: one Kronecker-seed pair, ℓ = 2, k = D)
               → paired sumcheck rounds ×ℓ_sc (F7: shared challenge, k = max-deg+1)
                 → final-eval step (F8: open-w̃ claim + M̃_α check)
                   → next-iteration statement (Phase G) or base case
```

## 3. Design decisions

- **D1 (PackingScheme, the generalization knob).** A new structure bundles the three
  instance-varying ingredients the current code hardwires:

  ```lean
  structure PackingScheme {B L : Type} [CommRing B] [CommRing L] [Algebra B L] {κ : ℕ}
      (P : RingSwitchingProfile B L κ) (SmallPoly LargePoly : Type) where
    /-- how the small-poly is packed (Binius: `packMLE P.basis`; Hachi: ψ on coefficient blocks) -/
    pack : SmallPoly → LargePoly
    /-- blending weights of the packed coordinates at the packed point-part
        (Binius: `eqTilde`-Lagrange; Hachi §3: tail monomials `monomialBasis`) -/
    weights : (Fin κ → L) → (Fin κ → Fin 2) → L
    /-- which profile decomposition the reconstruction check reads
        (Binius: `decomposeColumns`; Hachi: fixed by the C3 law proof — see R2) -/
    decomp : P.A → (Fin κ → Fin 2) → L
    /-- carrier evaluation of the packed polynomial (both: `embedded_MLP_eval`-shaped) -/
    carrierEval : LargePoly → (Fin κ → L) → P.A   -- point-suffix only, see D4
  ```

  The **laws are not structure fields** — they are standalone `Prop`s taken as hypotheses by the
  generic theorems (mirroring the Profile.lean law-boundary comment), so instances can exist
  before their laws are proven and no new `sorry` enters a structure:

  ```lean
  def PackingScheme.CheckSound (S : PackingScheme …) : Prop :=
    ∀ (t' : LargePoly) (rp : Fin κ → L) (rs : point-suffix) (s : L),
      (∑ v, S.weights rp v * S.decomp (S.carrierEval t' rs) v) = s →
      evalUnpacked S t' (rp ++ rs) = s          -- soundness direction
  def PackingScheme.CheckComplete (S : PackingScheme …) : Prop := …  -- honest direction
  ```

  Binius's law = DP24's step-2 identity (tensor algebra; optional milestone B5). Hachi's law =
  Theorem 2 at the multilinear level (C3, the heart).
- **D2 (split, don't fork).** Redefine `pSpecBatching := pSpecPacking ++ₚ pSpecBatchChal` and
  `batchingOracleReduction := packingReduction.append relocationReduction` **keeping all public
  names and statement boundaries** (`BatchingStmtIn` in, `Statement … 0 × SumcheckWitness … 0`
  out). Affordable because every affected Binius proof is sorried (§1.3); the two consumer files
  (`RingSwitching/General.lean`, `Binius/FRIBinius/General.lean`) are re-plumbed in the same PR.
  Fallback if maintainers object (R3): add the split reductions alongside and leave the monolith,
  at the cost of duplicate definitions.
- **D3 (guarded packing verifier).** The shared packing verifier is
  `if check then pure out else failure`. Rationale: (i) the Hachi head *must* reject at runtime —
  its trace check consumes `(xt, y)`, which the fixed downstream `PolyEvalStatement` drops, so
  the check can live neither in a downstream relation nor in a pull-back (a pure pass-through
  head is unsound here); (ii) `failure` is more faithful than the current dummy-state convention
  and is fully supported by the no-challenge CWSS bridge (§1.5). The Binius RBR statements are
  restated against the guarded verifier (they were sorried; the dummy-state KState scaffolding in
  `BatchingPhase.lean` is rewritten to match). This is a deliberate, flagged behavior change for
  Binius (R3).
- **D4 (packed-block position).** The module packs the **first** `κ` variables (`packMLE`); the
  paper's §3.1 packs the **last** `α−κ`. Keep the module convention; the Hachi instantiation
  arranges its point as `(packed-part, rest)` and a reindexing lemma (pinned in A1 with `decide`
  examples, cf. `splitEquiv`'s low-bits-first orientation) connects to the paper's
  `(xl, xh, xt)` order. Never resolve index conventions mid-proof (R4).
- **D5 (σ₋₁ twist at the seam, not in the algebra).** With the profile's `φ₀ = id, φ₁ = σ₋₁`,
  the generic carrier message is `ŝ = σ₋₁(Y_paper)` for subfield-valued points (σ₋₁ fixes them;
  σ₋₁ is an involution). The head's zero-round output adapter applies `conjAut` when building
  `PolyEvalStatement.y`. A faithfulness note records `message = σ₋₁(paper's Y)`; the *check* is
  proven equivalent to the paper's trace equation (C2's `traceCheck_iff`), and the computable
  `Decidable` route goes through `traceHComp` (the bundled `conjAut`/`psi` are `noncomputable`,
  fine for verifier definitions in this repo).
- **D6 (sent vs proven-not-sent, unchanged from v1).** Messages genuinely on the wire (`Y`, the
  §3.2/§4.5 partial evaluations, the §4.3 commitment `t`, sumcheck round polys) are transcript
  messages; last-message data the final scheme never sends (Fig. 4's `(z,r)`, Figs. 5–6's `w̃`,
  Fig. 3's `(ŵ,t̂,ẑ)`) are **output-relation witnesses** in the QuadEval style. Runtime guards
  are needed exactly where a check reads *sent or input* data that the downstream statement type
  drops — four places: the §3.1 head, each sumcheck round's `Σ_b g_i(b) = target` check (the old
  target is dropped by the next round's statement), the §4.3 final-eval check (the last target is
  dropped by the `w̃`-eval-claim statement), and the §4.5 handoff (the head re-instantiated at
  the next ring dimension, same argument as the §3.1 head). Everything else stays pure.
- **D7 (derive-`y₀`, purity for the partial-evals heads).** For §3.2/§4.5 the verifier *derives*
  `y_{0…0} := y − Σ_{i≠0} weight_i · y_i` (paper footnotes 5/10) instead of checking an equation
  — making these heads total/pure and composable by the plain append theorem. No guard needed.
- **D8 (§4.3 stays in the CWSS currency, per-round).** Model the paper's special-soundness
  lemmas as: α-round `ofSpecialSound (k := 2d)` (Lemma 9); the zero-check as one challenge
  `(ρ₀,ρ_α) ∈ F²`, with `τ_s := (ρ_s,ρ_s²,ρ_s⁴,…)` and
  `k := D = max(2^m₀,2^m_α)` (the corrected one-round Lemma 10 in R7); and sumcheck rounds
  `ofSpecialSound (k := d_round + 1)` (Lemma 11), with **guarded** round verifiers (R10).
  The zero-check uses a local `CWSSStructure` with `ℓ=2`; guarded append/seqCompose (B4) remains
  necessary at the four guarded seams (§3.1 head, sumcheck loop, final-eval step, §4.5 handoff).
- **D9 (paired sumcheck).** Fig. 7 runs the `H_0`- and `H_α`-sumchecks with **shared challenges**
  (one `g_i` pair per round). Model as a thin paired-round wrapper over `Sumcheck/Structured`
  (message = pair of round polys at degrees `d₀`, `d_α`; one scalar challenge; witness = shared
  `w̃` + both projected `H`s), per-round `k = max d₀ d_α + 1`. Fallback: two separate sequential
  sumchecks (simpler, costlier transcript, still CWSS) — decide at F7 kickoff.
- **D10 (field parameterization for Phase F).** State §4.3 generically over a field `F` with
  `[Field F] [Fintype F] [DecidableEq F] [SampleableType F]` plus an evaluation embedding
  `Rq Φ → Polynomial (ZMod q)`-side data, and instantiate `F := ↥(fixedSubring α (2^κ))` once
  the Lemma 5 field upgrade lands (F1). This decouples all of F2–F9 from the
  `no_selfReciprocal_factor` sorry; only the final instantiation waits on it.
- **D11 (standing hypotheses).** `[Fact (Nat.Prime q)]`, `h2 : (2 : ZMod q) ≠ 0`,
  `hk : 2 * 2^κ ∣ 2^α` throughout Phases A–E; `q % 8 = 5` only where LS18/Lemma 5 enter (QuadEval
  already carries it; F1 needs it).
- **D12 (scope guard).** Honest-prover/completeness stays at the skeleton level (QuadEval
  precedent, prover at QuadEval.lean:318); `Commitment.Scheme`-level statements, knowledge-error
  accounting (FMN24 Lemma 4), and Fiat–Shamir remain tracked TODOs (Basic.lean:256-272), not
  deliverables here.

## 4. Milestones

Ordering: A → B → C → D → E ∥ F → G → H, with B4 independent of B1–B3, and F1–F3 independent of
everything in B–E. Estimates are focused work-days.

### Phase A — Groundwork (~2 days)

**A1. Convention pinning (0.5 d).** One file of `@[simp]` characterizations + `decide`/
`native_decide` examples fixing: `splitEquiv` orientation (low bits = first variables = rows);
which end the module packs (first `κ`) vs the paper (last `α−κ`) and the reindexing equivalence;
`hypercubeEquivFin : (Fin n → Fin 2) ≃ Fin (2^n)` relocated out of
[`Binius/FRIBinius/Prelude.lean:40`](ArkLib/ProofSystem/Binius/FRIBinius/Prelude.lean#L40)
to a neutral home (`ArkLib/Data/Fin/` or ToMathlib; deprecated alias stays) so Hachi never
imports `Binius.*`. Acceptance: a concrete `α = 2, κ = 1` round-trip example checked by `decide`.

**A2. Lattice glue lemmas (1–1.5 d).** All small, no sorry dependencies:
1. `conjAut_conjAut : conjAut α (conjAut α x) = x` (via `conjExp α * conjExp α ≡ 1 [MOD 2^(α+1)]`).
2. `conjAut_eq_self_of_mem_fixedSubring` (one-liner from `mem_fixedSubring_iff`).
3. `Algebra ↥(fixedSubring α k) (Rq (powTwoCyclotomic α))` — Mathlib subring instance or
   `(fixedSubring α k).subtype.toAlgebra` scoped.
4. `psi_smul : psi α k (c • a) = ↑c * psi α k a`.
5. `psiLinearEquiv : (Fin (2^α/2^κ) → B) ≃ₗ[B] Rq …` from `psi_add` + `psi_smul` +
   `psi_bijective`.
6. `isUnit_natCast_two_pow_div : IsUnit ((2^α / 2^κ : ℕ) : Rq …)` + the `nsmul` cancellation
   corollary (`(d/k) • x = (d/k) • y → x = y`).

### Phase B — Generalize `RingSwitching/` (Binius-preserving) (~6–8 days, excl. optional B5)

**B1. `PackingScheme` (1 d).** New `RingSwitching/PackingScheme.lean` per D1: the structure, the
two law `Prop`s, and the **Binius instance data**
`biniusPackingScheme : PackingScheme (binaryTowerProfile …) …` with
`pack := packMLE`, `weights rp v := eqTilde v↑ rp`, `decomp := P.decomposeColumns`,
`carrierEval := embedded_MLP_eval` — laws *stated* (`biniusPackingScheme_checkSound : … := by sorry`
is **not** added; instead the props are left as named definitions with a TODO, per D1).
Redefine `performCheckOriginalEvaluation` as an `@[reducible]` alias of the generic
`PackingScheme.check` at the Binius instance so existing call sites are untouched.

**B2. Split the batching phase (2–3 d).** Per D2/D3:
- `pSpecPacking (P) : ProtocolSpec 1 := ⟨![.P_to_V], ![P.A]⟩`;
  `pSpecBatchChal : ProtocolSpec 1 := ⟨![.V_to_P], ![Fin κ → L]⟩`;
  `pSpecBatching := pSpecPacking ++ₚ pSpecBatchChal` (instances re-derived via the append
  instances in Spec.lean).
- `Packing.lean`: statement `PackedClaimStatement := { base : SumcheckBaseContext L ℓ, s_hat : P.A }`;
  the guarded verifier
  `fun s tr => if S.check s.original_claim s.t_eval_point (tr ⟨0,_⟩) then pure ⟨s, tr ⟨0,_⟩⟩ else failure`;
  prover sends `S.carrierEval t' (suffix)`; witness pass-through (`BatchingWitIn`).
  Output relation `relPackedClaim := { (⟨s, ŝ⟩, wit) | ŝ = S.carrierEval wit.t' … ∧ wit.t' = S.pack wit.t ∧ compat }`.
- `Relocation.lean`: the challenge round + `compute_s0`; StmtIn `PackedClaimStatement`, StmtOut
  `Statement (RingSwitchingBaseContext …) 0` (types unchanged); DP24-only, keeps RBR statements.
- Re-plumb `BatchingPhase.lean` (monolith = append; restate the sorried KState/RBR/completeness
  at the same outer boundaries), `General.lean`, `FRIBinius/General.lean`. Build green; no
  hand-edits to `ArkLib.lean`.

**B3. Generic packing CWSS (1 d).** In `Packing.lean`:

```lean
theorem PackingPhase.coordinateWiseSpecialSound_of_checkSound
    (hlaw : S.CheckSound) (D : CWSSStructure _) :
    (packingVerifier S).coordinateWiseSpecialSound init impl D
      relOriginalClaim relPackedClaim
```

via `coordinateWiseSpecialSound_of_isEmpty_challengeIdx` (probability-phrased hypothesis already
accommodates the guard; acceptance forces `check = true`, then `hlaw` converts the packed-claim
witness into the original-claim witness through `unpack`). One P→V message ⇒
`IsEmpty ChallengeIdx` holds. Also state the RBR-error-0 analogue for Binius symmetry (optional).

**B4. Guarded CWSS composition (2–3 d, independent).** Extend
`CoordinateWiseSpecialSoundness/Composition.lean` and `SeqCompose.lean`:
- `Verifier.append_treeSpecialSound_of_guard` — hypothesis
  `hV₁ : ∀ stmt tr, V₁.verify stmt tr = if check stmt tr then pure (verify₁ stmt tr) else failure`.
  Proof deltas against :366: a guarded `append_run_pure_left` (composed acceptance probability 1
  forces `check = true` — the `failure` branch has success probability 0 — then reduces to the
  pure case; uses nonemptiness of the suffix tree's transcript list, cf. the `LeafPath` machinery
  already used at Composition.lean:383) and a guarded `pure_accepting_of_mem`. Corollaries:
  `append_coordinateWiseSpecialSound_of_guard` + the OracleVerifier wrapper.
- `Verifier.seqCompose_treeSpecialSound_of_guard` — the n-ary variant with per-factor
  `IsGuarded` (a `check`-indexed generalization of `IsPure`; pure = trivially-true check), by the
  same induction as SeqCompose.lean:364 with the guarded append as the step.
Four consumers in this plan: the §3.1 head (D1), the guarded sumcheck-round loop (F7), the
final-eval step (F8), and the §4.5 handoff head (G3). Generic security infrastructure —
coordinate with maintainers (R3).

**B5 (optional, parallel). Binius packing law (2–4 d).** Prove
`biniusPackingScheme_checkSound` from `decomposeColumns_spec` + tensor-algebra + MLE partial
evaluation. Payoff: the first *proven* soundness statement in the Binius ring-switching stack
(via B3). Not on Hachi's critical path.

### Phase C — Hachi profile + packed-evaluation algebra (~4–6 days; the mathematical heart)

**C1. `hachiProfile` (1 d).** New `Commitments/Functional/Hachi/RingSwitch/Profile.lean`
(imports `RingSwitching/Profile`, `Lattices/CyclotomicRing/Subfield`). Parameter dictionary
(**`κ` clash**: paper `κ` = log extension degree; profile rank is `α − κ` — spell it out
everywhere, R5):

```lean
noncomputable def hachiPackBasis (h2 …) (hk …) :
    Basis (Fin (α − κ) → Fin 2) ↥(fixedSubring (R := ZMod q) α (2^κ)) (Rq (powTwoCyclotomic α)) :=
  -- Basis.ofEquivFun on psiLinearEquiv.symm (A2.5), reindexed along hypercubeEquivFin (A1)

noncomputable def hachiProfile (h2 …) (hk …) :
    RingSwitchingProfile ↥(fixedSubring (R := ZMod q) α (2^κ)) (Rq (powTwoCyclotomic α)) (α − κ) where
  basis := hachiPackBasis h2 hk
  A := Rq (powTwoCyclotomic α);  φ₀ := RingHom.id _;  φ₁ := (conjAut α : _ →+* _)
  decomposeColumns z v := ↑(hachiPackBasis h2 hk |>.repr z v)
  decomposeRows    z u := ↑(hachiPackBasis h2 hk |>.repr (conjAut α z) u)
  decomposeColumns_spec := …  -- ~10 lines: coords in B are conjAut-fixed (A2.2) + Basis.sum_repr
  decomposeRows_spec := …     -- conjAut ring-hom + involution (A2.1) + Basis.sum_repr
```

Acceptance: `example` instantiation at the paper's Fig. 9 shape (`q ≡ 5 (mod 8)`, `α = 10`,
`κ = 2`).

**C2. `hachiPackingScheme` (1 d).** `RingSwitch/Scheme.lean`:
`pack` = ψ on coefficient blocks of a `CMlPolynomial B (μ + (α−κ))` (block structure by the A1
convention; agreement-with-`packMLE` lemma is Phase H hygiene, not a dependency);
`weights xt j := ↑((CMlPolynomial.monomialBasis xt).get j)` (tail monomials, values in `B`);
`decomp` = rows or columns per the C3 proof (record the outcome as a one-line note in
Profile.lean's table, R2); `carrierEval := embedded_MLP_eval (hachiProfile …)`. Plus the
paper-form check `traceCheck s Y := traceH α (2^κ) (Y * conjAut α (psi … (monomialVec s.xt))) = (2^α/2^κ) • ↑s.y`
with a `Decidable` instance via `traceHComp`.

**C3. Packed-evaluation lemma (2–4 d).** `RingSwitch/PackedEval.lean` — Theorem 2 lifted to the
multilinear level; this discharges both scheme laws and the paper-check equivalence:

```lean
theorem traceH_packPoly_eval (h2) (hk)
    (f : CMlPolynomial B (μ + (α−κ))) (x : Fin μ → B) (xt : Fin (α−κ) → B) :
    traceH α (2^κ) ((packPoly f).eval (coe ∘ arrange x xt) * conjAut α (psi … (monomialVec xt)))
      = (2^α / 2^κ) • ↑(f.eval (paper-order x xt))
```

Proof plan: (i) expand `(packPoly f).eval` by `evalSplit_eq_eval`/`eval_eq_sum`
(PolynomialEvalSplit, instantiated at the subring `B` — check `CMlPolynomial`'s ring-hom
`map`/`eval_map` support early, R1) into `Σ_i headMonomial i * ψ(block i)`; (ii) push `traceH`
through the sum (additivity); (iii) extract the `B`-valued, σ-fixed `headMonomial i` via
`traceH_smul_fixed`; (iv) apply `traceH_psi_mul_conj` per block; (v) reassemble via
`evalSplit_eq_eval` over `B`. Corollaries:
- `hachiPackingScheme_checkSound` / `_checkComplete` (the B3/B1 law props);
- `traceCheck_iff_check` (paper trace equation ⟺ generic decomposition check, via A2.6
  unit-cancellation and `Subtype.val`-injectivity).

### Phase D — §3.1 head, composed end-to-end (~3–4 days)

**D1. The head as an instance + adapter (2–3 d).** `RingSwitch/Head.lean`:
- `RingSwitchStatement := { pp, u, xl : Vector B r, xh : Vector B m, xt : Vector B (α−κ), y : B }`
  (point pre-split to match `PolyEvalStatement`'s `r`/`m` split; `xt` = packed tail).
- The head verifier **is** `packingVerifier hachiPackingScheme` specialized with
  `Aux := (pp, u)` payload (statement-shape functor around `PackedClaimStatement`), i.e. one
  message `Y' ∈ Rq` and the guarded check — **no new protocol code**, only statement plumbing.
- Zero-round σ₋₁ adapter (`ReduceClaim`, D5): `toPolyEvalStatement (s) (Y') :=
  { pp := s.pp, u := s.u, xl := coe ∘ s.xl, xh := coe ∘ s.xh, y := conjAut α Y' }`.
- `relRingSwitch` — same three-case shape as `relPolyEval`; opening case:
  `VerifiedOpening … ∧ (unpackPoly (extractedPoly Φ base o)).eval (xl ++ xh ++ xt) = ↑y`.
- Pull-back `mem_relRingSwitch_of_relPolyEval` (opening case = C3's soundness corollary; MSIS
  cases pass through) → head CWSS via B3 + `ReduceClaim.verifier_coordinateWiseSpecialSound`.
- Prover skeleton + `traceCheck_of_honest` (D12 scope).

**D2. Composition + doc fixes (0.5–1 d).** In `Hachi/Basic.lean`:
`ringSwitchEvalVerifier := headVerifier.append (adapter.append evalVerifier)` and

```lean
theorem hachi_ringSwitch_eval_coordinateWiseSpecialSound :
    ringSwitchEvalVerifier.coordinateWiseSpecialSound init impl
      (…ofIsEmpty-append chain…) (relRingSwitch …) (relOut …)
```

via **B4's guarded append** at the head seam + the existing
`eval_coordinateWiseSpecialSound`. Migrate the (now ≥3) binary appends to `seqCompose`
where factors are pure (the guarded head stays an outer binary append). Fix the "§4.1" → "§3"
cross-references (Basic.lean:37/:212, PolyEvalReduction.lean:46-47).

### Phase E — §3.2 base-field head (~3–5 days, parallel with F)

One-message, **pure** (D7) head for `f` with `ZMod q` coefficients at a `B`-valued point
(Eq. (11); reduces variables to `ℓ − α` instead of `ℓ − α + κ`):
- Message: `(y_i)_{i ≠ 0} : Fin (2^κ − 1) → B`; verifier *derives* `y₀`, outputs the claim
  `f′(x_{κ+1..ℓ}) = Σ_i y_i · Z^{Σ i_t 2^{t−1}}` with the `Z`-powers realized by
  `vElt`/`fixedBasisMap` (Eq. (7) generators, §1.2).
- Formally a second `PackingScheme`-adjacent step at the **field-level profile shape**
  `B := ZMod q`, `L := ↥(fixedSubring α (2^κ))`, basis = `Z`-powers — reuse `packMLE` here
  (coefficients are already the right shape) or the CMlPolynomial analogue per A1 conventions.
- CWSS via `ReduceClaim`/one-message-pure + NoChallenge; zero soundness error; new algebra: the
  `Z`-power reindexing lemma `f′(x) = Σ_i y_i Z^{…}` (paper §3.2 display).
- Then Phase D applies downstream unchanged.

### Phase F — Hachi's sumcheck, §4.3 (~23–32 days total; ~21–27 excluding the deferrable F1)

**F1. Field upgrade (2–5 d, or defer via D10).** Close `no_selfReciprocal_factor`
(Field.lean:207; 4-step docstring plan, blueprint difficulty 8/10) to obtain
`Field ↥(fixedSubring α (2^κ))` / `fixedSubringEquivGaloisField` under `q % 8 = 5`. Everything
in F2–F9 is stated over an abstract `[Field F]` (D10), so F1 can land last; it gates only the
final Hachi-concrete instantiation. Also needed here: `SampleableType F` / `Fintype F` transport
along the subring (finite subring of a finite ring — easy), since F's challenges are sampled.

**F2. Eq. (20) → `R^lin` adapter (2 d).** Zero-round `ReduceClaim` from QuadEval's output
statement `(QuadEvalStatement × CarrierCom × challenges)` to

```lean
structure RlinStatement (Φ) (n μ : ℕ) where
  M : PolyMatrix (Rq Φ) n μ;  yvec : PolyVec (Rq Φ) n;  bound : ℕ   -- ‖·‖∞ ≤ bound
```

assembling the Eq. (20) block matrix from `(pp, v, u, y, avec, bvec, c)` (rows = c1..c5 blocks;
`jMatrix`, `gadgetMatrix`, `tensorG1`, `tensorG` from QuadEvalGadgets). Witness map: stack
`QuadEvalResponse` into `ζ = (ŵ, flatten t̂, ẑ)`; `mapWitInv` un-stacks. Deliverables: the
block-row equivalence lemmas `rlin_iff_relOut_linear` (c1–c5 ⟺ `M ζ = yvec`) and
`range_iff_relOut_norm` (c6 ⟺ `‖ζ‖∞ ≤ γ`), then
`ReduceClaim.verifier_coordinateWiseSpecialSound` with pull-back = the ⟸ directions. This
adapter is pure — plain append.

**F3. Quotient-lift algebra (2–3 d, independent).** `Data/Lattices/CyclotomicRing/` addition
(generic, reusable by LatticeFold-style work): for the quotient `π : (ZMod q)[X] → Rq Φ`,
- `exists_quotient_witness : M ζ = y (in Rq) ↔ ∃ ρ, deg-bounds ∧ M̂ ζ̂ = ŷ + (X^d + 1) · ρ (in (ZMod q)[X])`
  (coefficient-lift of matrices/vectors; `ρ` degree `< d − 1`, plus its base-`b` gadget
  decomposition per the paper's hidden-decomposition remark);
- evaluation compatibility: `evalAt (α : F) : (ZMod q)[X] →+* F` via the `ZMod q ↪ F` embedding,
  and the degree bound `natDegree (Σ M̂ᵢⱼ ζ̂ⱼ − ŷᵢ − (X^d+1)ρᵢ) ≤ 2d − 1`;
- the interpolation kernel: a degree-`≤ 2d−1` polynomial over a field vanishing at `2d` distinct
  points is zero (Mathlib: `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`-family).

**F4. HMZ25 lift reduction — Fig. 4 / Lemma 9 (3–4 d).** Two-round reduction
`pSpec := ⟨![.P_to_V, .V_to_P], ![WCommitment, F]⟩`:
- Message: `t := Com(w̃)` — the **inner-outer commitment without initial decomposition** of the
  next-iteration witness `w̃` (Eq. (21): the `(ZMod q)`-coefficient rows of `ζ` and of the
  quotient digits `ρ_u`); reuse `InnerOuter` commitment types + `WeakBinding`.
- Challenge: `α ← F`. Output statement: `{ rlin-data, t, α }`; **output witness** (never sent,
  D6): `w̃` itself. Output relation `relLift`: `t = Com(w̃) ∧ (rows of M̂ ζ̂(w̃) − ŷ − (X^d+1)ρ(w̃)
  evaluated at α are 0) ∧ ranges(w̃)` ∨ binding/MSIS escapes.
- CWSS: `ofSpecialSound (k := 2d)` on the single scalar challenge; extraction: `2d` accepting
  branches either yield two distinct `w̃` openings of `t` (→ weak-binding escape, Lemma 7 route)
  or one `w̃` with `2d` roots (F3's interpolation) ⇒ `R^lin` membership. The star machinery
  needed is the `ℓ = 1` case (`isSpecialSoundFamily_one_iff_injective`); generalize
  `CoordinateWise.SingleRound`'s star readers from `Fin (2^r) → C` challenges to plain scalar
  challenges (small refactor: its `pSpec` at `r := 0` + `Equiv.funUnique`, or a scalar twin).

**F5. Constraint encoding — Eqs. (21)–(23) (2–3 d).** Definitions only (no protocol):
`w̃` as a `CMlPolynomial F (log (μ+n) + log d)`-shaped table per Eq. (21) (index bookkeeping via
A1's conventions); `α̃(ℓ) = α^ℓ` and `M̃_α(i,u)` as multilinear extensions (`mle`-style, using
the repo's MLE infrastructure); the batched `H_α` (Eq. (22)) and `H_0` (Eq. (23)); the sumcheck
polynomials `F_{0,τ₀} = eq̃·range-product·1_{≤μ}` and `F_{α,τ_α} = w̃·α̃·(Σ eq̃ M̃_α)`, expressed
through `SumcheckMultiplierParam` with a Hachi `Context` type carrying scalar seeds `(ρ₀,ρ_α)`,
their derived Kronecker points `(τ₀,τ_α)`, and `(t, α, public M̃_α data)` (Context is generic,
§1.4). **Pin the exact per-round degree here**: the range
product `∏_{j=-(b-1)}^{b-1} (X − j)` has `2b−1` factors; with the multilinear `w̃` and `eq̃`
multiplier the round polynomial degree is `2b`, hence `k = 2b+1` transcripts per round
(verified independently; the repo docstring's "Q of degree 2b / round degree 2b+1" at
Structured.lean:79-80 is off by one against its own printed product — fix it here — and the
paper's "b+1 elements per round" matches neither, likely an unstated digit-range convention).
Thread the result as `d₀ := degCombinator + 1` uniformly; everything degree-parametric
downstream, so any residual convention change costs a constant rename. **Also pin the challenge
arities here**: the paper's `τ₀ ← F^{log μ + log d}` is in tension with `w̃`'s own index arity
`log(μ+n) + log d` (Eq. (23)'s `eq̃(t,(u,ℓ))` needs `t`-arity equal to `w̃`'s index arity; the
`1_{≤μ}` indicator restricts the *range check*, not the index space). Pin these as `m₀,m_α` and
set F6's interpolation parameter to `D := max(2^m₀,2^m_α)`; require `D ≤ |F|`.

**F6. One-round Kronecker zero-check (3–4 d).**

> **Superseded (5 August 2026).** This milestone is **not** what was built, and the Lean lemmas it
> plans below no longer exist. The formalization draws each of the `m₀ + m₁` coordinates in its own
> two-child scalar round and extracts with the nested-tree zero test
> (`NestedEvaluationTree.eq_zero_of_vanishes_comp`); the one-round Kronecker rendering was rejected
> because `k = D = 2^{m₀}` makes the branching factor exponential. `powAlgHom` and its degree bound
> survive in `LinearMvExtension.lean` (they predate this plan and serve Reed–Solomon), but the
> Kronecker-specific lemmas — injectivity on the multilinear subtype, curve-evaluation
> compatibility, root counting — have been removed. Current status:
> [`docs/kb/audits/noz26-zero-check-lemma10.md`](docs/kb/audits/noz26-zero-check-lemma10.md).
> The text below is retained as the record of the rejected design.

Keep Fig. 5 as one challenge round, but sample
two independent scalar seeds `(ρ₀,ρ_α) ∈ F²` and derive

```
τ₀ := (ρ₀, ρ₀², ρ₀⁴, …, ρ₀^(2^(m₀-1))),
τ_α := (ρ_α, ρ_α², ρ_α⁴, …, ρ_α^(2^(m_α-1))).
```

This block runs at the fixed `α` produced by F4. Keep F4's `α` fork as an earlier/nested CWSS
node even if the concrete transcript serializes `α,ρ₀,ρ_α` contiguously: one flat three-coordinate
star does not interpolate the mixed `(α,ρ_α)` dependence.

Use a single `CWSSStructure` with `ℓ=2` and `k=D=max(2^m₀,2^m_α)`, hence `2D−1` branches.
The mathematical work is:

- reuse `LinearMvExtension.powAlgHom` and
  `powAlgHom_of_restrict_degree_natDegree` from
  `ArkLib/Data/MvPolynomial/LinearMvExtension.lean`;
- prove `powAlgHom` injective on the per-variable-degree-`≤1` subtype (the same file's
  `linearMvExtension` inverse machinery supplies the coefficient argument);
- prove evaluation compatibility with the derived Kronecker point;
- generalize the single-round CWSS assembly helper beyond its current `k=2` specialization, or
  prove the local `ℓ=2,k=D` transcript-tree theorem directly;
- use `D` distinct roots on the first star arm for `H₀` and on the second arm for `H_α`; differing
  leaf openings return the existing weak-binding/MSIS escape;
- bridge `H₀ ≡ 0 ∧ H_α ≡ 0` to the entrywise range and row constraints, while the accepting leaf
  claims `H₀(τ₀)=H_α(τ_α)=0` feed F7 unchanged.

The equality-kernel multipliers and sumcheck formulas remain exactly those of Eqs. (22)–(23).
What changes is the challenge distribution: the points lie on Kronecker curves rather than being
uniform in the full vector spaces. Record the `D/|F|` error scale and require a larger concrete
extension or same-message parallel repetition if the `D≈2^26`, `|F|≈2^128` instance must meet a
full 128-bit target.
The shared-seed plain-`D`-SS variant is a smaller optional fallback; the independent-seed CWSS
version is the default because it preserves cross-block independence. Full proof and alternatives:
[`HACHI_LEMMA10_GAP.md`](HACHI_LEMMA10_GAP.md).

**F7. Per-round sumcheck CWSS on the substrate (5–6 d; the second heart).** New
`Sumcheck/Structured/CWSS.lean` (or Hachi-local first, promoted later):

```lean
theorem guardedRound_coordinateWiseSpecialSound (d : ℕ) (i : Fin ℓsc) (hcons : …) :
    (guardedRoundOracleVerifier … d i).coordinateWiseSpecialSound init impl
      (CWSSStructure.ofSpecialSound (fun _ => d + 1) …)
      (sumcheckRoundRel … i.castSucc) (sumcheckRoundRel … i.succ)
```

(stated over the **guarded** round verifier introduced below — per R10 the theorem is
unprovable for the substrate's pure-with-dummy `roundOracleVerifier`).

- New per-round relation family `sumcheckRoundRel` in the CWSS currency: "committed `w̃` opens
  `t` ∧ `H`-projection structural invariant ∧ `sumcheckConsistencyProp` at the current target"
  (∨ escapes) — the CWSS analogue of `masterKStateProp`, but Hachi-shaped and paper-faithful
  (Lemma 11's statement).
- Extraction per round: `d+1` distinct scalar challenges; branches share the message `g_i`;
  either two branches disagree on the (relation-level) `w̃` ⇒ binding escape, or the univariate
  `Σ_b H(a_{<i}, X, b) − g_i(X)` (degree ≤ d) has `d+1` roots ⇒ ≡ 0 (Lemma 11 verbatim).
- **Guarded round verifier** (new substrate variant, R10): the existing pure-with-dummy
  `roundOracleVerifier` cannot support per-round CWSS — the `Σ_b g_i(b) = target` check is
  challenge-independent (the message is shared by all siblings), so on a failed check *all*
  `d+1` sibling branches collapse onto the identical dummy statement and the extraction loses
  the tie between `g_i` and the *old* target (which the next round's statement drops). Add
  `guardedRoundOracleVerifier` (same prover, same `pSpec`, `verify := unless check do failure`)
  to `Sumcheck/Structured/SingleRound.lean`; Binius's RBR treatment keeps the dummy variant.
  A guarded verifier makes failed-check nodes non-accepting outright, which is exactly the
  paper's "valid transcripts" premise in Lemma 11.
- The **paired round** (D9): wrapper `pairedRoundOracleReduction` with message
  `(L⦃≤d₀⦄[X]) × (L⦃≤d_α⦄[X])`, one challenge, componentwise `getSumcheckRoundPoly`; its CWSS at
  `k = max d₀ d_α + 1` from the single-poly lemma applied twice on the same challenge family.
- Loop composition: B4's guarded n-ary `seqCompose_treeSpecialSound_of_guard` over `i : Fin ℓsc`
  (round verifiers are guarded), seam relations as above, `Nonempty` witness instances exist
  (QuadEval-precedent `⟨0,…⟩` instances).

**F8. Final-evaluation step (2–3 d).** One-message reduction closing the sumcheck (paper Fig. 7
tail; the analogue of `RingSwitching/SumcheckPhase`'s final step, but CWSS and Hachi-shaped):
- Message: `y′ := w̃(a₁,…,a_ℓsc)` in the clear. Verifier (**guarded**, D6): evaluates the
  *public* `M̃_α`/`eq̃`/`α̃` factors at the challenge point (the paper's expensive `O(√(2^ℓ)λ)`
  step) and checks both final sumcheck targets against `P(a)·Q(y′)`; on success outputs the
  **evaluation claim** `{ t, point a, claim y′ }` for the committed `w̃` (∨ carries the escapes).
  The guard is forced by the same argument as the §3.1 head: the check reads the final sumcheck
  targets, which the output statement drops, so it can live neither downstream nor in a
  pull-back. (In the *non*-recursive base case, where `relWEvalClaim` is the chain's final
  relation, a pure verifier + check-in-final-relation variant is also sound; keep the guarded
  form so Phase G's recursion composes uniformly.)
- Range-fact extraction lemma (needs `IsDomain F`): from `H_0 ≡ 0`, entrywise
  `∏_{j}(w̃(u,ℓ) − j) = 0` ⇒ `w̃(u,ℓ) ∈ [−(b−1), b−1]` — the field-side of c6 for the *next*
  iteration's norm bound.

**F9. §4.3 chain assembly (2 d).** Compose F2 ++ F4 ++ F6 ++ F7-loop ++ F8 by
append/seqCompose; top-level theorem

```lean
theorem hachi_lin_sumcheck_coordinateWiseSpecialSound :
    (linSumcheckVerifier …).coordinateWiseSpecialSound init impl (…structure…)
      (relOut …)                 -- Eq. (20) + ranges, QuadEval's output relation
      (relWEvalClaim …)          -- opening of t evaluates to y′ at a, + escapes
```

and its append onto `hachi_ringSwitch_eval_coordinateWiseSpecialSound` (D2), yielding the full
one-iteration chain `relRingSwitch → relWEvalClaim`. Knowledge-error accounting explicitly
out of scope (D12/R6).

### Phase G — §4.5 recursion handoff (~4–6 days, after F)

- **G1 (closed).** `cInfNorm_psi_le` proves Lemma 6, `‖ψ(a)‖∞ ≤ 2β`, using the support of
  `R_q^H` elements and the fact that at most two packed summands contribute to each coefficient.
  This is the bound needed to commit `ψ(ŵ)` without re-decomposition.
- **G2.** Partial-evaluations step for `mle[w̃]` (Eq. (24)) — the Phase E head re-instantiated at
  the `eq̃`/evaluation convention (paper uses `eq(j, a₀)` here, not monomials — the
  `PackingScheme.weights` knob absorbs exactly this difference).
- **G3.** The `Z`-power packing `ŵ_j` (Eq. (25)) + `ψ(ŵ)` + the trace handoff
  `p := eᵀ(σ₋₁(ψ(f))ᵀ ⊗ I)ψ(ŵ)` (Eqs. (27)–(28)) — `hachiPackingScheme` at the next ring
  dimension `d′`, producing the next-iteration `QuadEvalStatement`/`PolyEvalStatement`. Output:
  `relWEvalClaim → relPolyEval(next)` adapter, closing the recursion loop of Fig. 7 → Fig. 3.
  As a packing-head instance, G3's verifier is **guarded** (D3/D6): its trace check reads
  `(a, y′)`-derived data that the next-iteration statement drops — the fourth guarded seam
  (§5 row 10), composed by B4's guarded append.

### Phase H — Docs, blueprint, hygiene (~1–2 days, same PRs as the code)

- `docs/wiki/repo-map.md`: new `RingSwitching/{PackingScheme,Packing,Relocation}.lean`,
  `Hachi/RingSwitch/`, `Sumcheck/Structured/CWSS.lean` (CLAUDE.md guardrail: same PR).
- KB: `docs/kb/papers/NOZ26.md` gap list (:80-86) and `docs/kb/concepts/ring-switching.md`
  (mark the Hachi instance done; record the `decomp` rows/columns outcome and the `κ` dictionary).
- Blueprint: `blueprint/src/proof_systems/hachi_ring_switching.tex` +
  `hachi_sumcheck.tex`, companioning `lattices/hachi_subfield.tex` and
  `proof_systems/ring_switching.tex`.
- Optional agreement lemma `packPoly ↔ packMLE (hachiPackBasis)` (needs a
  `CMlPolynomial ↔ MvPolynomial` bridge; defer if absent, document divergence).
- Update `HACHI_RING_SWITCHING_COMPARISON.md` for the seam finding — this touches more than §4a:
  §1's "overlap … in nothing that is on the wire" and the "same algebra, different protocol"
  slogan, §4a's title/table (the first message and first check *do* coincide under the profile;
  divergence starts at the batching challenge), and the stale "plan milestone M1" reference
  (now C1). The corrected slogan: *same algebra, same first round, different discharge of the
  residual carrier claim.*

## 5. The composed chain — seams and currencies

| # | Reduction | pSpec | Verifier | CWSS structure | relIn → relOut | Composed by |
|---|---|---|---|---|---|---|
| 0 | §3.2/§4.5 partial-evals head (E/G2) | 1 msg | pure (derive-`y₀`) | any `D` (no challenge) | ext-field claim → packed-field claim | append (pure) |
| 1 | §3.1 packing head (C/D1) | 1 msg: `Y'` | **guarded** | `ofIsEmpty` | `relRingSwitch` → packed-claim | **guarded append (B4)** |
| 2 | σ₋₁ adapter (D1) | 0 rounds | pure | any `D` | packed-claim → `relPolyEval` | append (pure) |
| 3 | bridge (done) | 0 rounds | pure | any `D` | `relPolyEval` → QuadEval `relIn` | append (pure) |
| 4 | QuadEval (done) | msg + vector challenge | pure | `foldStructure` (ℓ=2^r, k=2) | `relIn` → `relOut` (Eq. 20) | append (pure) |
| 5 | R^lin adapter (F2) | 0 rounds | pure | any `D` | `relOut` → `R^lin` | append (pure) |
| 6 | HMZ25 lift (F4) | msg `t` + challenge `α` | pure | `ofSpecialSound k=2d` | `R^lin` → `relLift` | append (pure) |
| 7 | zero-check (F6) | 1 challenge `(ρ₀,ρ_α) ∈ F²` | pure | `ℓ=2`, `k=max(2^m₀,2^m_α)` | `relLift` → sumcheck targets | append (pure) |
| 8 | paired sumcheck ×ℓ_sc (F7) | (msg pair + challenge) each | **guarded** | `ofSpecialSound k=maxdeg+1` | round rels | **guarded seqCompose (B4)** |
| 9 | final eval (F8) | 1 msg: `y′` | **guarded** | any `D` | last round rel → `relWEvalClaim` | **guarded append (B4)** |
| 10 | §4.5 handoff (G3) | 1 msg (+ commit) | **guarded** | `ofIsEmpty` (as row 1) | `relWEvalClaim` → `relPolyEval`(next) | **guarded append (B4)** |

Four guarded seams (rows 1, 8, 9, 10) — exactly the places a runtime check reads data the next
statement type drops (D6); row 10 is row 1's packing head re-instantiated at the next ring
dimension, so it inherits the guard for the same reason. Everything else is pure and composes
with the existing theorems. Every relation carries the same escape disjuncts (weak-binding / MSIS), threaded as
in `relPolyEval`/`relIn`/`relOut` today.

## 6. Acceptance criteria

- **B2/B3**: repo builds green with the split module; FRIBinius still compiles; the *only*
  behavior change is `failure` vs dummy-state in the packing check (recorded in the PR
  description); `PackingPhase.coordinateWiseSpecialSound_of_checkSound` sorry-free.
- **B4**: guarded append theorem sorry-free; existing `append_*` theorems untouched (byte-level).
- **C1–C3**: `hachiProfile`, `hachiPackingScheme_checkSound/_checkComplete`,
  `traceCheck_iff_check` sorry-free; Fig. 9 parameter `example` compiles.
- **D2**: `hachi_ringSwitch_eval_coordinateWiseSpecialSound` sorry-free — extension-field claim
  down to Eq. (20), with zero added soundness error from the head.
- **Phase E**: the base-field head's CWSS theorem sorry-free, with the derive-`y₀` verifier
  proven pure (`IsPure` instance) and the `Z`-power reindexing lemma checked on a small concrete
  example (`decide`, `κ = 1`); composition with the Phase D chain compiles.
- **F-phase**: each of F2–F8 lands with a sorry-free CWSS theorem at its seam (F-milestones may
  land over `[Field F]` before F1 closes); F9's composed theorem sorry-free modulo F1's
  instantiation.
- **Phase G**: G1 (`cInfNorm_psi_le`) closed; G2/G3 each land with a sorry-free CWSS theorem;
  the recursion-closing adapter type-checks against `relPolyEval` at dimension `d′` (an
  `example` instantiating two nested iterations at Fig. 9-shaped parameters).
- Throughout: `./scripts/validate.sh` green (add `--lint` before PR); `git add` new files before
  validating; never hand-edit `ArkLib.lean`; wiki/KB updated in the same PR as the code
  (CLAUDE.md guardrails).

## 7. Risks and open points

- **R1 — CMlPolynomial API gaps** (C3, F5): `CMlPolynomial.map` for ring homs **exists**
  (CompPoly `Multilinear/Basic.lean:203`); the `eval_map`-style compatibility lemma for the
  subring coercion was not sighted and may need adding locally or upstreaming. Low-medium;
  confirm on the first C3 day.
- **R2 — rows-vs-columns in the Hachi check** (C2): whether the generic check reads
  `decomposeRows` or `decomposeColumns` of the carrier message depends on where the σ₋₁ twist
  lands (message = `σ₋₁(Y_paper)`, D5). The `PackingScheme.decomp` field makes this a knob, and
  C3's law proof settles it; budget half a day of algebraic care, don't guess. Medium.
- **R3 — shared-infrastructure changes** (B2, B4, D3): the module split, the guarded append, and
  the failure-vs-dummy change all touch code other people build on. All affected soundness proofs
  are currently sorried (verified §1.3), so the technical risk is low, but coordinate with
  maintainers before B2; fallback designs are recorded (D2-fallback, B4 one-off hand proof).
- **R4 — index-convention transposition bugs** (A1, C2, F5): mitigated by pinning conventions
  first with `decide` examples; treat any mid-proof index cast as a red flag.
- **R5 — `κ` naming collision**: paper `κ` (log extension degree) vs profile rank (`α − κ`).
  Spell `α − κ` out everywhere; the KB already warns.
- **R6 — CWSS ≠ knowledge soundness**: the composed theorems give tree extraction; the
  CWSS → knowledge-error bridge (FMN24 Lemma 4), `Commitment.extractability`, and Fiat–Shamir
  remain separate tracked work (Basic.lean:209-211). Not in this plan.
- **R7 — paper Lemma 10's star extraction is insufficient as stated.** Full standalone analysis
  (constructive protocol-level counterexample and repair approaches with proofs/refutations):
  [`HACHI_LEMMA10_GAP.md`](HACHI_LEMMA10_GAP.md). In brief: for a multilinear
  `H(t) = Σ_i eq̃(t,i)·c_i`, vanishing on a coordinate-wise star (center + `k−1` siblings per
  coordinate) does **not** imply `H ≡ 0`: `H(t₁,t₂) = (t₁−a)(t₂−b)` vanishes on every star
  centered at `(a,b)` yet is non-zero. The paper's `SS(F_{q^k}, 2, max(2d, 2b−1))` phrasing (vs
  its own "vector of log μ + log d + log n coordinates" text) does not repair this. F6 instead
  keeps one round but restricts each vector point to the Kronecker curve
  `κ_m(ρ)=(ρ,ρ²,ρ⁴,…)`. The pullback of an `m`-variate multilinear polynomial is an injective
  univariate polynomial of degree `<2^m`; an `SS(F,2,D)` star with
  `D=max(2^m₀,2^m_α)` therefore interpolates the two identities on its two scalar-seed arms.
  This changes the point distribution, not the checked equations or downstream sumchecks, and
  worsens the error scale from logarithmic-over-`|F|` to `D/|F|` (about 102 bits for the paper's
  `D≈2^26`, `|F|≈2^128` concrete setting). Flag the distribution and concrete-field adjustment
  explicitly. **This is the one place the formalization deliberately changes the paper's
  protocol in order to repair its proof.**
- **R8 — degree bookkeeping** (F5): repo docstrings say round degree `2b+1`, the factor count
  gives `2b`, the paper's proof-size table suggests `b+1` coefficients. Everything downstream is
  degree-parametric; F5 pins the true value once, early.
- **R9 — remaining Lemma 5 gate**: `no_selfReciprocal_factor` gates F1 (and only F1, given
  D10). The former Lemma 6/G1 gate `cInfNorm_psi_le` is closed.
- **R10 — the substrate's pure-with-dummy round verifier is CWSS-incompatible.** Because the
  round check `Σ_b g_i(b) = target` depends only on the shared message and the input statement
  (not the challenge), a failed check sends *every* sibling branch of a tree node to the
  identical dummy statement; an adversary can then build a fully accepting structured tree from
  which no extractor can recover the tie between `g_i` and the previous round's target (the
  next statement drops it). The dummy convention is fine for the RBR/KState treatment (where
  the state function watches the transcript), but Hachi's CWSS treatment needs the guarded
  variant (F7) and the guarded composition theorems (B4). This is a framework-level insight
  worth a docstring in `Sumcheck/Structured/SingleRound.lean` regardless of Hachi.
