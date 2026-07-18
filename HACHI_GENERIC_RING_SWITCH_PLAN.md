# Generic Ring Switch × Hachi — Reconciliation & Implementation Plan

Target: extend `origin/feat/generic-ring-switch`'s `RingSwitching/Generic/` layer so it
accommodates **Hachi's §3.1 packing head** (NOZ26, ePrint 2026/156), and build that head —
guarded, zero-challenge, CWSS — composed onto the existing sorry-free chain
(`eval_coordinateWiseSpecialSound`, [Basic.lean:136](ArkLib/Commitments/Functional/Hachi/Basic.lean#L136)).
This plan supersedes Phases B–D of [`HACHI_RING_SWITCHING_PLAN.md`](HACHI_RING_SWITCHING_PLAN.md)
(the `PackingScheme`-over-`Profile` design); Phases A, E, F, G of that plan are unaffected except
for the deltas listed in §10 (Phase 7, item 3). Every file/line/signature anchor below was re-verified on the working
tree and on `origin/feat/generic-ring-switch` (2026-07-09); the working tree is branch
`hachi-polynomial-quadratic-eq`.

---

## 0. Overview — what changes and why

The branch `feat/generic-ring-switch` (author: Alexander Hicks; 3 commits over main; purely
additive, +1351 lines across 16 files) generalizes ring switching via a new
`RingSwitching/Generic/` layer: `RingSwitchCarrier` (packing algebra `P` + opening algebra `E`,
everything derived from two `Basis` witnesses), `BatchingStrategy` (challenge + Schwartz–Zippel
`separates` bound), an anchored relation chain `openingClaimRel → sliceRel → sumcheckClaimRel`,
and a `PackedCommitment`/`DenseMLPCS` PCS interface whose soundness field is **RBR knowledge
soundness**. Its docstrings envision Hachi as "the S8 non-domain sibling": a `BatchingStrategy`
instance over `R_q` supplying its own `separates` proof.

That roadmap mis-models Hachi. Hachi's §3 ring switch is **deterministic**: the evaluation point
is engineered to be subfield-valued, so the reduction is one prover message `Y ∈ R_q`, one trace
check (Theorem 2), **zero challenges, zero sumcheck, zero soundness error** — and the residual
claim is already a native `R_q` evaluation claim consumed by the existing Fig. 3 chain. There is
nothing to batch and nothing to relocate. Moreover the Hachi chain's security currency is CWSS
(coordinate-wise special soundness, composed via `CWSSPackage`/`▷`), not RBR, and the repo has no
RBR↔CWSS bridge.

**The five changes, and why each is necessary:**

1. **Add a deterministic "packed-claim" exit stage to `Generic/`** (new `PackedClaim.lean` +
   relation re-anchor). *Why necessary:* the branch's pipeline is hardwired
   claims → eq-slices → batching → sumcheck → RBR-PCS; Hachi exits after the packing check, and
   today that exit does not exist as a stage, a relation, or a lemma. Without it, Hachi cannot be
   an instance of the generic layer at all — it would have to fake a degenerate
   `BatchingStrategy`, which models an identity *fold*, not a trace *check*.

2. **Retarget the "S8 Hachi sibling" docs.** *Why necessary:* three docstrings on the branch
   (Batching.lean ×2, Relations.lean sanity) present Hachi as a future non-domain *batching*
   instance. Left standing, the branch's own roadmap contradicts the protocol it claims to host,
   and future work would build the wrong thing. The `CommRing`-only vocabulary is right; the
   pipeline position is wrong.

3. **Close the small lattice-layer gaps** (`psi_smul`, a bundled `psiLinearEquiv`,
   `Nontrivial ↥(fixedSubring …)`, a named unit/cancellation lemma, one index-equiv). *Why
   necessary:* the head's check reads the ψ-coordinates of the prover message; ψ exists only as a
   bare bijective function today (`psi_bijective`), with no scalar-compatibility lemma and no
   bundled inverse — the coordinate map `psiInv` cannot even be written down without them.

4. **Build the head itself**: the unpack algebra (`unpackPoly` + the Theorem-2-powered
   `unpackPoly_eval` / `traceCheck_iff`), the guarded 1-message verifier, `relRingSwitch`, its
   CWSS theorem, and a **guarded CWSS append** in the framework. *Why necessary:* (a) the head's
   check consumes `(xt, y)`, which the downstream `PolyEvalStatement` drops — the check can live
   neither in a downstream relation nor in a pull-back, so the verifier must be able to *reject*
   (`failure`), and (b) every existing CWSS composition theorem
   ([Composition.lean:414](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L414))
   requires a **totally pure** left verifier — a guarded head is inadmissible without the new
   guarded append. The Basic.lean TODO block explicitly requests this
   ("Guarded subprotocols need a guarded variant of `▷`", Basic.lean:256-272).

5. **Compose into the chain** (`ringSwitchChain`, extending `evalChain`). *Why necessary:* the
   deliverable is the end-to-end theorem — extension-field-style claim down to Eq. (20) — and the
   chain's composition discipline (`CWSSPackage`, syntactic `rfl` seams at
   `relPolyEval 𝓜(q,α) …`) imposes exact statement/relation shapes on the head that must be built
   to fit, not adapted after the fact.

**What this plan deliberately does NOT do** (and why): it does not route Hachi's proofs through
the branch's `MultilinearPoly`-based generic lemmas. The Hachi chain speaks `CMlPolynomial`
(computable, `Vector`-indexed: `relPolyEval`'s eval claim is
`CMlPolynomial.eval (extractedPoly Φ base o) (s.xl ++ s.xh) = s.y`), the branch speaks
`MultilinearPoly` (an `MvPolynomial` subtype), and CompPoly's `toMvPolynomial` bridge **has no
eval-agreement lemma** (verified missing). Building that bridge is real work with zero payoff for
soundness. Instead: the generic layer gets the stage + value-level lemmas in its own idiom
(consumable by Binius later), and the Hachi head proves its pull-back natively on
`CMlPolynomial` via the existing `PolynomialEvalSplit` machinery. The `hachiCarrier` instance
(Phase 7) pins the correspondence; the polynomial-level bridge is recorded as optional hygiene.

**Phase order and dependencies:**

```
Phase 0 (branch setup)
  → Phase 1 (Generic/ stage + docs)          [independent of 2–6]
  → Phase 2 (lattice glue)
    → Phase 3 (unpack algebra, the heart)
      → Phase 4 (head reduction + CWSS)
  → Phase 5 (guarded append, framework)      [independent of 1–4; needed by 6]
      → Phase 6 (chain assembly)
  → Phase 7 (carrier instance + hygiene)
```

Estimated effort: 0: 0.5 d · 1: 1.5 d · 2: 1.5 d · 3: 3–4 d · 4: 2–3 d · 5: 2–3 d · 6: 1 d ·
7: 1 d. Total ≈ 12–15 focused days.

---

## 1. Verified ground truth (do not re-derive; re-verify only if a step fails)

### 1.1 The branch (`origin/feat/generic-ring-switch`, head `c14c1827`)

- Full footprint: 16 files, +1351/−12, **zero edits to existing `RingSwitching/` files**. New:
  `Generic/{Carrier,Packing,Batching,Recombine,Relations}.lean`, `ArkLib/Data/Module/Basis.lean`
  (`Module.Basis.sum_smul_bijective/injective`). Modified: `ArkLib.lean` (+6 imports, generated),
  `Data/MvPolynomial/{Degrees,Multilinear}.lean` (3 new lemmas incl. `MLE_eval_eq_sum_eqTilde`,
  `MLE_totalDegree_le`), `Data/Probability/Instances.lean` (**breaking**:
  `prob_schwartz_zippel_mv_polynomial` gains explicit `(d : ℕ)` arg — no callers on HEAD, safe),
  `Binius/BinaryBasefold/Basic.lean` + `FRIBinius/{CoreInteractionPhase,Prelude}.lean` (the R7
  `witnessNovelCoeffs` semantic fix + `biniusCommitsTo`), `references.bib`, `repo-map.md`,
  `docs/kb/concepts/ring-switching.md` (+81, "The Generic layer").
- **Merge into HEAD is conflict-free** (verified `git merge-tree`): only `ArkLib.lean`,
  `references.bib`, `repo-map.md` changed on both sides, all auto-merged. Caveat: the dry run
  tested committed HEAD; the working tree is dirty.
- Key signatures (Carrier.lean): `RingSwitchCarrier B` with fields
  `P E ιP ιE : Type`, `[commP commE : CommRing] [algP algE : Algebra B ·] [ntP ntE : Nontrivial ·]
  [ftP ftE : Fintype ·]`, `packBasis : Basis ιP B P`, `openBasis : Basis ιE B E` (all registered
  `attribute [instance]`); `packedMLE Ps = ∑ i, packBasis i • componentWise_embed_MLE B m
  (algebraMap B car.P) (Ps i)`; `bridge_eqTilde` proven.
- Packing.lean: `packedMLE_eval (Ps) (pt : Fin m → B) : MvPolynomial.eval (fun i => algebraMap B
  car.P (pt i)) (car.packedMLE Ps).val = ∑ i, algebraMap B car.P ((Ps i).val.eval pt) *
  car.packBasis i` — **proven, CommRing-only, base-embedded points only** (docstring forbids
  assuming more). `curryFamily` curries the **first** κ variables, `h_l : ℓ = ℓ' + κ`.
- Batching.lean: `BatchingStrategy P W` fields `Challenge [Fintype] [Nonempty]`,
  `weight : Challenge → W → P`, `error : ℝ≥0`, `separates : ∀ s s', s ≠ s' → Pr_{c ←$ᵖ
  Challenge}[∑ u, weight c u * s u = ∑ u, weight c u * s' u] ≤ error`. Instances
  `gammaPowers`/`eqFold` gated `[IsDomain P] [Fintype P]` at the section level (line 108).
- Relations.lean: `openingClaimRel`/`sliceRel`/`sumcheckClaimRel` + `sumcheckClaim_of_slices`
  (proven); `PackedCommitment` (`commitsTo` + `commitsTo_functional`, `commitsTo_not_top` proven);
  `DenseMLPCS` with **unfilled** `perfectCompleteness`/`rbrKnowledgeSoundness` obligations.
- Hachi/S8 docstrings to retarget: Batching.lean module docstring bullet, `BatchingStrategy`
  docstring (lines 60-69), sanity comment before line 246; Relations.lean:312-314.
- `git grep coordinateWiseSpecialSound` over the branch's `RingSwitching/` is **empty**; the
  branch's CWSS dir has only `Basic.lean` + `Composition.lean` (no `NoChallenge`, no
  `SeqCompose`, no `SingleRound`, no `Package`).

### 1.2 CWSS infrastructure (working tree — strictly ahead of every remote on these files)

- Files present: `Basic, Composition, SeqCompose, NoChallenge, SingleRound, Package` (Package.lean
  is **staged-new, working-tree only**; `origin/cwss-components-infra` lacks `ofIsEmpty`,
  `SingleRound`, `Package` — build on THIS branch, not infra).
- `Verifier.coordinateWiseSpecialSound (D : CWSSStructure pSpec) relIn relOut` =
  `treeSpecialSound init impl (CWSSStructure.toShape D) relIn relOut`
  ([Basic.lean:212](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L212));
  call shape `V.coordinateWiseSpecialSound init impl D relIn relOut`.
- `CWSSStructure.ofIsEmpty` ([NoChallenge.lean:45](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/NoChallenge.lean#L45));
  no-challenge bridge `Verifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx`
  (NoChallenge.lean:118-127) with premise
  `h : ∀ stmtIn tr, Pr[(· ∈ relOut.language) | …V.run stmtIn tr…] = 1 → (stmtIn, e stmtIn tr) ∈ relIn`
  and extractor `e : StmtIn → FullTranscript pSpec → WitIn` — **note: `e` sees only the
  transcript, not the downstream witness**. For reductions whose input witness must be built from
  the *output* witness (ours), the template is instead
  `ReduceClaim.verifier_coordinateWiseSpecialSound`
  ([ReduceClaim.lean:186](ArkLib/ProofSystem/Component/ReduceClaim.lean#L186), hypothesis
  `hRel : ∀ stmtIn witOut, (mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn`,
  requires `[Nonempty WitIn]`) and `SendWitness.verifier_coordinateWiseSpecialSound`
  (SendWitness.lean:109, non-oracle 1-message P→V) — **Phase 4 mirrors these proofs**.
- Pure append: `Verifier.append_coordinateWiseSpecialSound` (Composition.lean:414-428), purity
  hypothesis exactly `hV₁ : ∀ stmt tr, V₁.verify stmt tr = pure (verify₁ stmt tr)`. Helpers to
  generalize: `append_run_pure_left` (:311-319), `pure_accepting_of_mem` (:325-332), converse
  `mem_of_pure_accepting` (SeqCompose.lean:53-60). Generic layer: `append_treeSpecialSound`
  (:366-375) consumes `hV₁` at ~:396 and ~:407.
- Chain packaging: `CWSSPackage` (Package.lean:54-69; fields `verifier struct relIn relOut
  isPure isCWSS`), `CWSSPackage.append` with autoparam seam `(hseam : L₁.relOut = L₂.relIn := by
  rfl)`, infix `▷` (scoped `CoordinateWise`).
- The chain is **plain `Verifier`** (no oracle statements): `bridgeVerifier : Verifier …`,
  QuadEval `verifier : Verifier …`, composed by `Verifier.append`.

### 1.3 The Hachi chain seam (working tree)

- Namespace `ArkLib.Lattices.Ajtai.InnerOuter`; **never** `open ArkLib.Lattices` (ambiguous `⬝ᵥ`);
  `open WeakBinding` for `VerifiedOpening`.
- `PolyEvalStatement` (PolyEvalReduction.lean:81-92): fields `pp : Hachi.PublicParamsD Φ innerRows
  (2^m) messageDigits outerRows (2^r) innerDigits dRows`, `u : Commitment Φ outerRows`,
  `xl : Vector (Rq Φ) r`, `xh : Vector (Rq Φ) m`, `y : Rq Φ`.
- `relPolyEval Φ base βSq γ κ` (:151-159), opening case:
  `VerifiedOpening Φ base βSq γ κ s.pp.toPublicParams s.u o ∧
   CMlPolynomial.eval (extractedPoly Φ base o) (s.xl ++ s.xh) = s.y`; msisB/msisD cases via
  `ModuleSIS.relation`. `extractedPoly Φ base o : CMlPolynomial (Rq Φ) (r + m)` (:133-136).
- `evalChain` (Basic.lean:115-128) = `bridgePackage … ▷ quadEvalPackage …`; top theorem
  `eval_coordinateWiseSpecialSound` (Basic.lean:136-149). **Seam discipline**: a new head's
  `relOut` must be *syntactically*
  `relPolyEval 𝓜(q,α) (b : ZMod q) (quadEvalBetaSq γ b zDigits ((𝓜(q,α)).φ.natDegree) m
  messageDigits) γ (2 * ω)` with output statement exactly
  `PolyEvalStatement 𝓜(q,α) innerRows messageDigits outerRows innerDigits dRows m r` for the
  `rfl` autoparam to close. Section variables at Basic.lean:103-106; `b ω γ` are implicit.
- TODO block at Basic.lean:256-272 names exactly this work; header diagram at :51-74 already
  slots "§3.1 ring-switch packing head — planned (guarded, 1 msg)".

### 1.4 Lattice layer (working tree)

- `psi (α k) (a : Fin (2^α / k) → fixedSubring (R := R) α k) : Rq (powTwoCyclotomic α)`
  (Subfield/Packing.lean:61-64) — a plain `def` (sum of `↑(a j) * Xpow (packExp α k j.val)`).
  `psi_add` ✓ (:74), `psi_zero` ✓, `psi_bijective (α κ) (h2 : (2 : ZMod q) ≠ 0)
  (hk : 2 * 2^κ ∣ 2^α)` ✓ (Bijectivity.lean:34). **`psi_smul` MISSING. Any bundled
  LinearMap/LinearEquiv MISSING** (grep-verified).
- **Theorem 2**: `traceH_psi_mul_conj (α k) (h2 : (2 : R) ≠ 0) (hk2pow : ∃ κ, k = 2^κ)
  (hk : 2 * k ∣ 2^α) (a b : Fin (2^α / k) → fixedSubring (R := R) α k) :
  traceH α k (psi α k a * conjAut α (psi α k b)) = (2^α / k) • ((∑ i, a i * b i : fixedSubring
  (R := R) α k) : Rq (powTwoCyclotomic (R := R) α))` — proven
  (TraceInnerProduct.lean:229-234). RHS is ℕ-`nsmul` of a coerced subring sum.
- `fixedSubring (α k) : Subring (Rq (powTwoCyclotomic α))` (FixedSubring.lean:43);
  `Fintype ↥(fixedSubring α k)` instance ✓ (Subfield/Basis.lean:305-307);
  `Nontrivial ↥(fixedSubring …)` **not an instance** — must be derived (pattern:
  Field.lean:288-302 `haveI`, or via `card_fixedSubring_eq q α κ h2 hk` q-explicit,
  Cardinality.lean:99).
- `Algebra ↥(fixedSubring α k) (Rq …)`: **free from Mathlib** (`Algebra.ofSubring`,
  `algebraMap = S.subtype`; rfl-lemma `algebraMap_ofSubsemiring`). No ArkLib code needed.
- Unit/cancellation: only **inline** today —
  `IsUnit ((2^α / 2^κ : ℕ) : Rq …)` via `Nat.pow_div hκ (by norm_num), Nat.cast_pow, Nat.cast_ofNat`
  + `(isUnit_two (powTwoCyclotomic α) h2).pow _` (TraceInnerProduct.lean:273-275); cancellation
  pattern `rw [nsmul_eq_mul, nsmul_eq_mul] at heq; hunit.mul_left_cancel heq` (:282-283).
  `isUnit_two` is named (Subfield/Basis.lean:227).
- Index arithmetic: everything is literally `2 ^ α / 2 ^ κ` (Nat division), **never**
  `2 ^ (α − κ)`; `Nat.pow_div : n ≤ m → 0 < x → x^m / x^n = x^(m-n)` (Lean core; exponent
  inequality FIRST). `succ_le_of_two_mul_two_pow_dvd (hk : 2 * 2^κ ∣ 2^α) : κ + 1 ≤ α`
  (Galois/Order.lean:113) supplies `κ ≤ α`.
- ZMod-q section style: `variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)]
  [LawfulBEq (ZMod q)]` with `q` explicit.
- Split machinery (ArkLib/Commitments/Functional/Hachi/PolynomialEvalSplit.lean, namespace
  `ArkLib.Lattices.Hachi`, `[CommSemiring R]`): `splitEquiv nl nh : Fin (2^nh) × Fin (2^nl) ≃
  Fin (2^(nl+nh))` with `(splitEquiv nl nh (x,y)).val = y.val + 2^nl * x.val` (low bits = second
  component = first `nl` variables); `eval_eq_sum (p) (v) : eval p v = ∑ i, p.get i *
  (monomialBasis v).get i` (:126); `monomialBasis_get` (:131);
  `toMatrix : CMlPolynomial R (nl+nh) → PolyMatrix R (2^nl) (2^nh)` (:141) /
  `toPolynomial : PolyMatrix R (2^nl) (2^nh) → CMlPolynomial R (nl+nh)` (:190) + round-trips
  (:202/:209); `splitForm_monomialBasis_eq_eval (M) (xl) (xh) : splitForm M (monomialBasis
  xl).get (monomialBasis xh).get = CMlPolynomial.eval (toPolynomial M) (xl ++ xh)` (:221-224);
  `evalSplit_eq_eval` (:163); `monomialBasis_split` (:145). **Name trap**:
  `Hachi.toPolynomial` (matrix reshape) ≠ CompPoly's `CMlPolynomial.toMvPolynomial` (which has
  NO eval-agreement lemma — do not plan around it).
- Sorries OFF this plan's path: `no_selfReciprocal_factor` (Field.lean:211),
  `cInfNorm_psi_le` (NormBound.lean:103). Nothing here depends on either.

### 1.5 Mathlib (rev v4.30.0) — exact names

`Module.Basis.ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R)` + `Basis.ofEquivFun_repr_apply`
(`(Basis.ofEquivFun e).repr x i = e x i`, rfl) + `Basis.equivFun_ofEquivFun`;
`Module.Basis.singleton ι R [Unique ι]` + `singleton_repr`; `Basis.equivFun_symm_apply`;
`Finsupp.mapRange(_apply/support_mapRange)`; `MvPolynomial.eval_eq'`;
`mem_restrictDegree_iff_degreeOf_le` (**ArkLib-local**, ArkLib/Data/MvPolynomial/Degrees.lean:183);
`Fin.append` + `append_left/right`; `finSumFinEquiv`; `finCongr`; `Algebra.smul_def`,
`algebraMap_smul`, `_root_.smul_eq_mul` (the `Algebra.id.` variant is deprecated);
`Nat.pow_div {x m n} (h : n ≤ m) (hx : 0 < x)` (Lean core). Basis namespace is `Module.Basis` —
write it qualified, per ArkLib convention.

---

## 2. Design decisions (each with its reason)

- **G1 — Two representations, one seam.** Generic layer additions are stated in the branch's
  idiom (`RingSwitchCarrier` + `MultilinearPoly`); the Hachi head's soundness algebra is stated
  natively on `CMlPolynomial` using `PolynomialEvalSplit`. They are tied by the `hachiCarrier`
  instance (Phase 7) and a documented correspondence, NOT by a proof-level bridge. *Reason:*
  CompPoly's `toMvPolynomial` has no eval lemma; the truly generic kernel of the head's soundness
  is two lines of `Basis.repr` linear algebra, so a representation bridge buys nothing and risks
  much.
- **G2 — The check is basis-coordinate-form; the trace form is an instance equivalence.** The
  verifier's check is `y = ∑ v, w v * psiInv Y v` (all in `B := ↥(fixedSubring …)`); the paper's
  `Tr_H(Y · σ₋₁(ψ(monomials))) = (2^α/2^κ)·y` is proven **equivalent** via `traceH_psi_mul_conj`
  (Phase 3). *Reason:* coordinates via `Basis.repr`/`psiInv` are canonical — this kills the old
  plan's R2 (rows-vs-columns) and D5 (σ₋₁ message twist) wholesale: the wire message is the
  untwisted `Y`, and no `φ₀/φ₁` data is needed anywhere.
- **G3 — Guarded verifier, `failure` on check-failure.** `verify := fun s tr => if check … then
  pure (toPolyEvalStatement s Y) else failure`. *Reason:* the check consumes `s.xt, s.y`, which
  `PolyEvalStatement` drops; a pure pass-through head would be unsound (nothing downstream can
  re-impose the check), and the dummy-state convention loses the constraint in CWSS extraction.
- **G4 — The head outputs `PolyEvalStatement` directly** (no separate σ₋₁/coercion adapter
  reduction). *Reason:* G2 killed the twist, so the only statement work is coercion
  `Vector B → Vector (Rq Φ)` and `y := Y` — folding it into the head's pure-branch avoids a
  zero-round `ReduceClaim` factor and keeps the `▷` seam count minimal.
- **G5 — Batching stays untouched; Hachi is NOT a degenerate `BatchingStrategy`.** *Reason:* a
  `Challenge := Unit, error := 0` instance would model an identity fold of claims, not a trace
  check — the check predicate appears nowhere in `BatchingStrategy`'s vocabulary. The honest
  reading: `BatchingStrategy` is the *relocation* phase's design axis (DP24-only); the packing
  stage's axis is the weight family (Phase 1).
- **G6 — Laws as hypotheses, no new sorries in structures** (inherited from the old plan's D1
  and the branch's own "hypotheses live on theorems" discipline). Structures carry data; `Prop`s
  are standalone and taken as theorem hypotheses.
- **G7 — Index conventions pinned once, in code, with `decide` examples.** All packing indices
  are `Fin (2^α / 2^κ)`; the single named equiv `packIndexEquiv` (Phase 2) converts to
  `Fin (2^(α−κ))` where `CMlPolynomial` arity arithmetic needs it. *Reason:* the two forms are
  NOT defeq; every mid-proof cast is a bug factory (old plan R4).
- **G8 — Scope guard.** Honest-prover/completeness stays at skeleton level (QuadEval precedent);
  knowledge-error accounting, Fiat–Shamir, and the branch's S6/S7 obligations are out of scope.
  *Reason:* matches the chain's current discipline (TODO block) and keeps this plan mergeable.
- **G9 — The guard check is Bool-valued, defined once.** Phase 4 defines
  `def headCheck … : Bool := decide (s.y = ∑ …)` (via `DecidableEq B`); the verifier is the Bool
  `if headCheck … then pure … else failure`; `Verifier.IsGuarded` (Phase 5) stores a
  `… → Bool` check so `verify_eq` matches *syntactically*; `relRingSwitch`-side proofs cross via
  `decide_eq_true_eq`. CheckClaim's `[DecidablePred pred]` + `do guard …` convention is **not**
  copied — only its guard/`failure` mechanics are precedent. *Reason:* three candidate
  conventions exist in-tree; Bool is the only one that lets `IsGuarded.verify_eq` match without
  instance-plumbing at the composition site. Decided now so Phases 4 and 5 cannot diverge.

### 2.5 Delivery discipline

- **Scratch files stay untracked.** Phase 0.1 commits only tracked changes plus explicitly
  `git add`-ed new `.lean`/docs files (`git add -u` + named adds — never `git add .` at the
  root). The four root-level `HACHI_*.md` planning notes remain untracked (CLAUDE.md: stable
  guidance belongs in `docs/wiki/`, not ephemeral notes).
- **PR partition:** PR-A = Phases 0–1 (Generic/ additions + docs retarget; request review from
  the branch author, per R8). PR-B = Phase 5 (framework-only; maintainer review, per R3). PR-C =
  Phases 2–4 + 6–7 (the Hachi head; depends on A and B).
- **Cadence:** `./scripts/validate.sh` green at every phase boundary; `--lint` before each PR;
  new files `git add`-ed before validation (generated `ArkLib.lean`).

---

## 3. Phase 0 — Branch setup (0.5 d)

*Why necessary:* the Generic/ files exist only on `origin/feat/generic-ring-switch`; the CWSS
infra (incl. `Package.lean`, staged-only) exists only on the current branch's working tree. No
single existing ref contains both.

Steps (exact):

1. Commit all current working-tree changes on `hachi-polynomial-quadratic-eq` (or have the user
   do so / stash-confirm). **Do not proceed on a dirty tree** — the merge dry-run only covered
   committed state.
2. `git checkout -b hachi-generic-ring-switch` (from the committed tip).
3. `git merge origin/feat/generic-ring-switch`. Expected: clean auto-merge; the only both-sides
   files are `ArkLib.lean`, `blueprint/src/references.bib`, `docs/wiki/repo-map.md`. If
   `ArkLib.lean` conflicts anyway: take either side, then `git add` all new `.lean` files and run
   `./scripts/update-lib.sh` (it regenerates `ArkLib.lean` from `git ls-files`; it **hard-fails
   on untracked** `ArkLib/**/*.lean` — always `git add` first). Never hand-edit `ArkLib.lean`.
4. `lake exe cache get` if needed, then `./scripts/validate.sh` — must be green before any new
   work. Note the merge brings a breaking 4-arg `prob_schwartz_zippel_mv_polynomial` (no HEAD
   callers — nothing to fix) and the Binius `witnessNovelCoeffs` semantic fix (HEAD does not
   touch BinaryBasefold — nothing to fix).

Acceptance: `./scripts/validate.sh` green on the merged branch;
`git grep -l RingSwitchCarrier -- 'ArkLib/ProofSystem/RingSwitching/Generic'` returns the five
Generic files (repo-wide the grep hits 8 paths — the five plus `Data/MvPolynomial/Multilinear.lean`
and two docs files; that is expected, not a bad merge).

---

## 4. Phase 1 — Generic layer: the deterministic exit stage + docs retarget (1.5 d)

### 4.1 New file `ArkLib/ProofSystem/RingSwitching/Generic/PackedClaim.lean`

Imports: `ArkLib.ProofSystem.RingSwitching.Generic.Packing`. Namespace
`RingSwitching.Generic.RingSwitchCarrier`, `variable {B : Type} [CommRing B]
(car : RingSwitchCarrier B)`, inside `noncomputable section`, `open Module MvPolynomial
Sumcheck.Structured` (mirror Packing.lean's header exactly).

Content (names indicative; keep docstring style of the sibling files):

```lean
/-- The deterministic packed-claim check (design "step 2", packing-phase exit): the original
claim value `y : B` is the `w`-weighted recombination of the packed carrier value's
`packBasis`-coordinates. Hachi §3.1: `w` = tail monomials, `Y` = the one prover message;
DP24 continues past this stage into batching + sumcheck instead. -/
def recombineCheck (w : car.ιP → B) (Y : car.P) (y : B) : Prop :=
  y = ∑ v, w v * car.packBasis.repr Y v

/-- The residual native claim after a packing head: the packed polynomial evaluates to `Y`
at the (base-embedded) head point. This is the deterministic exit's output anchor — for a
carrier with `P` = the committed ring, it is already a native PCS claim. -/
def packedClaimRel (m : ℕ) :
    Set (((Fin m → B) × car.P) × MultilinearPoly car.P m) :=
  { x | x.1.2 = x.2.val.eval (fun i => algebraMap B car.P (x.1.1 i)) }

/-- Coordinates of an honest packed evaluation are the family's evaluations —
`packedMLE_eval` pushed through `repr`. NB: `packBasis.repr` lands in `B`, so the RHS is the
bare `(Ps v).val.eval pt` — the `algebraMap` in `packedMLE_eval`'s reassembly is absorbed by
`repr`. -/
theorem repr_packedMLE_eval {m : ℕ} (Ps : car.ιP → MultilinearPoly B m)
    (pt : Fin m → B) (v : car.ιP) :
    car.packBasis.repr
      (MvPolynomial.eval (fun i => algebraMap B car.P (pt i)) (car.packedMLE Ps).val) v
      = (Ps v).val.eval pt
```

Proof plan: rewrite with `car.packedMLE_eval`; convert each summand
`algebraMap B car.P c * car.packBasis i` to `c • car.packBasis i`
(`Algebra.smul_def`, symm — i.e. `simp_rw [← Algebra.smul_def]`); finish with
**`Module.Basis.repr_sum_self`** (Mathlib LinearAlgebra/Basis/Defs.lean:265, `[Fintype ι]`:
`b.repr (∑ i, c i • b i) = c` — verified to exist; do NOT reach for `Basis.repr_equivFun_symm`,
which does not exist) plus a `congrFun` at `v`.

```lean
/-- Generic soundness kernel of the deterministic packing exit: if the check passes against
the honest packed value, the weighted family claim holds. (The Binius/Hachi instances feed
their own weight-law into `w` — hypotheses live on theorems, per the layer's discipline.) -/
theorem recombineCheck_iff_of_packedClaim {m : ℕ} (Ps : car.ιP → MultilinearPoly B m)
    (pt : Fin m → B) (w : car.ιP → B) (y : B) :
    car.recombineCheck w
      (MvPolynomial.eval (fun i => algebraMap B car.P (pt i)) (car.packedMLE Ps).val) y
    ↔ y = ∑ v, w v * (Ps v).val.eval pt := by
  unfold recombineCheck; simp [car.repr_packedMLE_eval]
```

Sanity section (mirror the siblings): exercise `recombineCheck` + `packedClaimRel` on
`decoupledToyCarrier` and `towerCarrier`; one value-level `example` computing
`repr_packedMLE_eval` on the toy carrier.

*Why this change:* this is the missing stage — the branch's relation chain starts at
`openingClaimRel` and immediately eq-decomposes toward batching; Hachi's protocol content at this
layer is exactly (`recombineCheck`, `packedClaimRel`) and nothing else. Stating it generically
(with the weight family `w` as the knob and the check's coordinates fixed to `packBasis.repr`)
also gives Binius the *proven* step-2 identity for free later, replacing the old plan's
4-field `PackingScheme` with 1 knob + 1 proven kernel lemma.

### 4.2 Edit `Generic/Relations.lean` — re-anchor the chain docstring

Extend the module docstring's relation-chain bullet list: `packedClaimRel` (in
`PackedClaim.lean`) is the **shared deterministic segment**; `sliceRel → sumcheckClaimRel` is the
**DP24/relocation route** taken only when the head point is not base-embedded. Do not change any
existing definition. Add one `example` in the sanity section instantiating `packedClaimRel` on
both carriers.

*Why:* prevents the next reader from assuming the batching route is the only route; zero proof
risk.

### 4.3 Docs retarget (same PR)

- Batching.lean module docstring + `BatchingStrategy` docstring + sanity comment (three verified
  sites): replace "the S8 non-domain (Hachi) sibling … supply its own proven `separates`" with:
  Hachi `R_q` is a **non-domain carrier of the packing stage only** — its head is deterministic
  (one message + `recombineCheck`, zero challenges, zero error; see
  `Generic/PackedClaim.lean` and `Commitments/Functional/Hachi/RingSwitch/`), and it does not
  instantiate `BatchingStrategy`. Keep the `CommRing`-only-vocabulary sentence — it remains true
  and load-bearing.
- Relations.lean:312-314 sanity comment: same correction (the `DenseMLPCS (ZMod 6) 3` statability
  example stays; it is about vocabulary, not Hachi).
- `docs/kb/concepts/ring-switching.md` ("The Generic layer" section): add the packing-stage
  paragraph + correct the S8 description.
- `docs/wiki/repo-map.md`: add `Generic/PackedClaim.lean` and (Phase 4's)
  `Hachi/RingSwitch/` entries — CLAUDE.md guardrail: same PR as the code.

*Why:* the branch's written roadmap currently models Hachi as a batching instance — the exact
misread this whole plan exists to prevent from ossifying.

Acceptance (Phase 1): build green; `recombineCheck_iff_of_packedClaim` sorry-free; docstrings
contain no remaining claim that Hachi batches.

---

## 5. Phase 2 — Lattice glue (1.5 d)

New file `ArkLib/Data/Lattices/CyclotomicRing/Subfield/LinearEquiv.lean` (imports
`Subfield/Packing.lean`, `Subfield/Bijectivity.lean`, `Galois/Order.lean`). Naming note: this
phase lives in the lattice layer, whose house parameter name is `κ` (as in `psi_bijective`,
`card_fixedSubring_eq`) — keep it here; Phases 3–6 instantiate it as `κRS` (§11's dictionary),
since only the *chain* files have the `κ`-collision. Work in the ZMod-q section style (`variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)]
[LawfulBEq (ZMod q)]`, q explicit) for the bundled equiv (it needs `psi_bijective`, which is
ZMod-q); the `psi_smul` lemma can stay in the generic `[Field R]` section of Packing.lean.

Deliverables, in order:

1. **`psi_smul`** (append to Subfield/Packing.lean, generic section):
   ```lean
   theorem psi_smul (α k : ℕ) (c : fixedSubring (R := R) α k)
       (a : Fin (2 ^ α / k) → fixedSubring (R := R) α k) :
       psi α k (c • a) = (c : Rq (powTwoCyclotomic α)) * psi α k a
   ```
   Proof: unfold `psi`; `Finset.mul_sum`; per-summand `Subring` coe-of-mul + `mul_assoc`. (Pin
   how `c • a` acts pointwise: `Pi.smul_apply` + subring `smul = mul` on the subtype —
   if the pointwise action is not already `Mul`-defeq, state the lemma with
   `(fun j => c * a j)` instead of `c • a`; either form serves step 2.)
2. **Nontriviality lemmas** (as theorems producing instances, not global instances):
   - `nontrivial_Rq_powTwoCyclotomic : Nontrivial (Rq (powTwoCyclotomic (R := ZMod q) α))` —
     export the inline `haveI` derivation at Subfield/Field.lean:298-302 (via `Rq.equivQuotient`;
     needs only the standing `[Fact (Nat.Prime q)]`, no `h2`/`hk`) as a named lemma. Phase 7's
     carrier needs it for its `ntP` field.
   - `Nontrivial ↥(fixedSubring (R := ZMod q) α (2^κ))` under `(h2) (hk)`: derive from
     `card_fixedSubring_eq q α κ h2 hk` (`Fintype.card … = q ^ 2^κ ≥ 2` since `q` prime ⇒
     `Fintype.one_lt_card_iff_nontrivial`), or from the subring's `0 ≠ 1` directly given the
     ambient nontriviality above (Mathlib's `Subring` Nontrivial instance needs
     `Nontrivial (Rq …)`, which is exactly the first lemma).
3. **`psiLinearEquiv`**:
   ```lean
   noncomputable def psiLinearEquiv (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0)
       (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
       (Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ))
         ≃ₗ[fixedSubring (R := ZMod q) α (2 ^ κ)] Rq (powTwoCyclotomic (R := ZMod q) α) :=
     LinearEquiv.ofBijective
       ({ toFun := psi α (2 ^ κ), map_add' := psi_add α (2 ^ κ), map_smul' := … } : _ →ₗ[_] _)
       (psi_bijective q α κ h2 hk)
   ```
   The `Module ↥(fixedSubring …) (Rq …)` instance is found by TC search via Mathlib's
   `Algebra.ofSubring` (verified); `map_smul'` is `psi_smul` composed with
   `Algebra.smul_def` + `algebraMap_ofSubsemiring` (`algebraMap = Subtype.val`-coe). Definitional
   abbreviation: `noncomputable abbrev psiInv … := (psiLinearEquiv q α κ h2 hk).symm` with simp
   lemmas `psiInv_psi`, `psi_psiInv` (from `LinearEquiv.symm_apply_apply` etc.).
4. **Named unit + cancellation** (append to TraceInnerProduct.lean or the new file):
   ```lean
   theorem isUnit_pow_div_cast (α κ : ℕ) (hκα : κ ≤ α) (h2 : (2 : ZMod q) ≠ 0) :
       IsUnit ((2 ^ α / 2 ^ κ : ℕ) : Rq (powTwoCyclotomic (R := ZMod q) α))
   theorem nsmul_pow_div_cancel (α κ : ℕ) (hκα : κ ≤ α) (h2 : (2 : ZMod q) ≠ 0)
       {x y : Rq (powTwoCyclotomic (R := ZMod q) α)}
       (h : (2 ^ α / 2 ^ κ) • x = (2 ^ α / 2 ^ κ) • y) : x = y
   ```
   Proofs: lift the verified inline pattern (TraceInnerProduct.lean:273-275 and :282-283)
   verbatim into named lemmas. Get `hκα` from `succ_le_of_two_mul_two_pow_dvd hk` (κ+1 ≤ α ⇒
   κ ≤ α) at call sites.
5. **`packIndexEquiv`** (the one sanctioned index cast, G7):
   ```lean
   def packIndexEquiv (α κ : ℕ) (hκα : κ ≤ α) :
       Fin (2 ^ α / 2 ^ κ) ≃ Fin (2 ^ (α - κ)) :=
     finCongr (Nat.pow_div hκα (by norm_num))
   ```
   Plus a `decide` example at `α = 2, κ = 1` pinning the round-trip (old plan A1's acceptance,
   scoped down to what this plan uses).

*Why each:* (1)+(3) — `psiInv` (the check's coordinate map) is `psiLinearEquiv.symm`; without
`psi_smul` the linear map cannot be bundled and `map_sum/map_smul` (Phase 3's whole proof engine)
are unavailable. (2) — `RingSwitchCarrier` requires `Nontrivial` for the Phase 7 instance, and
several Phase 3 rewrites need `0 ≠ 1` in `B`. (4) — Phase 3's `traceCheck_iff` must cancel the
`(2^α/2^κ) •` factor of Theorem 2; today that cancellation exists only inline inside another
proof. (5) — `CMlPolynomial` arities are `2^(vars)` while ψ's index is `2^α/2^κ`; G7 mandates
exactly one named crossing.

Acceptance: all five sorry-free; `example : Fin (2^2/2^1) ≃ Fin (2^1) := packIndexEquiv 2 1
(by omega)` compiles; `decide` example green.

---

## 6. Phase 3 — The unpack algebra: Theorem 2 at the polynomial level (3–4 d, the heart)

New file `ArkLib/Commitments/Functional/Hachi/RingSwitch/Unpack.lean`. Imports:
`Hachi/PolynomialEvalSplit.lean`, `Subfield/LinearEquiv.lean`, `Subfield/TraceInnerProduct.lean`.
Namespace `ArkLib.Lattices.Hachi` (the split layer's namespace), ZMod-q section. **Header opens
(mandatory, or nothing resolves):** `open CompPoly ArkLib.Lattices.CyclotomicModulus` — psi,
traceH, conjAut, fixedSubring, Rq, powTwoCyclotomic all live in
`ArkLib.Lattices.CyclotomicModulus` (mirror `Hachi/Basic.lean:97`'s open line; §12's ban is only
on `open ArkLib.Lattices` *itself*, whose `⬝ᵥ` is ambiguous — opening the leaf namespace is
safe and the chain already does it).

Abbreviations: export a **public** `abbrev PackBase (q α κRS : ℕ) … : Type :=
↥(fixedSubring (R := ZMod q) α (2 ^ κRS))` from this file — Phase 4's statement fields and
Phase 7's `rfl` examples must see through it, so it cannot be `local`. `Φα`, `N := 2^α / 2^κRS`,
`κ' := α - κRS` may stay local, with `hκα : κRS ≤ α` and crossing to `Fin (2^κ')` only via
`packIndexEquiv` — never inline-cast. **Coercion spelling (pin once, use everywhere):** the bare
`(↑·)` lambda does NOT elaborate (compile-verified: it degenerates to `fun x => x` and
type-errors); define `def coeVec {n} (x : Vector (PackBase q α κRS) n) : Vector (Rq Φα) n :=
x.map (fun b => (b : Rq Φα))` and state every lemma through `coeVec`.

One prerequisite edit in `PolynomialEvalSplit.lean`: `eval_eq_sum` is stated at arity
`nl + nh`, and `rw [eval_eq_sum]` does NOT fire at a bare arity `n` (compile-verified
unification failure). Either generalize it to `{n : ℕ}` (the existing proof compiles unchanged —
preferred) or invoke it as `eval_eq_sum (nl := n) (nh := 0)` (defeq `n + 0`); do not rely on
bare `rw [eval_eq_sum]`.

Deliverables, in dependency order (each a lemma; sorry-free before moving on):

1. **Coe/monomial commutation.** `B`'s coe into `Rq Φα` is `SubringClass` coe (a ring hom).
   ```lean
   theorem monomialBasis_map_coe {n : ℕ} (x : Vector (PackBase q α κRS) n) (j : Fin (2 ^ n)) :
       (CMlPolynomial.monomialBasis (coeVec x)).get j
         = ((CMlPolynomial.monomialBasis x).get j : Rq Φα)
   ```
   Proof: `monomialBasis_get` on both sides; the RHS product of `if`-selected entries commutes
   with the coe ring hom (`map_prod`, `apply_ite`). (If `CMlPolynomial.monomialBasis` has its own
   `map` lemma in CompPoly, use it; otherwise `monomialBasis_get` + `Finset.prod_congr` is 10
   lines.)
2. **Eval at coerced points is a `B`-combination of coefficients.**
   ```lean
   theorem eval_coeVec {n : ℕ} (F : CMlPolynomial (Rq Φα) n) (x : Vector (PackBase q α κRS) n) :
       CMlPolynomial.eval F (coeVec x)
         = ∑ j : Fin (2 ^ n), (CMlPolynomial.monomialBasis x).get j • F.get j
   ```
   Proof: `eval_eq_sum` (per the arity note above) + step 1 + `Algebra.smul_def`/
   `algebraMap_ofSubsemiring` to turn `↑c * F.get j` into `c • F.get j`. (Note `eval_eq_sum` is
   stated `p.get i * (monomialBasis v).get i` — commute with `mul_comm` before the smul rewrite.)
3. **Coordinate/eval commutation** (`psiInv` is `B`-linear — the generic kernel, instance-side):
   ```lean
   theorem psiInv_eval_coeVec {n : ℕ} (h2) (hk) (F : CMlPolynomial (Rq Φα) n)
       (x : Vector (PackBase q α κRS) n) (v : Fin N) :
       psiInv q α κRS h2 hk (CMlPolynomial.eval F (coeVec x)) v
         = ∑ j : Fin (2 ^ n), (CMlPolynomial.monomialBasis x).get j
             * psiInv q α κRS h2 hk (F.get j) v
   ```
   Proof: step 2, then `map_sum` + `map_smul` of the linear equiv, then `Pi.smul_apply` +
   `smul_eq_mul` in `B`.
4. **`unpackPoly`** — coefficient-wise ψ⁻¹, tail variables LAST. The compile-verified form
   (row index = head `j` FIRST, column = tail `v` second — `toPolynomial` with target
   `CMlPolynomial B (n + κ')` forces `PolyMatrix B (2^n) (2^κ')`):
   ```lean
   noncomputable def unpackPoly {n : ℕ} (h2) (hk) (F : CMlPolynomial (Rq Φα) n) :
       CMlPolynomial (PackBase q α κRS) (n + κ') :=
     Hachi.toPolynomial (fun (j : Fin (2 ^ n)) (v : Fin (2 ^ κ')) =>
       psiInv q α κRS h2 hk (F.get j) ((packIndexEquiv α κRS hκα).symm v))
   ```
   (This lambda was type-checked by a verification agent against
   `CMlPolynomial ↥(fixedSubring α (2^κ)) (n + (α - κ))`. If your `PolyMatrix` literal needs a
   different constructor than a bare function, read its definition in PolynomialEvalSplit.lean
   and keep the SAME index order: `(j, v)`, head first.) The orientation acceptance test is
   step 5 — if anything is transposed, fix it HERE, never by casting in step 5's proof (G7).
5. **The unpack-eval identity** (the C3 heart, replacing the old plan's
   `traceH_packPoly_eval` at the same difficulty):
   ```lean
   theorem unpackPoly_eval {n : ℕ} (h2) (hk) (F : CMlPolynomial (Rq Φα) n)
       (x : Vector (PackBase q α κRS) n) (xt : Vector (PackBase q α κRS) κ') :
       CMlPolynomial.eval (unpackPoly h2 hk F) (x ++ xt)
         = ∑ v : Fin (2 ^ κ'), (CMlPolynomial.monomialBasis xt).get v
             * psiInv q α κRS h2 hk (CMlPolynomial.eval F (coeVec x))
                 ((packIndexEquiv α κRS hκα).symm v)
   ```
   Proof plan: LHS via `splitForm_monomialBasis_eq_eval` (with `toPolynomial_toMatrix`/the
   round-trip to expose the matrix) = the double sum
   `∑ v ∑ j (monomialBasis xt).get v * (monomialBasis x).get j * M j v` (note `M j v`, head
   index first); RHS via step 3 expands to the same double sum; finish with `Finset.sum_comm` +
   ring. All in `B` ([CommSemiring] suffices for the split machinery — verified).
6. **Head-soundness corollary** (what Phase 4's pull-back calls):
   ```lean
   theorem unpackPoly_eval_of_check {n : ℕ} (h2) (hk)
       {F : CMlPolynomial (Rq Φα) n} {x : Vector (PackBase q α κRS) n}
       {xt : Vector (PackBase q α κRS) κ'} {Y : Rq Φα} {y : PackBase q α κRS}
       (hY : CMlPolynomial.eval F (coeVec x) = Y)
       (hchk : y = ∑ v, (CMlPolynomial.monomialBasis xt).get v
                    * psiInv q α κRS h2 hk Y ((packIndexEquiv α κRS hκα).symm v)) :
       CMlPolynomial.eval (unpackPoly h2 hk F) (x ++ xt) = y := by
     subst hY; rw [unpackPoly_eval, hchk]
   ```
7. **Trace-form equivalence** (paper faithfulness; Theorem 2 discharges):
   ```lean
   /-- Hachi's paper check (§3.1 / Theorem 2 form). Message is the UNTWISTED `Y` —
   the σ₋₁ lives inside the trace identity, not on the wire (design G2). -/
   def traceCheck (h2) (hk) (xt : Vector (PackBase q α κRS) κ') (Y : Rq Φα)
       (y : PackBase q α κRS) : Prop :=
     traceH α (2 ^ κRS) (Y * conjAut α (psi α (2 ^ κRS)
         (fun j => (CMlPolynomial.monomialBasis xt).get (packIndexEquiv α κRS hκα j))))
       = (2 ^ α / 2 ^ κRS) • (y : Rq Φα)

   theorem traceCheck_iff_recombine (h2) (hk) (xt) (Y) (y) :
       traceCheck h2 hk xt Y y
         ↔ y = ∑ v, (CMlPolynomial.monomialBasis xt).get v
                 * psiInv q α κRS h2 hk Y ((packIndexEquiv α κRS hκα).symm v)
   ```
   (Type note: `j : Fin (2^α/2^κRS)`, so `packIndexEquiv … j : Fin (2^(α−κRS))`, and with
   `κ'` an abbrev for `α − κRS` this is literally `Fin (2^κ')` — `monomialBasis xt |>.get`
   accepts it with no cast; this is exactly why κ' must be an abbrev, G7.)
   Proof plan: write `Y = psi α (2^κRS) (psiInv … Y)` (`psi_psiInv`); apply
   `traceH_psi_mul_conj α (2^κRS) h2 ⟨κRS, rfl⟩ hk`; the RHS becomes
   `(2^α/2^κRS) • ↑(∑ i, psiInv Y i * weights i)`; reindex the sum along `packIndexEquiv`
   (`Equiv.sum_comp` / `Fintype.sum_equiv`) and commute the factors; conclude by
   `nsmul_pow_div_cancel` (Phase 2.4) + `Subtype.val`-injectivity
   (`Subtype.coe_injective` on the subring; both sides are coerced subring elements — the LHS via
   `traceH_mem_fixed` + `mem_fixedSubring_iff` if needed, but the cleaner route is to cancel
   first and compare inside `Rq`, then pull back along injectivity of the coe).

*Why this phase:* steps 4–6 are the entire mathematical content of the head's soundness — the
paper's Theorem 2 lifted to "the unpacked polynomial's evaluation is check-determined". Step 7 is
what makes the formalization *the paper's protocol* (the wire check is provably the trace
equation) rather than a lookalike; it is also where the σ₋₁ twist is discharged once and for all.

Acceptance (hard): steps 1–7 sorry-free and `./scripts/validate.sh` green. Note `unpackPoly` is
necessarily noncomputable (`psiInv` comes from `LinearEquiv.ofBijective`; `fixedSubring` itself
is noncomputable), so a `decide`/`native_decide` evaluation of `unpackPoly_eval` is
**infeasible, not merely impractical** — do not attempt it. Optional (30-min timebox): a
`decide` example on the computable ingredients only (`packIndexEquiv` round-trip,
`monomialBasis` values at `α = 2, κRS = 1`); if it doesn't land in the timebox, drop it — the
hard acceptance stands alone.

---

## 7. Phase 4 — The head reduction + its CWSS theorem (2–3 d)

New file `ArkLib/Commitments/Functional/Hachi/RingSwitch/Head.lean`. Imports: `Unpack.lean`,
`PolynomialQuadraticEq/PolyEvalReduction.lean`, CWSS `NoChallenge`/`Package`. Namespace
`ArkLib.Lattices.Ajtai.InnerOuter` (the chain's namespace; `open WeakBinding`, plus
`open CompPoly ArkLib.Lattices.CyclotomicModulus` as in Phase 3; do NOT
`open ArkLib.Lattices` itself). Section variables: copy Basic.lean:103-106 verbatim, **plus
`{κRS : ℕ}`** (it is NOT in Basic.lean's list; with `autoImplicit = false` forgetting to declare
it is a hard error) and `(hκα : κRS ≤ α) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κRS ∣ 2 ^ α)` —
**the ring-switch parameter is named `κRS` throughout**: the chain already uses `κ` for the
challenge-set parameter (`relPolyEval … γ κ`, instantiated at `κ := 2 * ω`). This collision is
the old plan's R5; pin the dictionary in the file header.

Deliverables:

1. **Statement — pinned to the chain modulus `𝓜(q,α)`, NOT Φ-generic**:
   ```lean
   structure RingSwitchStatement (innerRows messageDigits outerRows innerDigits dRows m r : Nat) where
     pp : Hachi.PublicParamsD 𝓜(q,α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
     u  : Commitment 𝓜(q,α) outerRows
     xl : Vector (PackBase q α κRS) r
     xh : Vector (PackBase q α κRS) m
     xt : Vector (PackBase q α κRS) κ'     -- κ' := α - κRS, the packed tail
     y  : PackBase q α κRS
   ```
   `q α κRS` enter as auto-bound section-variable parameters. Do NOT add a
   `(Φ : CyclotomicModulus (ZMod q))` parameter: `PackBase` lives inside
   `Rq (powTwoCyclotomic α)`, and nothing would tie a generic `Φ` to `α` — step 2 would then
   fail to typecheck. The pin is sound because `𝓜(q,α)` is `@[reducible] hachiModulus q α :=
   primePowTwoModulus q α` (InnerOuter/Arithmetic.lean:58) `:= powTwoCyclotomic α`
   (CyclotomicRing/PowTwo.lean:58) — so `Rq 𝓜(q,α)` unfolds to `PackBase`'s ambient ring and
   the coercions land without casts. (Statement stores the split point, matching
   `PolyEvalStatement`'s discipline — verified docstring: split storage avoids take/drop casts.)
2. **Output map** (fused adapter, G4):
   ```lean
   def toPolyEvalStatement (s : RingSwitchStatement …) (Y : Rq 𝓜(q,α)) :
       PolyEvalStatement 𝓜(q,α) innerRows messageDigits outerRows innerDigits dRows m r :=
     { pp := s.pp, u := s.u, xl := coeVec s.xl, xh := coeVec s.xh, y := Y }
   ```
   (`coeVec` from Phase 3 — the bare `(↑·)` lambda does not elaborate.)
3. **pSpec, instances, check, verifier** (guarded, G3/G9). First bullet, all mandatory:
   ```lean
   @[reducible, simp]
   def pSpecHead : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Rq 𝓜(q,α)]⟩

   instance : IsEmpty (pSpecHead …).ChallengeIdx := ⟨fun ⟨0, h⟩ => nomatch h⟩
   -- and, if not found via reducibility from ProtocolSpec/Basic.lean:295/:304:
   instance : ∀ i, SampleableType ((pSpecHead …).Challenge i) := fun i => isEmptyElim i
   ```
   `@[reducible]` mirrors `SendClaim.pSpec` (SendClaim.lean:57) and is what lets the generic
   1-message instances (`IsEmpty ChallengeIdx`, `∀ i, SampleableType (Challenge …)` —
   OracleReduction/ProtocolSpec/Basic.lean:295/:304) fire; a plain `def` stalls Phase 6's
   package append on opaque instance-synthesis failures (`CWSSPackage.append` requires
   `[∀ i, SampleableType (pSpec₁.Challenge i)]`, Package.lean:83). Then the Bool check (G9):
   ```lean
   noncomputable def headCheck (s : RingSwitchStatement …) (Y : Rq 𝓜(q,α)) : Bool :=
     decide (s.y = ∑ v, (CMlPolynomial.monomialBasis s.xt).get v
                * psiInv q α κRS h2 hk Y ((packIndexEquiv α κRS hκα).symm v))

   noncomputable def headVerifier … :
       Verifier oSpec (RingSwitchStatement …) (PolyEvalStatement …) (pSpecHead …) where
     verify := fun s tr =>
       if headCheck s (tr 0) then pure (toPolyEvalStatement s (tr 0)) else failure
   ```
   Notes: message access is plain `tr 0` (the SendWitness/SendClaim idiom — SendWitness.lean:73,
   SendClaim.lean:107), not `tr.messages ⟨0, rfl⟩`. The `decide` needs
   `DecidableEq (PackBase q α κRS)` — via `Subtype.instDecidableEq` from
   `DecidableEq (Rq 𝓜(q,α))` (the chain's `[BEq]/[LawfulBEq]` context; check how QuadEval-side
   files obtain `DecidableEq (Rq Φ)` and copy the route; if none exists, add the instance next
   to `Rq`'s `commRing`). Bridge lemma for proofs: `headCheck s Y = true ↔ s.y = ∑ …` by
   `decide_eq_true_eq`.
4. **Input relation** (mirror `relPolyEval`'s three-case shape exactly):
   ```lean
   def relRingSwitch (base : ZMod q) (βSq γ κchal : ℕ) :
       Set (RingSwitchStatement … × QuadEvalWitness 𝓜(q,α) innerRows (2^m) messageDigits (2^r) innerDigits) :=
     { p | match p with
       | (s, .opening o) =>
           VerifiedOpening 𝓜(q,α) base βSq γ κchal s.pp.toPublicParams s.u o ∧
           CMlPolynomial.eval (unpackPoly h2 hk (extractedPoly 𝓜(q,α) base o))
             ((s.xl ++ s.xh) ++ s.xt) = s.y
       | (s, .msisB z) => ModuleSIS.relation 𝓜(q,α) (outerShort 𝓜(q,α) γ) s.pp.outerMatrix z = true
       | (s, .msisD z) => ModuleSIS.relation 𝓜(q,α) (dShort 𝓜(q,α) γ) s.pp.dMatrix z = true }
   ```
   Arity check: `extractedPoly … : CMlPolynomial (Rq 𝓜(q,α)) (r + m)`; `unpackPoly` gives
   `CMlPolynomial (PackBase q α κRS) ((r + m) + κ')`; the point
   `(s.xl ++ s.xh) ++ s.xt : Vector (PackBase q α κRS) ((r+m)+κ')`. ✓
5. **Pull-back lemma** (the CWSS engine):
   ```lean
   theorem mem_relRingSwitch_of_relPolyEval (s) (Y) (w)
       (hchk : headCheck s Y = true)
       (h : (toPolyEvalStatement s Y, w) ∈ relPolyEval 𝓜(q,α) base βSq γ κchal) :
       (s, w) ∈ relRingSwitch base βSq γ κchal
   ```
   Opening case: `relPolyEval` gives `CMlPolynomial.eval (extractedPoly …)
   (coeVec s.xl ++ coeVec s.xh) = Y`; rewrite `coeVec xl ++ coeVec xh = coeVec (xl ++ xh)`
   (a `Vector.map`/append commutation — verify the exact lemma name for the Vector type used by
   `CMlPolynomial.eval`; if missing, prove it locally, 3 lines by `ext`/`get` — this is the only
   Vector plumbing in the plan); cross `hchk` into the Prop form via `decide_eq_true_eq` (G9);
   apply `unpackPoly_eval_of_check` (Phase 3.6). msisB/msisD: statement field `pp` passes
   through unchanged — immediate.
6. **Head CWSS theorem.** The head is a 1-message reduction: `IsEmpty ChallengeIdx` holds for
   `pSpecHead` (step 3's instance). Verified proof route (the verification pass read
   `treeSpecialSound`, TranscriptTree/Basic.lean:308-323, and both templates end-to-end):
   ```lean
   theorem head_coordinateWiseSpecialSound (init impl)
       (D : CWSSStructure (pSpecHead …)) … :
       (headVerifier …).coordinateWiseSpecialSound init impl D
         (relRingSwitch base βSq γ κchal)
         (relPolyEval 𝓜(q,α) base βSq γ κchal)
   ```
   — `D` **universally quantified** (both templates do this; the no-challenge bridge holds for
   any `D`; a `(D := …)` default-value pseudo-binder is not valid syntax). Instantiate
   `D := CWSSStructure.ofIsEmpty` only at the package (Phase 6). Proof skeleton, mirroring
   `SendWitness.verifier_coordinateWiseSpecialSound` (SendWitness.lean:109) +
   `ReduceClaim.verifier_coordinateWiseSpecialSound` (ReduceClaim.lean:186):
   - Enter via `Verifier.coordinateWiseSpecialSound_of_isEmpty_challengeIdx` (its premise
     imposes **no purity** on the verifier — verified — so the guard needs no Phase-5 machinery
     here). The extractor `e : StmtIn → FullTranscript → WitIn` cannot see the output witness
     (the transcript tree carries **no** `WitOut` at leaves — leaves are bare); recover it by
     classical choice à la ReduceClaim's `hpick`: from acceptance,
     `toPolyEvalStatement s (tr 0) ∈ relPolyEval.language`, and `Set.mem_language_iff` gives
     `∃ w, … ∈ relPolyEval`; choose it (`Exists.choose`), here per `(s, tr)` since the chosen
     witness depends on the message `tr 0`.
   - (a) Acceptance forces the check: case on `headCheck s (tr 0)`. In the `false` branch
     `verify = failure` and the run's acceptance probability is 0 ≠ 1 — add the missing helper
     `not_accepting_of_failure` next to `pure_accepting_of_mem` (verified absent; the executable
     spec for the probability argument is `CheckClaim.knowledgeStateFunction.toFun_full`'s
     guard-false branch, via `probEvent_pos_iff`/support-of-`OptionT.mk (pure none)`).
   - (b) In the `true` branch the run is `pure (toPolyEvalStatement s (tr 0))`: apply
     `Verifier.mem_of_pure_accepting` (SeqCompose.lean:53) with `hV := if_pos hchk` (in place of
     the templates' `rfl`), unpack via `Set.mem_language_iff`, and close with step 5.
   - `[Nonempty WitIn]`: `instance : Nonempty (QuadEvalWitness …)` exists at QuadEval.lean:114
     (verified) — same instance the bridge uses.
7. **Prover skeleton.** Honest prover sends
   `Y := CMlPolynomial.eval (extractedPoly …) (coeVec (s.xl ++ s.xh))`-style packed value.
   Type (cf. `QuadEval.prover`, QuadEval.lean:323):
   `Prover oSpec (RingSwitchStatement …) (QuadEvalWitness 𝓜(q,α) …)
   (PolyEvalStatement 𝓜(q,α) …) (QuadEvalWitness 𝓜(q,α) …) (pSpecHead …)` — skeleton only
   (G8). The head *package* (`GuardedCWSSPackage` value) is **deferred to Phase 6**, which is
   where its structure type exists (Phase 5) and where the seam is checked.
8. **Completeness-side lemma (statement only, G8):** `traceCheck_of_honest` — the honest `Y`
   passes the check; provable from `psiInv_eval_coeVec` + the recombination identity; leave
   proven if ≤ 1 day, else `sorry`-free *statement* deferred to the completeness TODO (do NOT
   add a sorry — omit the lemma if unproven).

*Why this phase:* this is the reduction itself. The guard (G3) is forced by information flow
(`xt, y` dropped downstream); the direct-to-`PolyEvalStatement` output (G4) is what makes the
`▷` seam close by `rfl`; the pull-back (step 5) is where Phase 3's algebra meets the chain's
relation shapes.

Acceptance: `head_coordinateWiseSpecialSound` sorry-free; file compiles inside the chain's
namespace; `head_coordinateWiseSpecialSound`'s `relOut` argument is written **verbatim** as the
§1.3 seam expression (`relPolyEval 𝓜(q,α) (b : ZMod q) (quadEvalBetaSq γ b zDigits
((𝓜(q,α)).φ.natDegree) m messageDigits) γ (2 * ω)` at the chain instantiation) and elaborates
without coercion. (The package-level `rfl`-seam example belongs to Phase 6 — the
`GuardedCWSSPackage` type does not exist until Phase 5.)

---

## 8. Phase 5 — Guarded CWSS composition (2–3 d, framework; independent of Phases 1–4)

Extend `CoordinateWiseSpecialSoundness/Composition.lean` + `Package.lean` (+ one helper in
`TranscriptTree/Basic.lean`). **Coordinate with maintainers before landing** (shared security
infrastructure — old plan R3; the Basic.lean TODO already sanctions the need).

**Known tension to raise in that coordination:** CheckClaim.lean:26 and :185-189 record an
unfinished "no-failure `OracleComp`" refactor under which guard-based verifiers are "retained as
a rightmost-only factor" (the sanctioned workaround being: keep the verifier pure and move the
check into the output relation, as `CheckClaim.oracleRelOut` does). That workaround is **not
available** for the Hachi head: its check reads `s.xt, s.y`, which the output statement type
drops (G3), so the check cannot live in `relOut`. Basic.lean's TODO ("Guarded subprotocols need
a guarded variant of `▷`") is the sanctioned path; flag the refactor interaction explicitly.

1. **`Verifier.IsGuarded`** (new, next to the pure machinery). Mirror `Verifier.IsPure`'s exact
   style — it is a **class with an existential field** (OracleReduction/Basic.lean:748:
   `is_pure : ∃ verify, ∀ …, V.verify … = pure …`), and `CWSSPackage.append` destructures it via
   `obtain ⟨verify₁, hV₁⟩ := L₁.isPure.is_pure` (Package.lean:92); the guarded twin must
   destructure the same way:
   ```lean
   /-- A verifier that either purely transforms the statement or rejects outright.
   Pure verifiers are the `check := fun _ _ => true` case. -/
   class Verifier.IsGuarded (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop where
     is_guarded : ∃ (check : StmtIn → pSpec.FullTranscript → Bool)
         (out : StmtIn → pSpec.FullTranscript → StmtOut),
       ∀ s tr, V.verify s tr = if check s tr then pure (out s tr) else failure
   ```
   (Bool check per G9 — matches Phase 4's `headVerifier` syntactically.)
2. **Guarded run lemmas** (generalizing the verified anchors):
   - `append_run_guarded_left` (from `append_run_pure_left`, Composition.lean:311): under the
     guarded hypothesis, if `check s tr₁ = true` then
     `(V₁.append V₂).run s (tr₁ ++ₜ tr₂) = V₂.run (out s tr₁) tr₂`; if `check s tr₁ = false`
     then the composed run is `failure` (`failure >>= _ = failure` on `OptionT`).
   - `not_accepting_of_failure` : if `V.verify s tr = failure` then
     `Pr[(· ∈ lang) | …V.run…] = 0` — **verified missing**; add next to
     `pure_accepting_of_mem` (:325-332). Executable spec for the probability argument:
     `CheckClaim.knowledgeStateFunction.toFun_full`'s guard-false branch
     (`probEvent_pos_iff` + support of `OptionT.mk (pure none)` contains no `some`).
   - **`ChallengeTree.transcripts_ne_nil`** (new, `TranscriptTree/Basic.lean`, next to
     `transcripts` at :178-183): `(∀ i, 0 < arity i) → ∀ {m} (T : ChallengeTree pSpec arity m)
     pre, T.transcripts pre ≠ []` — structural induction, ~10 lines. *Why:* the guarded false
     branch must exhibit SOME composed transcript to contradict acceptance; a suffix tree with a
     zero-arity node lists no transcripts, making the shape-generic guarded theorem otherwise
     unprovable (verified gap — no nonemptiness lemma exists anywhere in TranscriptTree/).
3. **`Verifier.append_treeSpecialSound_of_guardedLeft`** — restate
   `append_treeSpecialSound` (Composition.lean:366-375) with the guarded hypothesis replacing
   the pure one, **plus the extra hypothesis `hS₂ : ∀ i, 0 < S₂.arity i`** (required for the
   false branch, per the `transcripts_ne_nil` note above; the pure theorem needs no such
   hypothesis, which is why this was invisible until now). Proof deltas: at the two `hV₁`
   consumption sites (~:396, ~:407) case on `check s tr₁`: the `false` branch picks a suffix
   transcript via `transcripts_ne_nil` + `hS₂` and contradicts composed acceptance
   probability 1 via `not_accepting_of_failure` lifted along `append_run_guarded_left`; the
   `true` branch reduces verbatim to the existing pure argument with `verify₁ := out`.
   Corollary `append_coordinateWiseSpecialSound_of_guardedLeft` (mirror :414-428): discharge
   `hS₂` from `D₂.arity_eq` — `arity i = ℓᵢ(kᵢ−1)+1 ≥ 1` by `coordIndex.2`/`soundnessParam.2`
   (CWSSStructure fields carry `0 < ell` and `2 ≤ k`), so at the CWSS level the hypothesis is
   free.
   **3b. `Verifier.IsGuarded.append_isPureRight`** — `(hg : V₁.IsGuarded) (hp : V₂.IsPure) :
   (V₁.append V₂).IsGuarded`, with `check := fun s tr => check₁ s tr.fst`,
   `out := fun s tr => f₂ (out₁ s tr.fst) tr.snd` where `⟨f₂, hf₂⟩ := hp.is_pure`. Mirror
   `Verifier.IsPure.append` (Composition/Sequential/IsPure.lean:37-43 — it supplies exactly the
   `tr.fst`/`tr.snd` transcript split); `verify_eq` by `simp [Verifier.append, …]` + case-split
   on the check. *Why:* Phase 6's composed package must certify its own `isGuarded` field; the
   run lemmas of step 2 quantify over split transcripts and do not give this.
4. **`GuardedCWSSPackage` + guarded `▷`** (Package.lean), fields spelled out:
   ```lean
   structure GuardedCWSSPackage init impl StmtIn WitIn StmtOut WitOut pSpec where
     verifier : Verifier oSpec StmtIn StmtOut pSpec
     struct : CWSSStructure pSpec
     relIn : Set (StmtIn × WitIn)
     relOut : Set (StmtOut × WitOut)
     isGuarded : verifier.IsGuarded
     isCWSS : verifier.coordinateWiseSpecialSound init impl struct relIn relOut

   def GuardedCWSSPackage.append [∀ i, SampleableType (pSpec₁.Challenge i)]
       (L₁ : GuardedCWSSPackage … pSpec₁) (L₂ : CWSSPackage … pSpec₂)
       (hseam : L₁.relOut = L₂.relIn := by rfl) : GuardedCWSSPackage … (pSpec₁ ++ₚ pSpec₂) where
     verifier := L₁.verifier.append L₂.verifier
     struct := L₁.struct.append L₂.struct
     relIn := L₁.relIn
     relOut := L₂.relOut
     isGuarded := L₁.isGuarded.append_isPureRight L₂.isPure
     isCWSS := append_coordinateWiseSpecialSound_of_guardedLeft … -- + hseam rewrite

   scoped infixr:65 " ▷! " => GuardedCWSSPackage.append   -- name/notation: maintainer's call
   ```
   The `[∀ i, SampleableType (pSpec₁.Challenge i)]` binder mirrors `CWSSPackage.append`
   (Package.lean:83) and is what Phase 4.3's pSpecHead instances exist to satisfy. (A pure
   package lifts to a guarded one via `check := fun _ _ => true` — provide
   `CWSSPackage.toGuarded` so mixed chains need only the one append.)
5. Do **not** build the guarded n-ary `seqCompose` here (the old plan's B4 second half) — the
   chain currently has exactly one guarded factor at the outer edge; the binary form suffices.
   Record the n-ary variant in the Basic.lean TODO instead. *Reason:* smallest reviewable
   framework change that unblocks Phase 6.

*Why this phase:* verified fact — every CWSS composition theorem in the tree demands
`V₁.verify stmt tr = pure (verify₁ stmt tr)` for the left factor; a rejecting head is therefore
uncomposable today. The existing helper pair (`append_run_pure_left` / `pure_accepting_of_mem` /
`mem_of_pure_accepting`) was verified to be exactly the right generalization surface.

Acceptance: guarded append theorem sorry-free; existing `append_*` theorems byte-identical
(`git diff` shows additions only); a toy `example` composing a trivially-guarded identity
verifier with a pure one.

---

## 9. Phase 6 — Chain assembly (1 d)

Host file (pinned): **new file `Hachi/RingSwitch/Chain.lean`**, importing `Hachi/Basic.lean` +
`Hachi/RingSwitch/Head.lean` — this keeps Basic.lean's imports free of the RingSwitch subtree;
Basic.lean receives only the diagram/TODO doc edits below.

First define the head package here (deferred from Phase 4.7 — the structure type is Phase 5's):

```lean
def headPackage (init impl) (h2) (hk) (hκα) {b ω γ : ℕ} … :
    GuardedCWSSPackage init impl (RingSwitchStatement …) (QuadEvalWitness …)
      (PolyEvalStatement 𝓜(q,α) …) (QuadEvalWitness …) (pSpecHead …) where
  verifier := headVerifier …
  struct := CWSSStructure.ofIsEmpty
  relIn := relRingSwitch (b : ZMod q)
    (quadEvalBetaSq γ b zDigits ((𝓜(q,α)).φ.natDegree) m messageDigits) γ (2 * ω)
  relOut := relPolyEval 𝓜(q,α) (b : ZMod q)
    (quadEvalBetaSq γ b zDigits ((𝓜(q,α)).φ.natDegree) m messageDigits) γ (2 * ω)
  isGuarded := ⟨headCheck …, toPolyEvalStatement …, fun _ _ => rfl⟩  -- shape per IsGuarded
  isCWSS := head_coordinateWiseSpecialSound … CWSSStructure.ofIsEmpty …

def ringSwitchChain (init impl) (hq5) (hκ) (hτ) (h2) (hk) (hκα) {b ω γ : ℕ} … :
    GuardedCWSSPackage init impl
      (RingSwitchStatement …) (QuadEvalWitness …)
      (QuadEvalStatement … × CarrierCom … × (Fin (2^r) → ShortChallenge …))
      (QuadEvalResponse …)
      (pSpecHead ++ₚ ((!p[] : ProtocolSpec 0) ++ₚ pSpec …)) :=
  headPackage … ▷! evalChain (b := b) (γ := γ) init impl hq5 hκ hτ

theorem ringSwitch_eval_coordinateWiseSpecialSound … :
    (…the composed verifier…).coordinateWiseSpecialSound init impl
      (CWSSStructure.ofIsEmpty.append (CWSSStructure.ofIsEmpty.append (foldStructure …)))
      (relRingSwitch (b : ZMod q) (quadEvalBetaSq …) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q,α) (b : ZMod q) ω γ) :=
  (ringSwitchChain …).isCWSS
```

Instantiation discipline (verified §1.3): the head package is constructed at base
`(b : ZMod q)`, `βSq := quadEvalBetaSq γ b zDigits ((𝓜(q,α)).φ.natDegree) m messageDigits`,
`κchal := 2 * ω` so the `▷!` autoparam seam closes by `rfl`. **Write the right factor as
`evalChain (b := b) (γ := γ) init impl hq5 hκ hτ`** — `b, γ` are implicit in `evalChain`'s
binders but absent from its result TYPE (verified), so leaving them to be solved through the
autoparam's `rfl` goal is elaboration-order-fragile; instantiate them explicitly.

Doc edits in `Hachi/Basic.lean` (same PR): in the header diagram (:51-74) mark the §3.1 head
done AND **delete the now-obsolete "σ₋₁ statement adapter — planned (0-round ReduceClaim)" row**
(:~58) — resolved by design, G2/G4: the head outputs `PolyEvalStatement` directly and the σ₋₁
twist is discharged inside `traceCheck_iff_recombine`; point the head's arrow straight at the
evalChain band. In the TODO block (:256-272): guarded-`▷` done, §3.1 head done, remaining items
unchanged.

*Why:* the deliverable theorem — subfield-point evaluation claim (paper §3.1 input) reduced to
Eq. (20) + range checks with zero added soundness error, composed from sorry-free parts.

Acceptance: theorem sorry-free; `./scripts/validate.sh` green; diagram/TODO updated in the same
PR (CLAUDE.md guardrail).

---

## 10. Phase 7 — Carrier instance + hygiene (1 d)

1. **`hachiCarrier`** (new `Hachi/RingSwitch/Carrier.lean`) — the corrected "S8 witness": a
   genuinely non-domain, `P = E` carrier:
   ```lean
   noncomputable def hachiCarrier (h2) (hk) :
       RingSwitchCarrier ↥(fixedSubring (R := ZMod q) α (2 ^ κRS)) where
     P := Rq (powTwoCyclotomic (R := ZMod q) α)
     E := ↥(fixedSubring (R := ZMod q) α (2 ^ κRS))   -- opening claims are base-valued
     ιP := Fin (2 ^ α / 2 ^ κRS)
     ιE := Unit
     packBasis := Module.Basis.ofEquivFun (psiLinearEquiv q α κRS h2 hk).symm
     openBasis := Module.Basis.singleton Unit _
     ntP := nontrivial_Rq_powTwoCyclotomic …   -- MUST be an explicit named field:
     ntE := …                                  -- Nontrivial (Rq …) is NOT a global instance
   ```
   **`ntP`/`ntE` must be assigned explicitly** — instance search cannot fill them (verified:
   `Nontrivial (Rq …)` exists only as an inline `haveI` at Subfield/Field.lean:298-302, which
   Phase 2.2 exports as `nontrivial_Rq_powTwoCyclotomic`; `ntE` = the subring nontriviality from
   Phase 2.2). `ftP` (= `Fintype (Fin _)`) and `ftE` (= `Fintype Unit`) synthesize; `algP` via
   Mathlib's `Algebra.ofSubring`; `algE` via `Algebra.id`. Note `Basis.ofEquivFun` wants
   `M ≃ₗ[R] (ι → R)`, i.e. `psiLinearEquiv.symm` — then `packBasis.repr = psiLinearEquiv.symm`
   definitionally (`ofEquivFun_repr_apply`, rfl), tying the carrier to Phase 3's `psiInv` by
   `rfl`. Sanity `example`s: `hachiCarrier.packBasis.repr Y v = psiInv q α κRS h2 hk Y v := rfl`
   (this one IS rfl); `recombineCheck (hachiCarrier …) w Y y ↔ (Phase 4's check)` — **not rfl**:
   the sums range over `Fin (2^α/2^κRS)` vs `Fin (2^(α−κRS))` (not defeq, G7); prove via
   `Fintype.sum_equiv (packIndexEquiv α κRS hκα)` with
   `w := (CMlPolynomial.monomialBasis xt).get ∘ packIndexEquiv α κRS hκα`.
   *Why:* pins the generic-layer correspondence, gives the branch its promised non-domain carrier
   with the **correct** (packing-stage) role, and keeps `Generic/PackedClaim.lean`'s lemmas
   honest against a real instance. Not on the head's proof-critical path — if instance plumbing
   fights (`Nontrivial (Rq …)` derivation), timebox to half a day and land the carrier with the
   Nontrivial argument as an explicit hypothesis-parameter instead.
2. Wiki/KB: `repo-map.md` (Generic/PackedClaim, Hachi/RingSwitch/), KB ring-switching page
   (packing-stage + corrected S8 + the `hachiCarrier` pointer), `docs/kb/papers/NOZ26.md` gap
   list if present.
3. Update `HACHI_RING_SWITCHING_PLAN.md`: mark B1–B3 superseded by `Generic/PackedClaim.lean`,
   B4 superseded by Phase 5 (binary case; n-ary still open), C1–C3 + D1–D2 superseded by Phases
   2–4 + 6; note R2 and D5's twist are resolved-by-design (G2); Phases A, E–G unaffected
   (Phase E's derive-`y₀` head and Phases F/G continue to apply downstream of this plan's head).
4. `./scripts/validate.sh --lint` (and `--docs` if docstrings were the day's work).

---

## 11. Standing hypotheses & conventions (pin before writing any Lean)

- `q` prime, `[Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]`; `q` explicit
  in lattice-layer lemmas (house style). `h2 : (2 : ZMod q) ≠ 0` threaded explicitly (derivable
  from `q % 8 = 5` at the chain level if desired — small lemma, optional).
- `hk : 2 * 2 ^ κRS ∣ 2 ^ α` everywhere ψ appears; `hκα : κRS ≤ α` via
  `succ_le_of_two_mul_two_pow_dvd`.
- **`κRS` (packing) vs `κ`/`κchal` (chain challenge param, instantiated `2 * ω`) vs paper-`κ`**:
  three different things; the file headers of Head.lean/Unpack.lean must carry the dictionary.
- Index forms: `2 ^ α / 2 ^ κRS` in all ψ-adjacent types; `2 ^ (α − κRS)` only after
  `packIndexEquiv`; **no other casts**.
- Variable order: unpacked polynomial has the packed tail **last** (`(xl ++ xh) ++ xt`), matching
  the paper and `relPolyEval`'s `xl ++ xh`; the branch's `curryFamily` (prefix packing) is NOT
  used by the Hachi path — do not import its convention.
- All new Hachi-side defs `noncomputable` where ψ/traceH forces it; the guard check is
  Bool-valued per **G9** (`headCheck := decide (…)`; no un-scoped `Classical`); coercions
  `B → Rq` go through `coeVec` (Phase 3 — bare `(↑·)` does not elaborate).
- New files must be `git add`ed before `./scripts/update-lib.sh` / validation (generated
  `ArkLib.lean`).

## 12. What NOT to do (each has bitten before)

- Do not hand-edit `ArkLib.lean` (generated; `scripts/update-lib.sh`).
- Do not `open ArkLib.Lattices` in chain files (ambiguous `⬝ᵥ` — verified docstring warning).
  The ban is on that namespace **itself**; opening the leaf namespaces
  `ArkLib.Lattices.CyclotomicModulus` (needed for psi/traceH/fixedSubring — Basic.lean:97
  already does it) and `ArkLib.Lattices.Hachi` is safe and required.
- Do not resolve `Fin (2^α/2^κ)` vs `Fin (2^(α−κ))` mid-proof — go through `packIndexEquiv`.
- Do not route the Hachi head through `BatchingStrategy`, `DenseMLPCS`, or the MvPolynomial
  generic lemmas (G1/G5) — the RBR obligations are unfilled and there is no CWSS bridge.
- Do not add `sorry` inside structures or instances; laws are theorem hypotheses (G6).
- Do not modify `openingClaimRel`/`sliceRel`/`sumcheckClaimRel`/`BatchingStrategy` definitions —
  Phase 1 is additive plus docstrings only (the branch's Binius path must stay intact).
- Do not build the CWSS work on `origin/cwss-components-infra` — it *lacks* `ofIsEmpty`,
  `SingleRound.lean`, `Package.lean` (verified); the working tree is the source of truth.
- Do not conflate `Hachi.toPolynomial` (matrix reshape) with CompPoly's
  `CMlPolynomial.toMvPolynomial` (no eval lemma).

## 13. Risk register

| # | Risk | Mitigation |
|---|---|---|
| R1 | `treeSpecialSound`'s output-witness flow differs from what Phase 4.6 assumes | **Resolved by verification**: the direct route is viable — the no-challenge bridge (NoChallenge.lean:118) imposes no purity, so the guarded 1-message head is provable by mirroring SendWitness (pSpec shape, `tr 0`) + ReduceClaim (`hpick`/`Exists.choose` witOut recovery from `Set.mem_language_iff`) + the new `not_accepting_of_failure` helper (executable spec: `CheckClaim.knowledgeStateFunction.toFun_full`). The 2-factor-decomposition fallback is legal only with the guarded factor as the RIGHT append factor, still requires Phase 5 for the outer composition, and reuses no existing CWSS theorem — prefer the direct route. |
| R2 | `PolyMatrix` orientation in `unpackPoly` transposed | Acceptance test is `unpackPoly_eval` itself; fix at the definition (G7), plus the Phase 3 toy example. |
| R3 | Framework changes (Phase 5) touch shared files | Coordinate with maintainers; additions only; existing theorems byte-identical (acceptance-checked). |
| R4 | `Vector.map_append` or similar plumbing missing in the Vector API used by CompPoly | Prove locally (3-line `ext`); do not refactor the Vector library. |
| R5 | `DecidableEq (Rq …)` not available where Phase 4.3's `decide` needs it | Derive from the chain's `[LawfulBEq (ZMod q)]` context (e.g. `instDecidableEqOfLawfulBEq`-style, or add the instance next to `Rq`'s `commRing`); last resort: `headCheck` via `==` (`BEq`) with a `LawfulBEq` bridge lemma into the Prop form used by `relRingSwitch` (still G9-conformant — the check stays Bool). |
| R6 | Merge conflicts from the dirty working tree at Phase 0 | Commit first (hard requirement in Phase 0.1). |
| R7 | `Nontrivial (Rq …)` instance derivation fights (Phase 7) | Timeboxed; hypothesis-parameter fallback specified. |
| R8 | Branch author's in-flight S6 work collides with Phase 1 | Phase 1 is additive + docstrings; raise the PackedClaim stage with the author before merging (it slots as a new stage between S2 and S5 in their numbering). |
