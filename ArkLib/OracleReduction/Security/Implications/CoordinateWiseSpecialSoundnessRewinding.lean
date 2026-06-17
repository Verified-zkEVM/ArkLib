/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ForkOracle

/-!
  # Coordinate-Wise Special Soundness ⇒ Rewinding Knowledge Soundness

  This file carries the implication `coordinateWiseSpecialSound → knowledgeSoundnessRewinding`,
  instantiating the abstract rewinding knowledge-soundness notion
  (`Verifier.knowledgeSoundnessRewinding`) with the CWSS fork oracle
  (`CWSSStructure.forkOracle`, implemented by `CWSSStructure.cwssForkImpl`).

  ## Two-phase extraction

  The rewinding extractor (`CWSSStructure.rewindingExtractor`) is factored into an *effectful*
  collection phase and a *pure* assembly phase, so that all monadic (support-level) reasoning is
  concentrated in a single lemma:

  1. **Collect** (`CWSSStructure.collectForest`, effectful): by round induction
     (`Fin.reverseInduction`, from the last round backwards), gather a `RunForest` — at each
     challenge round `i`, for each coordinate `j < ℓᵢ`, query the fork oracle `kᵢ - 1` times with
     accumulating `avoid` sets (`collectSiblingRuns`; single-shot, any failed or rejecting fork
     aborts), recursing into each sibling run for its own subforest. The forest stores only the
     collected `SiblingRun`s; no tree assembly happens here.
  2. **Assemble** (`RunForest.toTree`, pure): turn the forest into a `ChallengeTree`, reading
     messages and challenge labels off the transcripts (the central path's transcript threads
     through the recursion; sibling subtrees assemble relative to their own transcripts).

  Correctness factors accordingly:

  * `collectForest_wellFormed` — the **only monadic lemma**: any collected forest satisfies the
    pure predicate `RunForest.WellFormed` (per-node `CoordEq`, pairwise-distinct coordinate
    values, transcript-prefix agreement, accepted outputs), and each collected run's transcript
    is accepted with certainty. This is where the fork-oracle guarantees
    (`cwssForkImpl_coordEq`, `cwssForkImpl_prefix_eq`, `cwssForkImpl_realizes`) and the bridging
    hypotheses (`ReplayConsistent`, `DeterminateAcceptance`, realizedness of the central path)
    are consumed.
  * `RunForest.WellFormed.toTree_isStructured` and
    `RunForest.WellFormed.mem_toTree_fullTranscripts` — **pure inductions** over the forest: the
    assembled tree is `D`-structured, and each of its root-to-leaf transcripts is the central
    transcript or the transcript of a collected (accepted) run.

  ## The extraction bound

  The reference (expected-time) knowledge error is `CWSSStructure.knowledgeError`
  (`∑ᵢ ℓᵢ·(kᵢ-1)/|Sᵢ|`, [FMN24] Lemma 2.31 — [NOZ26] Lemma 4 misprints the denominator as
  `|Sᵢ|^{ℓᵢ}`; see the `knowledgeError` docstring). It is **not** achievable by the bounded
  (`OracleComp`) extractor here: with single-shot forks the guarantee is a forking-lemma-style
  function `CWSSStructure.forkBound` of the prover's acceptance probability. Its closed form is
  pinned down by the quantitative analysis of the collection phase and is left `sorry`-defined
  until that analysis is carried out — deliberately so: committing to a formula before the proof
  risks repeating the [NOZ26] Lemma 4 mistake in the other direction.

  ## References

  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec ProtocolSpec.ChallengeTree
open scoped NNReal ENNReal

/-- Collect a `Fin ℓ`-indexed family of monadic results, in index order. -/
private def gatherFin {m : Type → Type*} [Monad m] {β : Type} :
    (ℓ : ℕ) → ((j : Fin ℓ) → m β) → m (Fin ℓ → β)
  | 0, _ => pure Fin.elim0
  | ℓ + 1, f => do
    let hd ← f 0
    let tl ← gatherFin ℓ (fun j => f j.succ)
    pure (Fin.cons hd tl)

namespace CWSSStructure

variable {n : ℕ} {pSpec : ProtocolSpec n}

/- DEPRECATED (single-shot forking route) — superseded by the seeded-replay architecture.
  The seeded route targets the additive bound `fun ε => ε - D.knowledgeError` directly, so this
  non-linear `forkBound` constant is no longer used. Commented out (not deleted) for reference;
  remove once the seeded implication lands.

/-- The extraction-success lower bound achieved by the single-shot tree builder, as a function of
  the prover's acceptance probability `ε`, for the protocol structure `D`.

  Its closed form is determined by the quantitative analysis of `collectForest` (a per-fork
  forking-lemma factor of shape `ε·(ε - |avoid|/|Sᵢ|)`, composed by round induction over the
  `∏ᵢ (ℓᵢ·(kᵢ-1)+1)` nodes of the tree) and is `sorry`-defined until that analysis is carried
  out, so that downstream statements can depend on the implication's *shape* without committing
  to a possibly-unprovable constant. The expected-time reference target is the linear bound
  `fun ε => ε - D.knowledgeError` ([FMN24] Lemma 2.31), which no bounded extractor achieves. -/
noncomputable def forkBound (D : CWSSStructure pSpec) [∀ i, Fintype (D.alphabet i)] :
    ℝ≥0∞ → ℝ≥0∞ := sorry
-/

/-! ## The run forest: collected fork data, separated from tree assembly -/

/-- A **run forest**: the raw data collected by the forking phase of the extractor, mirroring the
  shape of a `ChallengeTree` but storing only the collected sibling runs. A node of a challenge
  round `i` carries, for each coordinate `j < ℓᵢ` and each of the `kᵢ - 1` sibling slots, the
  forked `SiblingRun` and its own subforest; the central path's data is *not* stored — it is
  threaded as a transcript through assembly (`toTree`) and well-formedness (`WellFormed`).

  The sibling runs and subforests are two separate function fields (rather than one function into
  a product) so that the recursive occurrence is not nested under `Prod`, which the kernel
  forbids (cf. `ChallengeTree`). -/
inductive RunForest {n : ℕ} {pSpec : ProtocolSpec n} (D : CWSSStructure pSpec)
    (StmtOut : Type) : Fin (n + 1) → Type where
  /-- A leaf, reached once all `n` rounds have been processed. -/
  | leaf : RunForest D StmtOut (Fin.last n)
  /-- A message round: nothing is collected; the message lives in the central transcript. -/
  | msgNode (m : Fin n) (h : pSpec.dir m = .P_to_V)
      (child : RunForest D StmtOut m.succ) : RunForest D StmtOut m.castSucc
  /-- A challenge round: the central path continues in `center`; `siblingRuns j t` is the `t`-th
    collected sibling at coordinate `j`, and `siblingForests j t` its subforest. -/
  | chalNode (m : Fin n) (h : pSpec.dir m = .V_to_P)
      (center : RunForest D StmtOut m.succ)
      (siblingRuns : Fin (D.coordIndex ⟨m, h⟩) → Fin (D.soundnessParam ⟨m, h⟩ - 1) →
        SiblingRun pSpec StmtOut)
      (siblingForests : Fin (D.coordIndex ⟨m, h⟩) → Fin (D.soundnessParam ⟨m, h⟩ - 1) →
        RunForest D StmtOut m.succ) :
      RunForest D StmtOut m.castSucc

namespace RunForest

variable {StmtOut : Type} {D : CWSSStructure pSpec}

/-- All sibling runs collected in a forest, in some canonical order. -/
def runs : {m : Fin (n + 1)} → RunForest D StmtOut m → List (SiblingRun pSpec StmtOut)
  | _, .leaf => []
  | _, .msgNode _ _ child => child.runs
  | _, .chalNode _ _ center siblingRuns siblingForests =>
      center.runs ++ (List.finRange _).flatMap fun j =>
        (List.finRange _).flatMap fun t =>
          siblingRuns j t :: (siblingForests j t).runs

/-- **Pure assembly**: turn a run forest into a `ChallengeTree`, relative to the central
  transcript `tr`. Messages and the central challenge label are read off `tr`; sibling challenge
  labels are read off the sibling transcripts, and sibling subtrees assemble relative to their
  own transcripts. The `ℓᵢ·(kᵢ-1)` sibling slots are indexed via `finProdFinEquiv`, with the
  central child at index `0`. -/
def toTree : {m : Fin (n + 1)} → FullTranscript pSpec → RunForest D StmtOut m →
    ChallengeTree pSpec D.arity m
  | _, _, .leaf => .leaf
  | _, tr, .msgNode m h child => .msgNode m h (tr m) (child.toTree tr)
  | _, tr, .chalNode m h center siblingRuns siblingForests =>
      .chalNode m h
        (Fin.cons (tr.challenges ⟨m, h⟩) (fun s =>
          (siblingRuns (finProdFinEquiv.symm s).1
            (finProdFinEquiv.symm s).2).transcript.challenges ⟨m, h⟩))
        (Fin.cons (center.toTree tr) (fun s =>
          (siblingForests (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2).toTree
            (siblingRuns (finProdFinEquiv.symm s).1 (finProdFinEquiv.symm s).2).transcript))

/-- **Pure well-formedness** of a run forest relative to its central transcript `tr`: at every
  challenge node, each collected sibling

  1. has a round-`i` challenge vector that is `CoordEq j` to the central one,
  2. has a value at coordinate `j` distinct from every other sibling of the same coordinate,
  3. agrees with the central transcript on the *entire* transcript strictly before the fork
     round (challenges *and* messages — this is what makes assembled root-to-leaf paths genuine
     transcripts), and
  4. was accepted (`stmtOut ∈ langOut`),

  and its subforest is well-formed relative to the sibling's own transcript. This is the pure
  interface between the (monadic) collection phase and the (pure) structure/acceptance lemmas:
  `collectForest_wellFormed` establishes it, `toTree_isStructured` and
  `mem_toTree_fullTranscripts` consume it. -/
def WellFormed (langOut : Set StmtOut) :
    {m : Fin (n + 1)} → FullTranscript pSpec → RunForest D StmtOut m → Prop
  | _, _, .leaf => True
  | _, tr, .msgNode _ _ child => child.WellFormed langOut tr
  | _, tr, .chalNode m h center siblingRuns siblingForests =>
      center.WellFormed langOut tr ∧
      ∀ (j : Fin (D.coordIndex ⟨m, h⟩)) (t : Fin (D.soundnessParam ⟨m, h⟩ - 1)),
        CoordinateWise.CoordEq j
          (D.decompose ⟨m, h⟩ (tr.challenges ⟨m, h⟩))
          (D.decompose ⟨m, h⟩ ((siblingRuns j t).transcript.challenges ⟨m, h⟩)) ∧
        (∀ t', t' ≠ t →
          D.decompose ⟨m, h⟩ ((siblingRuns j t').transcript.challenges ⟨m, h⟩) j ≠
          D.decompose ⟨m, h⟩ ((siblingRuns j t).transcript.challenges ⟨m, h⟩) j) ∧
        (∀ m' : Fin n, m' < m → (siblingRuns j t).transcript m' = tr m') ∧
        (siblingRuns j t).stmtOut ∈ langOut ∧
        (siblingForests j t).WellFormed langOut (siblingRuns j t).transcript

/-- **Pure structure lemma**: a well-formed forest assembles into a `D`-structured tree.

  *Proof route:* pure induction over the forest. At a challenge node, take the center `e := 0`;
  clause 1 gives the `CoordEq` siblings for each coordinate, and clauses 1–2 give injectivity of
  the whole challenge family (siblings of one coordinate are pairwise distinct there; siblings of
  different coordinates differ from the center at different coordinates, hence from each
  other). -/
theorem WellFormed.toTree_isStructured {langOut : Set StmtOut} {m : Fin (n + 1)}
    {tr : FullTranscript pSpec} {forest : RunForest D StmtOut m}
    (hwf : forest.WellFormed langOut tr) :
    (forest.toTree tr).IsStructured D := by
  induction forest generalizing tr with
  | leaf => exact trivial
  | msgNode m h child ih =>
    simp only [RunForest.WellFormed] at hwf
    simp only [RunForest.toTree, ChallengeTree.IsStructured]
    exact ih hwf
  | chalNode m h center siblingRuns siblingForests ih_center ih_sib =>
    simp only [RunForest.WellFormed] at hwf
    obtain ⟨hcenter, hsib⟩ := hwf
    simp only [RunForest.toTree, ChallengeTree.IsStructured]
    refine ⟨?_, ?_⟩
    · -- The sibling challenges form a coordinate-wise special-sound family `SS(Sᵢ, ℓᵢ, kᵢ)`.
      simp only [CoordinateWise.IsSpecialSoundFamily]
      refine ⟨?_, 0, fun i => ?_⟩
      · -- Injectivity of the whole challenge family `c`.
        intro a b hab
        rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩ <;>
          rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
        · rfl
        · -- central vs sibling: they differ in the sibling's fork coordinate (clause 1).
          simp only [Fin.cons_zero, Fin.cons_succ] at hab
          exact absurd (congrFun hab (finProdFinEquiv.symm b').1)
            (hsib (finProdFinEquiv.symm b').1 (finProdFinEquiv.symm b').2).1.1
        · simp only [Fin.cons_zero, Fin.cons_succ] at hab
          exact absurd (congrFun hab.symm (finProdFinEquiv.symm a').1)
            (hsib (finProdFinEquiv.symm a').1 (finProdFinEquiv.symm a').2).1.1
        · -- two siblings: equal coordinate (clause 1) and equal slot (clause 2).
          simp only [Fin.cons_succ] at hab
          have hjab : (finProdFinEquiv.symm a').1 = (finProdFinEquiv.symm b').1 := by
            by_contra hjne
            have h1 := (hsib (finProdFinEquiv.symm a').1 (finProdFinEquiv.symm a').2).1.2
              (finProdFinEquiv.symm b').1 (Ne.symm hjne)
            have h2 := congrFun hab (finProdFinEquiv.symm b').1
            exact (hsib (finProdFinEquiv.symm b').1 (finProdFinEquiv.symm b').2).1.1 (h1.trans h2)
          have htab : (finProdFinEquiv.symm a').2 = (finProdFinEquiv.symm b').2 := by
            by_contra htne
            rw [hjab] at hab
            have h2 := congrFun hab (finProdFinEquiv.symm b').1
            exact (hsib (finProdFinEquiv.symm b').1 (finProdFinEquiv.symm b').2).2.1
              (finProdFinEquiv.symm a').2 htne h2
          have hsymm : finProdFinEquiv.symm a' = finProdFinEquiv.symm b' := Prod.ext hjab htab
          rw [finProdFinEquiv.symm.injective hsymm]
      · -- For coordinate `i`, the `kᵢ-1` siblings of `i` are `CoordEq i` to the central vector.
        refine ⟨Finset.image (fun t => (finProdFinEquiv (i, t)).succ) Finset.univ, ?_, ?_, ?_⟩
        · intro h0
          rw [Finset.mem_image] at h0
          obtain ⟨t, -, ht⟩ := h0
          exact Fin.succ_ne_zero _ ht
        · have hinj : Function.Injective
              (fun t : Fin (D.soundnessParam ⟨m, h⟩ - 1) => (finProdFinEquiv (i, t)).succ) := by
            intro t1 t2 ht
            have := finProdFinEquiv.injective (Fin.succ_injective _ ht)
            exact (Prod.ext_iff.1 this).2
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        · intro j hj
          rw [Finset.mem_image] at hj
          obtain ⟨t, -, rfl⟩ := hj
          simp only [Fin.cons_zero, Fin.cons_succ, Equiv.symm_apply_apply]
          exact (hsib i t).1
    · -- Each child of the assembled node is itself structured (induction hypotheses).
      intro s
      rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
      · simp only [Fin.cons_zero]
        exact ih_center hcenter
      · simp only [Fin.cons_succ]
        exact ih_sib _ _ (hsib _ _).2.2.2.2

/-- **Prefix agreement propagates through `concat`**: if `pre` agrees with `tr` on rounds `< m`
  (the path prefix), `T` agrees with `tr` on rounds `< m` (the new central transcript shares the
  prefix), and `v` is `T`'s round-`m` entry, then `pre` extended by `v` agrees with `T` on rounds
  `< m+1`. This is the single index-bookkeeping step of the path lemma. -/
private theorem agree_snoc {m : Fin n} (pre : Transcript m.castSucc pSpec)
    (tr T : FullTranscript pSpec) (v : pSpec.«Type» m)
    (hpre : ∀ i : Fin m.castSucc.val, pre i = tr (Fin.castLE m.castSucc.is_le i))
    (hbelow : ∀ i : Fin n, i.val < m.val → T i = tr i)
    (hv : v = T m) :
    ∀ i : Fin m.succ.val, (pre.concat v) i = T (Fin.castLE m.succ.is_le i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · -- last round `m`: `pre.concat v` reads `v = T m` here, and `castLE _ (last) = m` (defeq).
    simp only [Transcript.concat, Fin.snoc_last, hv]
    rfl
  · -- earlier round `j < m`: `pre.concat v` reads `pre j`, which agrees with `tr` hence with `T`.
    simp only [Transcript.concat, Fin.snoc_castSucc]
    rw [hpre j]
    -- `castLE m.castSucc.is_le j` and `castLE m.succ.is_le j.castSucc` are defeq (same value `j`).
    exact (hbelow _ (by simp only [Fin.val_castLE, Fin.val_castSucc]; exact j.isLt)).symm

/-- **Generalized path lemma**: for a forest at round `m`, a central transcript `tr`, and a path
  prefix `pre` that agrees with `tr` on rounds `< m`, every transcript produced by
  `(forest.toTree tr).transcripts pre` is `tr` itself or one of the collected (accepted) runs'
  transcripts. The `mem_toTree_fullTranscripts` lemma is the `m = 0`, `pre = default` case. -/
private theorem aux_mem_transcripts {langOut : Set StmtOut} :
    ∀ {m : Fin (n + 1)} (forest : RunForest D StmtOut m) (tr : FullTranscript pSpec)
      (pre : Transcript m pSpec),
      forest.WellFormed langOut tr →
      (∀ i : Fin m.val, pre i = tr (Fin.castLE m.is_le i)) →
      ∀ tr' ∈ (forest.toTree tr).transcripts pre,
        tr' = tr ∨ ∃ r ∈ forest.runs, tr' = r.transcript ∧ r.stmtOut ∈ langOut := by
  intro m forest
  induction forest with
  | leaf =>
    intro tr pre _ hAgree tr' htr'
    simp only [RunForest.toTree, ChallengeTree.transcripts, List.mem_singleton] at htr'
    subst htr'
    refine Or.inl ?_
    funext i
    -- `pre i = tr (castLE (last n).is_le i) = tr i` since `castLE (last n).is_le i = i` (defeq).
    rw [hAgree i]
    rfl
  | msgNode m h child ih =>
    intro tr pre hWF hAgree tr' htr'
    simp only [RunForest.toTree, ChallengeTree.transcripts] at htr'
    simp only [RunForest.WellFormed] at hWF
    exact ih tr (pre.concat (tr m)) hWF
      (agree_snoc pre tr tr (tr m) hAgree (fun _ _ => rfl) rfl) tr' htr'
  | chalNode m h center sibRuns sibForests ih_center ih_sib =>
    intro tr pre hWF hAgree tr' htr'
    simp only [RunForest.toTree, ChallengeTree.transcripts, List.mem_flatMap,
      List.mem_finRange, true_and] at htr'
    simp only [RunForest.WellFormed] at hWF
    obtain ⟨hWFcenter, hWFsib⟩ := hWF
    obtain ⟨s, htr'⟩ := htr'
    rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s', rfl⟩
    · -- central branch: the path follows the central transcript at this round
      simp only [Fin.cons_zero] at htr'
      rcases ih_center tr (pre.concat (tr.challenges ⟨m, h⟩)) hWFcenter
          (agree_snoc pre tr tr (tr.challenges ⟨m, h⟩) hAgree (fun _ _ => rfl) rfl) tr' htr'
        with h | ⟨r, hr, hreq, hracc⟩
      · exact Or.inl h
      · refine Or.inr ⟨r, ?_, hreq, hracc⟩
        simp only [RunForest.runs]
        exact List.mem_append_left _ hr
    · -- sibling branch `(j, t)`: the central transcript becomes the sibling's own transcript
      simp only [Fin.cons_succ] at htr'
      set j := (finProdFinEquiv.symm s').1 with hj
      set t := (finProdFinEquiv.symm s').2 with ht
      rcases ih_sib j t (sibRuns j t).transcript
          (pre.concat ((sibRuns j t).transcript.challenges ⟨m, h⟩))
          (hWFsib j t).2.2.2.2
          (agree_snoc pre tr (sibRuns j t).transcript
            ((sibRuns j t).transcript.challenges ⟨m, h⟩) hAgree
            (fun i hi => (hWFsib j t).2.2.1 i hi) rfl) tr' htr'
        with h | ⟨r, hr, hreq, hracc⟩
      · -- the path stays central inside the sibling: `tr'` is exactly the sibling's transcript
        refine Or.inr ⟨sibRuns j t, ?_, h, (hWFsib j t).2.2.2.1⟩
        simp only [RunForest.runs]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_finRange _,
          List.mem_flatMap.mpr ⟨t, List.mem_finRange _, List.mem_cons_self⟩⟩)
      · -- the path deviates deeper inside the sibling subforest
        refine Or.inr ⟨r, ?_, hreq, hracc⟩
        simp only [RunForest.runs]
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_finRange _,
          List.mem_flatMap.mpr ⟨t, List.mem_finRange _, List.mem_cons_of_mem _ hr⟩⟩)

/-- **Pure path lemma**: every root-to-leaf transcript of the assembled tree is either the
  central transcript or the transcript of one of the collected (accepted) runs.

  *Proof route:* pure induction over the forest, with clause 3 of `WellFormed` propagating prefix
  agreement: a path through the sibling `(j, t)` branch has the central prefix below the fork
  round, which equals the sibling transcript's own prefix; deeper branches compose
  transitively. -/
theorem WellFormed.mem_toTree_fullTranscripts {langOut : Set StmtOut}
    {tr : FullTranscript pSpec} {forest : RunForest D StmtOut 0}
    (hwf : forest.WellFormed langOut tr) :
    ∀ tr' ∈ (forest.toTree tr).fullTranscripts,
      tr' = tr ∨ ∃ r ∈ forest.runs, tr' = r.transcript ∧ r.stmtOut ∈ langOut := by
  intro tr' htr'
  simp only [ChallengeTree.fullTranscripts] at htr'
  exact aux_mem_transcripts forest tr default hwf (fun i => i.elim0) tr' htr'

end RunForest

/- DEPRECATED (single-shot collection phase + its correctness proofs) — superseded by the
  seeded-replay exhaustive collector. The block below is commented out (not deleted); the
  following parts are REUSABLE and should be lifted/adapted for the seeded route:

    • `simulateQ_addLift_fork` (H1) and `reachable_trans` (H2): generic, port verbatim.
    • `AcceptedCert`: the certain-acceptance shorthand, route-independent.
    • `collectSiblingRuns_spec` / `gatherFin_spec` / `aux_wellFormed` / `collectForest_wellFormed`:
      the reverse-induction proof technique (thread realizedness + reachability through the
      collector) transfers directly to the seeded collector's WellFormed lemma.

  Still LIVE above this block (route-independent, reused as-is by the seeded route):
  `gatherFin`, `RunForest`, `runs`, `toTree`, `WellFormed`, `WellFormed.toTree_isStructured`,
  `WellFormed.mem_toTree_fullTranscripts`.

/-! ## The collection phase (effectful) -/

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type} {σ : Type}

/-- Collect `t` sibling runs at coordinate `(i, j)` of the parent run `tr`, by querying the fork
  oracle with an `avoid` set accumulating the collected coordinate values (without-replacement
  sampling, [FMN24] Fig. 11), and recurse (via `rec`) into each sibling for its subforest.

  Single-shot semantics: a failed fork (`none`) or a rejecting sibling (`stmtOut ∉ langOut`)
  aborts the whole collection (`failure`). -/
def collectSiblingRuns (D : CWSSStructure pSpec) [∀ i, DecidableEq (D.alphabet i)]
    (langOut : Set StmtOut) [DecidablePred (· ∈ langOut)] {m' : Fin (n + 1)}
    (rec : FullTranscript pSpec →
      OptionT (OracleComp (oSpec + D.forkOracle StmtOut)) (RunForest D StmtOut m'))
    (tr : FullTranscript pSpec) (i : pSpec.ChallengeIdx) (j : Fin (D.coordIndex i)) :
    (t : ℕ) → Finset (D.alphabet i) →
      OptionT (OracleComp (oSpec + D.forkOracle StmtOut))
        (Fin t → SiblingRun pSpec StmtOut × RunForest D StmtOut m')
  | 0, _ => pure Fin.elim0
  | t + 1, avoid => do
    let fq : D.ForkQuery := ⟨tr, i, j, avoid⟩
    let some r ← liftM
        (query (spec := oSpec + D.forkOracle StmtOut)
          (m := OracleComp (oSpec + D.forkOracle StmtOut)) (Sum.inr fq))
      | failure
    if r.stmtOut ∈ langOut then
      let forest ← rec r.transcript
      let rest ← D.collectSiblingRuns langOut rec tr i j t
        (insert (D.decompose i (r.transcript.challenges i) j) avoid)
      pure (Fin.cons (r, forest) rest)
    else failure

/-- **The collection phase**: gather a `RunForest` for the rounds `m, m+1, …, n-1`, taking the
  run `tr` as the central path, by reverse induction on the round index `m`. At a challenge
  round, `collectSiblingRuns` forks `tr` at each coordinate; the builder recurses into each
  sibling's run for its subforest. Single-shot: any failed fork or rejecting sibling aborts
  (`failure`). -/
def collectForest (D : CWSSStructure pSpec) [∀ i, DecidableEq (D.alphabet i)]
    (langOut : Set StmtOut) [DecidablePred (· ∈ langOut)] (m : Fin (n + 1)) :
    FullTranscript pSpec →
      OptionT (OracleComp (oSpec + D.forkOracle StmtOut)) (RunForest D StmtOut m) :=
  Fin.reverseInduction
    (motive := fun m => FullTranscript pSpec →
      OptionT (OracleComp (oSpec + D.forkOracle StmtOut)) (RunForest D StmtOut m))
    (fun _ => pure .leaf)
    (fun m rec tr =>
      match h : pSpec.dir m with
      | .P_to_V => do
        let child ← rec tr
        pure (.msgNode m h child)
      | .V_to_P => do
        let center ← rec tr
        let sibs ← gatherFin (D.coordIndex ⟨m, h⟩) (fun j =>
          D.collectSiblingRuns langOut rec tr ⟨m, h⟩ j (D.soundnessParam ⟨m, h⟩ - 1) ∅)
        pure (.chalNode m h center (fun j t => (sibs j t).1) (fun j t => (sibs j t).2)))
    m

/-- The **tree builder**: collect a run forest from the central transcript, then assemble it
  purely. The two phases are separated so that support-level reasoning concentrates in
  `collectForest_wellFormed` while structure and acceptance are pure inductions
  (`RunForest.WellFormed.toTree_isStructured`, `RunForest.WellFormed.mem_toTree_fullTranscripts`).
-/
def treeBuilder (D : CWSSStructure pSpec) [∀ i, DecidableEq (D.alphabet i)]
    (langOut : Set StmtOut) [DecidablePred (· ∈ langOut)] (m : Fin (n + 1))
    (tr : FullTranscript pSpec) :
    OptionT (OracleComp (oSpec + D.forkOracle StmtOut)) (ChallengeTree pSpec D.arity m) :=
  (RunForest.toTree tr) <$> D.collectForest langOut m tr

/-- The rewinding extractor realizing the CWSS implication: build a tree of transcripts from the
  measured run's transcript (its central path) via `treeBuilder`, then apply the deterministic
  `TreeBased` extractor supplied by `coordinateWiseSpecialSound`. -/
def rewindingExtractor (D : CWSSStructure pSpec) [∀ i, DecidableEq (D.alphabet i)]
    (langOut : Set StmtOut) [DecidablePred (· ∈ langOut)]
    (E₀ : Extractor.TreeBased StmtIn WitIn pSpec D.arity) :
    Extractor.Rewinding oSpec (D.forkOracle StmtOut) StmtIn WitIn WitOut pSpec :=
  fun stmtIn _witOut transcript _proveQueryLog _verifyQueryLog => do
    let tree ← D.treeBuilder langOut 0 transcript
    pure (E₀ stmtIn tree)

/-! ## Correctness of the collection phase -/

variable {D : CWSSStructure pSpec}
  [∀ i, SampleableType (pSpec.Challenge i)] [∀ i, SampleableType (D.alphabet i)]
  [∀ i, DecidableEq (D.alphabet i)]
  {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {verifier : Verifier oSpec StmtIn StmtOut pSpec}
  {stmtIn : StmtIn} {witIn : WitIn}
  {prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec}
  {langOut : Set StmtOut} [DecidablePred (· ∈ langOut)]

/-- **H1 — fork-query reduction**: under the combined implementation `impl.addLift forkImpl`, a
  fork query (`Sum.inr fq`) is answered by `forkImpl fq`, independent of `impl`. The right-summand
  analog of `simulateQ_addLift_getChallenge`. -/
private lemma simulateQ_addLift_fork
    (forkImpl : QueryImpl (D.forkOracle StmtOut) (StateT σ ProbComp)) (fq : D.ForkQuery) :
    simulateQ (impl.addLift forkImpl :
        QueryImpl (oSpec + D.forkOracle StmtOut) (StateT σ ProbComp))
      (query (spec := oSpec + D.forkOracle StmtOut)
        (m := OracleComp (oSpec + D.forkOracle StmtOut)) (Sum.inr fq)) = forkImpl fq := by
  change simulateQ (impl.addLift forkImpl)
    (liftM (OracleSpec.query (spec := oSpec + D.forkOracle StmtOut) (Sum.inr fq))) = forkImpl fq
  rw [simulateQ_spec_query, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_self]

/-- **H2 — reachability transitivity** (local copy; the `ForkOracle` version is `private`). -/
private lemma reachable_trans {s a b : σ}
    (h1 : impl.Reachable s a) (h2 : impl.Reachable a b) : impl.Reachable s b := by
  induction h2 with
  | refl => exact h1
  | step _ hmem ih => exact QueryImpl.Reachable.step ih hmem

/-- Shorthand: the verifier accepts transcript `tr` with certainty when run from a fresh initial
  oracle state. This is the per-run conclusion of `collectForest_wellFormed`. -/
private def AcceptedCert (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (stmtIn : StmtIn) (langOut : Set StmtOut)
    [DecidablePred (· ∈ langOut)] (tr : FullTranscript pSpec) : Prop :=
  Pr[(· ∈ langOut) |
    OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] = 1

/-- **Layer 2 — the inner fork loop.** Inverting `collectSiblingRuns` (induction on the count `t`):
  from a successful collection of `t` siblings at coordinate `(i, j)` against `avoid`, each sibling
  is `CoordEq j` to the parent, has its fork value outside `avoid`, agrees with the parent before
  round `i`, was accepted, and carries a well-formed (and certainly-accepted) subforest; moreover
  the siblings' fork values are pairwise distinct. `ih_rec` supplies the correctness of the
  subforest recursion `rec` (the outer induction hypothesis). -/
private lemma collectSiblingRuns_spec
    (hImpl : impl.ReplayConsistent)
    (hVer : verifier.DeterminateAcceptance init impl langOut)
    {m' : Fin (n + 1)}
    (rec : FullTranscript pSpec →
      OptionT (OracleComp (oSpec + D.forkOracle StmtOut)) (RunForest D StmtOut m'))
    (ih_rec : ∀ (tr' : FullTranscript pSpec) {ss ss' : σ} {fst : RunForest D StmtOut m'},
      (∃ s₀ s₁, prover.Realizes impl stmtIn witIn tr' s₀ s₁ ∧ impl.Reachable s₁ ss) →
      (some fst, ss') ∈ support
        ((simulateQ (impl.addLift (cwssForkImpl D impl verifier stmtIn witIn prover) :
            QueryImpl (oSpec + D.forkOracle StmtOut) (StateT σ ProbComp))
          ((rec tr').run)).run ss) →
      fst.WellFormed langOut tr' ∧
        (∀ r ∈ fst.runs, AcceptedCert init impl verifier stmtIn langOut r.transcript) ∧
        impl.Reachable ss ss')
    {tr : FullTranscript pSpec} (i : pSpec.ChallengeIdx) (j : Fin (D.coordIndex i)) :
    ∀ (t : ℕ) (avoid : Finset (D.alphabet i)) {s s' : σ}
      {sibs : Fin t → SiblingRun pSpec StmtOut × RunForest D StmtOut m'},
      (∃ s₀ s₁, prover.Realizes impl stmtIn witIn tr s₀ s₁ ∧ impl.Reachable s₁ s) →
      (some sibs, s') ∈ support
        ((simulateQ (impl.addLift (cwssForkImpl D impl verifier stmtIn witIn prover) :
            QueryImpl (oSpec + D.forkOracle StmtOut) (StateT σ ProbComp))
          ((D.collectSiblingRuns langOut rec tr i j t avoid).run)).run s) →
      (∀ k : Fin t,
        CoordinateWise.CoordEq j (D.decompose i (tr.challenges i))
          (D.decompose i ((sibs k).1.transcript.challenges i)) ∧
        D.decompose i ((sibs k).1.transcript.challenges i) j ∉ avoid ∧
        (∀ m'' : Fin n, m'' < i.1 → (sibs k).1.transcript m'' = tr m'') ∧
        (sibs k).1.stmtOut ∈ langOut ∧
        AcceptedCert init impl verifier stmtIn langOut (sibs k).1.transcript ∧
        (sibs k).2.WellFormed langOut (sibs k).1.transcript ∧
        (∀ r ∈ (sibs k).2.runs, AcceptedCert init impl verifier stmtIn langOut r.transcript)) ∧
      (∀ k k' : Fin t, k ≠ k' →
        D.decompose i ((sibs k).1.transcript.challenges i) j ≠
        D.decompose i ((sibs k').1.transcript.challenges i) j) ∧
      impl.Reachable s s' := by
  intro t
  induction t with
  | zero =>
    intro avoid s s' sibs _ h
    simp only [CWSSStructure.collectSiblingRuns, OptionT.run_pure, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun k => k.elim0, fun k => k.elim0, QueryImpl.Reachable.refl _⟩
  | succ t ih =>
    intro avoid s s' sibs hRz h
    simp only [CWSSStructure.collectSiblingRuns, OptionT.run_bind, OptionT.run_monadLift,
      Option.elimM, monadLift_eq_self, simulateQ_bind, simulateQ_map, simulateQ_addLift_fork,
      StateT.run_bind, support_bind, Set.mem_iUnion] at h
    obtain ⟨i_1, hi1mem, hcont⟩ := h
    rw [StateT.run_map, support_map, Set.mem_image] at hi1mem
    obtain ⟨⟨a, st⟩, hfork, rfl⟩ := hi1mem
    simp only [Option.elim] at hcont
    rcases a with _ | r
    · -- the fork returned `none`: the collection would have failed, contradiction
      simp at hcont
    · -- the fork returned `some r`: a successful sibling
      have hcoord := cwssForkImpl_coordEq hfork
      have hpre := cwssForkImpl_prefix_eq hImpl hRz hfork
      obtain ⟨sr1, hRlz, hreach_r⟩ := cwssForkImpl_realizes hfork
      obtain ⟨ssa, ssa', hver⟩ := cwssForkImpl_accepts hfork
      have hreach_fork := cwssForkImpl_reachable hfork
      simp only at hcont
      split at hcont
      · rename_i hguard
        -- invert `forest ← rec r.transcript`
        simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run_bind,
          support_bind, Set.mem_iUnion] at hcont
        obtain ⟨⟨fo, s1⟩, hfomem, hcont2⟩ := hcont
        rcases fo with _ | forest
        · simp at hcont2
        · obtain ⟨hforestWF, hforestRuns, hreach_rec⟩ :=
            ih_rec r.transcript ⟨s, sr1, hRlz, hreach_r⟩ hfomem
          simp only [Option.elim] at hcont2
          -- invert `rest ← collectSiblingRuns t (insert ..)`
          simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run_bind,
            support_bind, Set.mem_iUnion] at hcont2
          obtain ⟨⟨re, s2⟩, hremem, hcont3⟩ := hcont2
          rcases re with _ | rest
          · simp at hcont3
          · have hRz2 : ∃ s₀ s₁, prover.Realizes impl stmtIn witIn tr s₀ s₁ ∧
                impl.Reachable s₁ s1 := by
              obtain ⟨s₀, s₁, hR, hRe⟩ := hRz
              exact ⟨s₀, s₁, hR, reachable_trans hRe (reachable_trans hreach_fork hreach_rec)⟩
            obtain ⟨ihPer, ihDist, hreach_ih⟩ :=
              ih (insert (D.decompose i (r.transcript.challenges i) j) avoid) hRz2 hremem
            simp only [Option.elim, OptionT.run_pure, simulateQ_pure, StateT.run_pure,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hcont3
            obtain ⟨rfl, rfl⟩ := hcont3
            refine ⟨?_, ?_, ?_⟩
            · -- per-sibling well-formedness
              intro k
              refine Fin.cases ?_ (fun k' => ?_) k
              · simp only [Fin.cons_zero]
                exact ⟨hcoord.1, hcoord.2.1, fun m'' hm'' => hpre m'' hm'', hguard,
                  hVer stmtIn r.transcript ⟨ssa, ssa', r.stmtOut, hver, hguard⟩,
                  hforestWF, hforestRuns⟩
              · simp only [Fin.cons_succ]
                obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := ihPer k'
                exact ⟨hc1, fun hmem => hc2 (Finset.mem_insert_of_mem hmem), hc3, hc4, hc5,
                  hc6, hc7⟩
            · -- pairwise distinctness
              intro k k' hkk'
              rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨ka, rfl⟩ <;>
                rcases Fin.eq_zero_or_eq_succ k' with rfl | ⟨kb, rfl⟩
              · exact absurd rfl hkk'
              · simp only [Fin.cons_zero, Fin.cons_succ]
                have := (ihPer kb).2.1
                rw [Finset.mem_insert, not_or] at this
                exact (Ne.symm this.1)
              · simp only [Fin.cons_zero, Fin.cons_succ]
                have := (ihPer ka).2.1
                rw [Finset.mem_insert, not_or] at this
                exact this.1
              · simp only [Fin.cons_succ]
                exact ihDist ka kb (fun heq => hkk' (by rw [heq]))
            · exact reachable_trans hreach_fork (reachable_trans hreach_rec hreach_ih)
      · simp at hcont

/-- **Layer 3 — fan-out over coordinates.** Inverting `gatherFin` (induction on the number of
  coordinates `ℓ`): a successful gather of per-coordinate sibling collections gives, for each
  coordinate, the `collectSiblingRuns_spec` conclusion (reachability threaded across coordinates).
  The reindexing `g` tracks which coordinate each gather slot uses. -/
private lemma gatherFin_spec
    (hImpl : impl.ReplayConsistent)
    (hVer : verifier.DeterminateAcceptance init impl langOut)
    {m' : Fin (n + 1)}
    (rec : FullTranscript pSpec →
      OptionT (OracleComp (oSpec + D.forkOracle StmtOut)) (RunForest D StmtOut m'))
    (ih_rec : ∀ (tr' : FullTranscript pSpec) {ss ss' : σ} {fst : RunForest D StmtOut m'},
      (∃ s₀ s₁, prover.Realizes impl stmtIn witIn tr' s₀ s₁ ∧ impl.Reachable s₁ ss) →
      (some fst, ss') ∈ support
        ((simulateQ (impl.addLift (cwssForkImpl D impl verifier stmtIn witIn prover) :
            QueryImpl (oSpec + D.forkOracle StmtOut) (StateT σ ProbComp))
          ((rec tr').run)).run ss) →
      fst.WellFormed langOut tr' ∧ (∀ r ∈ fst.runs, AcceptedCert init impl verifier stmtIn langOut
        r.transcript) ∧ impl.Reachable ss ss')
    {tr : FullTranscript pSpec} (i : pSpec.ChallengeIdx) (kt : ℕ) :
    ∀ (ℓ : ℕ) (g : Fin ℓ → Fin (D.coordIndex i)) {s s' : σ}
      {sibs : Fin ℓ → (Fin kt → SiblingRun pSpec StmtOut × RunForest D StmtOut m')},
      (∃ s₀ s₁, prover.Realizes impl stmtIn witIn tr s₀ s₁ ∧ impl.Reachable s₁ s) →
      (some sibs, s') ∈ support
        ((simulateQ (impl.addLift (cwssForkImpl D impl verifier stmtIn witIn prover) :
            QueryImpl (oSpec + D.forkOracle StmtOut) (StateT σ ProbComp))
          ((gatherFin ℓ (fun jj => D.collectSiblingRuns langOut rec tr i (g jj) kt ∅)).run)).run
          s) →
      (∀ jj : Fin ℓ,
        (∀ k : Fin kt,
          CoordinateWise.CoordEq (g jj) (D.decompose i (tr.challenges i))
            (D.decompose i ((sibs jj k).1.transcript.challenges i)) ∧
          D.decompose i ((sibs jj k).1.transcript.challenges i) (g jj) ∉
            (∅ : Finset (D.alphabet i)) ∧
          (∀ m'' : Fin n, m'' < i.1 → (sibs jj k).1.transcript m'' = tr m'') ∧
          (sibs jj k).1.stmtOut ∈ langOut ∧
          AcceptedCert init impl verifier stmtIn langOut (sibs jj k).1.transcript ∧
          (sibs jj k).2.WellFormed langOut (sibs jj k).1.transcript ∧
          (∀ r ∈ (sibs jj k).2.runs, AcceptedCert init impl verifier stmtIn langOut r.transcript)) ∧
        (∀ k k' : Fin kt, k ≠ k' →
          D.decompose i ((sibs jj k).1.transcript.challenges i) (g jj) ≠
          D.decompose i ((sibs jj k').1.transcript.challenges i) (g jj))) ∧
      impl.Reachable s s' := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro g s s' sibs _ h
    simp only [gatherFin, OptionT.run_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun jj => jj.elim0, QueryImpl.Reachable.refl _⟩
  | succ ℓ ih =>
    intro g s s' sibs hRz h
    simp only [gatherFin, OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run_bind,
      support_bind, Set.mem_iUnion] at h
    obtain ⟨⟨hd?, s_hd⟩, hhdmem, hcont⟩ := h
    rcases hd? with _ | hd
    · simp at hcont
    · obtain ⟨hdPer, hdDist, hreach_hd⟩ :=
        collectSiblingRuns_spec hImpl hVer rec ih_rec i (g 0) kt ∅ hRz hhdmem
      simp only [Option.elim, OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run_bind,
        support_bind, Set.mem_iUnion] at hcont
      obtain ⟨⟨tl?, s_tl⟩, htlmem, hcont2⟩ := hcont
      rcases tl? with _ | tl
      · simp at hcont2
      · have hRz2 : ∃ s₀ s₁, prover.Realizes impl stmtIn witIn tr s₀ s₁ ∧
            impl.Reachable s₁ s_hd := by
          obtain ⟨s₀, s₁, hR, hRe⟩ := hRz
          exact ⟨s₀, s₁, hR, reachable_trans hRe hreach_hd⟩
        obtain ⟨ihPer, hreach_tl⟩ := ih (fun j => g j.succ) hRz2 htlmem
        simp only [Option.elim, OptionT.run_pure, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hcont2
        obtain ⟨rfl, rfl⟩ := hcont2
        refine ⟨fun jj => ?_, reachable_trans hreach_hd hreach_tl⟩
        refine Fin.cases ?_ (fun jj' => ?_) jj
        · simp only [Fin.cons_zero]; exact ⟨hdPer, hdDist⟩
        · simp only [Fin.cons_succ]; exact ihPer jj'

/-- `collectForest` at the last round is the leaf. -/
private lemma collectForest_last (tr : FullTranscript pSpec) :
    D.collectForest langOut (Fin.last n) tr =
      (pure .leaf : OptionT (OracleComp (oSpec + D.forkOracle StmtOut)) _) := by
  simp only [CWSSStructure.collectForest, Fin.reverseInduction_last]

/-- `collectForest` at a `castSucc` round unfolds to one collection step. -/
private lemma collectForest_castSucc (i : Fin n) (tr : FullTranscript pSpec) :
    D.collectForest langOut i.castSucc tr =
      (match h : pSpec.dir i with
        | .P_to_V => do
          let child ← D.collectForest langOut i.succ tr
          pure (.msgNode i h child)
        | .V_to_P => do
          let center ← D.collectForest langOut i.succ tr
          let sibs ← gatherFin (D.coordIndex ⟨i, h⟩) (fun j =>
            D.collectSiblingRuns langOut (D.collectForest langOut i.succ) tr ⟨i, h⟩ j
              (D.soundnessParam ⟨i, h⟩ - 1) ∅)
          pure (.chalNode i h center (fun j t => (sibs j t).1) (fun j t => (sibs j t).2)) :
        OptionT (OracleComp (oSpec + D.forkOracle StmtOut)) (RunForest D StmtOut i.castSucc)) := by
  simp only [CWSSStructure.collectForest, Fin.reverseInduction_castSucc]

/-- **Layer 4 — the round recursion.** Generalized over the round `m`: any forest collected from a
  realized central transcript `tr` (by `collectForest m`) is well-formed and has every collected
  run accepted with certainty. Proven by `Fin.reverseInduction`, consuming `gatherFin_spec` /
  `collectSiblingRuns_spec` (whose `rec` recursion is this lemma's own induction hypothesis). -/
private lemma aux_wellFormed
    (hImpl : impl.ReplayConsistent)
    (hVer : verifier.DeterminateAcceptance init impl langOut) :
    ∀ {m : Fin (n + 1)} (forest : RunForest D StmtOut m) (tr : FullTranscript pSpec) {s s' : σ},
      (∃ s₀ s₁, prover.Realizes impl stmtIn witIn tr s₀ s₁ ∧ impl.Reachable s₁ s) →
      (some forest, s') ∈ support
        ((simulateQ (impl.addLift (cwssForkImpl D impl verifier stmtIn witIn prover) :
            QueryImpl (oSpec + D.forkOracle StmtOut) (StateT σ ProbComp))
          ((D.collectForest langOut m tr).run)).run s) →
      forest.WellFormed langOut tr ∧
      (∀ r ∈ forest.runs, AcceptedCert init impl verifier stmtIn langOut r.transcript) ∧
      impl.Reachable s s' := by
  intro m
  induction m using Fin.reverseInduction with
  | last =>
    intro forest tr s s' _ h
    rw [collectForest_last] at h
    simp only [OptionT.run_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨trivial, fun r hr => by simp [RunForest.runs] at hr, QueryImpl.Reachable.refl _⟩
  | cast i ih =>
    intro forest tr s s' hRz h
    rw [collectForest_castSucc] at h
    split at h
    · -- message round: nothing collected, recurse into the child
      rename_i hDi
      simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run_bind,
        support_bind, Set.mem_iUnion] at h
      obtain ⟨⟨ch?, s1⟩, hchmem, hcont⟩ := h
      rcases ch? with _ | child
      · simp at hcont
      · obtain ⟨hchWF, hchRuns, hreach_ch⟩ := ih child tr hRz hchmem
        simp only [Option.elim, OptionT.run_pure, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hcont
        obtain ⟨rfl, rfl⟩ := hcont
        exact ⟨hchWF, hchRuns, hreach_ch⟩
    · -- challenge round: collect siblings via gatherFin, recurse into center and subforests
      rename_i hDi
      simp only [OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run_bind,
        support_bind, Set.mem_iUnion] at h
      obtain ⟨⟨ce?, s1⟩, hcemem, hcont⟩ := h
      rcases ce? with _ | center
      · simp at hcont
      · obtain ⟨hceWF, hceRuns, hreach_ce⟩ := ih center tr hRz hcemem
        simp only [Option.elim, OptionT.run_bind, Option.elimM, simulateQ_bind, StateT.run_bind,
          support_bind, Set.mem_iUnion] at hcont
        obtain ⟨⟨sb?, s2⟩, hsbmem, hcont2⟩ := hcont
        rcases sb? with _ | sibs
        · simp at hcont2
        · have hRz2 : ∃ s₀ s₁, prover.Realizes impl stmtIn witIn tr s₀ s₁ ∧
              impl.Reachable s₁ s1 := by
            obtain ⟨s₀, s₁, hR, hRe⟩ := hRz
            exact ⟨s₀, s₁, hR, reachable_trans hRe hreach_ce⟩
          obtain ⟨hsbPer, hreach_sb⟩ :=
            gatherFin_spec hImpl hVer (D.collectForest langOut i.succ)
              (fun tr' {_ _ fst} h1 h2 => ih fst tr' h1 h2) ⟨i, hDi⟩
              (D.soundnessParam ⟨i, hDi⟩ - 1) (D.coordIndex ⟨i, hDi⟩) id hRz2 hsbmem
          simp only [Option.elim, OptionT.run_pure, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hcont2
          obtain ⟨rfl, rfl⟩ := hcont2
          refine ⟨?_, ?_, reachable_trans hreach_ce hreach_sb⟩
          · -- well-formedness of the challenge node
            simp only [RunForest.WellFormed]
            refine ⟨hceWF, fun j t => ?_⟩
            obtain ⟨hPer, hDist⟩ := hsbPer j
            obtain ⟨hc1, _, hc3, hc4, _, hc6, _⟩ := hPer t
            exact ⟨hc1, fun t' ht' => hDist t' t ht', hc3, hc4, hc6⟩
          · -- every run is accepted with certainty
            intro r hr
            simp only [RunForest.runs, List.mem_append, List.mem_flatMap, List.mem_finRange,
              true_and] at hr
            rcases hr with hr | ⟨j, t, hr⟩
            · exact hceRuns r hr
            · rw [List.mem_cons] at hr
              obtain ⟨hPer, _⟩ := hsbPer j
              obtain ⟨_, _, _, _, hc5, _, hc7⟩ := hPer t
              rcases hr with rfl | hr
              · exact hc5
              · exact hc7 r hr

/-- **The (only) monadic correctness lemma of the extraction**: any forest collected against the
  concrete fork-oracle implementation, from a realized central transcript, is well-formed, and
  every collected run's transcript is accepted with certainty.

  *Proof route:* induction over the collection (unfolding `Fin.reverseInduction` and inverting
  the binds of `collectSiblingRuns`/`gatherFin`), consuming the fork-oracle guarantees: clauses
  1–2 of `WellFormed` from `cwssForkImpl_coordEq` (CoordEq and `avoid`-exclusion), clause 3 from
  `cwssForkImpl_prefix_eq` (with realizedness threaded by `cwssForkImpl_realizes`), clause 4 from
  the builder's acceptance check; the certainty of acceptance from `hVer`
  (`DeterminateAcceptance`) applied to each realized accepting sibling. -/
theorem collectForest_wellFormed
    (hImpl : impl.ReplayConsistent)
    (hVer : verifier.DeterminateAcceptance init impl langOut)
    {central : FullTranscript pSpec} {forest : RunForest D StmtOut 0} {s s' : σ}
    (hRealized : ∃ s₀ s₁, prover.Realizes impl stmtIn witIn central s₀ s₁ ∧
      impl.Reachable s₁ s)
    (h : (some forest, s') ∈ support
      ((simulateQ
        (impl.addLift (cwssForkImpl D impl verifier stmtIn witIn prover) :
          QueryImpl (oSpec + D.forkOracle StmtOut) (StateT σ ProbComp))
        ((D.collectForest langOut 0 central).run)).run s)) :
    forest.WellFormed langOut central ∧
    ∀ r ∈ forest.runs,
      Pr[ (· ∈ langOut) |
        OptionT.mk do (simulateQ impl (verifier.run stmtIn r.transcript)).run' (← init)] = 1 := by
  obtain ⟨hwf, hruns, _⟩ := aux_wellFormed hImpl hVer forest central hRealized h
  exact ⟨hwf, hruns⟩
-/

end CWSSStructure

/-! ## The implication -/

namespace Verifier

open CWSSStructure

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/- DEPRECATED (single-shot forking route) — superseded by the seeded-replay architecture.
  This is the implication via the single-shot `rewindingExtractor`/`collectForest` and the
  non-linear `forkBound`. The seeded route replaces it with an implication concluding
  `knowledgeSoundnessRewindingWithError … D.knowledgeError` via the seeded value-indexed
  exhaustive extractor. Commented out (not deleted) for reference.

/-- **Coordinate-wise special soundness implies rewinding knowledge soundness**, with the
  forking-style extraction bound `CWSSStructure.forkBound` (the bounded-extractor counterpart of
  [FMN24] Lemma 2.31; see the module docstring).

  The witness extractor is `CWSSStructure.rewindingExtractor`: it forks the measured run via the
  CWSS fork oracle into a run forest (`collectForest_wellFormed`), whose pure assembly is a
  `D`-structured tree of accepting transcripts (`RunForest.WellFormed.toTree_isStructured`,
  `RunForest.WellFormed.mem_toTree_fullTranscripts`), and applies the `TreeBased` extractor
  supplied by `coordinateWiseSpecialSound`. The hypotheses `hImpl` and `hVer` are the bridging
  assumptions of the realized-vs-certain acceptance gap (see `Rewinding`);
  both are trivial for an empty `oSpec` and a deterministic verifier. -/
theorem coordinateWiseSpecialSound_implies_knowledgeSoundnessRewinding
    (D : CWSSStructure pSpec) [∀ i, Fintype (D.alphabet i)] [∀ i, SampleableType (D.alphabet i)]
    [∀ i, DecidableEq (D.alphabet i)]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (hImpl : impl.ReplayConsistent)
    (hVer : verifier.DeterminateAcceptance init impl relOut.language) :
    verifier.coordinateWiseSpecialSound init impl D relIn relOut.language →
      verifier.knowledgeSoundnessRewinding init impl (D.forkOracle StmtOut)
        (cwssForkImpl D impl verifier) relIn relOut D.forkBound := by
  sorry
-/

end Verifier
