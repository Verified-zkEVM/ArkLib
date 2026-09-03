/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.Basic

/-!
  # Sequential Composition: Extractors and State Functions

  Composition of straightline and round-by-round extractors (`Extractor.Straightline.append`,
  `Extractor.RoundByRound.append`), and of verifier state functions
  (`Verifier.StateFunction.append`), for two sequentially composed reductions.

  Past the seam the composed state function is scored *disjunctively*: the composite is winning if
  the adversary already won the first half, or is winning the second. See
  `Verifier.StateFunction.append` for why.
-/

open OracleComp OracleSpec SubSpec

universe u v

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-! Sequential composition of extractors and state functions

These have the following form: they needs to know the first verifier, and derive the intermediate
statement from running the first verifier on the first statement.

This leads to complications: the verifier is assumed to be a general `OracleComp oSpec`, and so
we also need to have the extractors and state functions to be similarly `OracleComp`s.

The alternative is to consider a fully deterministic (and non-failing) verifier. The non-failing
part is somewhat problematic as we write our verifiers to be able to fail (i.e. implicit failing
via `guard` statements).

As such, the definitions below are temporary until further development. -/

namespace Extractor

/-- The sequential composition of two straightline extractors.

TODO: state a monotone condition on the extractor, namely that if extraction succeeds on a given
query log, then it also succeeds on any extension of that query log -/
def Straightline.append (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) :
      Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) :=
  fun stmt₁ wit₃ transcript proveQueryLog verifyQueryLog => do
    let stmt₂ ← V₁.verify stmt₁ transcript.fst
    let wit₂ ← E₂ stmt₂ wit₃ transcript.snd proveQueryLog verifyQueryLog
    let wit₁ ← E₁ stmt₁ wit₂ transcript.fst proveQueryLog verifyQueryLog
    return wit₁

/-- The composed round-by-round witness motive of `Extractor.RoundByRound.append`, evaluated at an
index lying in the first protocol's range, is the first extractor's witness type. -/
private lemma witMid_append_left {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (i : Fin (m + n + 1)) (j : Fin (m + 1)) (hij : i.val = j.val) :
    (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) i = WitMid₁ j := by
  have hcast : Fin.cast (show m + n + 1 = m + 1 + n by omega) i = Fin.castAdd n j := by
    ext; simpa using hij
  simp only [Function.comp_apply, hcast, Fin.append_left]

/-- The composed round-by-round witness motive of `Extractor.RoundByRound.append`, evaluated at an
index lying in the second protocol's range, is the second extractor's witness type. -/
private lemma witMid_append_right {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (i : Fin (m + n + 1)) (j : Fin (n + 1)) (hij : i.val = m + j.val) (hj : 0 < j.val) :
    (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) i = WitMid₂ j := by
  have hjn := j.isLt
  have hcast : Fin.cast (show m + n + 1 = m + 1 + n by omega) i
      = Fin.natAdd (m + 1) ⟨j.val - 1, by omega⟩ := by
    ext; simp; omega
  rw [Function.comp_apply, hcast, Fin.append_right]
  change Fin.tail WitMid₂ _ = _
  unfold Fin.tail
  congr 1
  ext; simp; omega

/-- The round-by-round extractor for the sequential composition of two (oracle) reductions.

`verify` is the first verifier's *deterministic* next-statement function. It is needed because the
second extractor `E₂` runs on the intermediate statement `Stmt₂`, and an appended extractor is only
handed the *initial* statement `Stmt₁`: without `verify` there is no way to produce the `Stmt₂`
that every call into `E₂` requires, and the definition cannot be written at all.

This mirrors `Extractor.Straightline.append`, which takes the first verifier for the same reason,
and `Verifier.StateFunction.append`, which takes this same deterministic `verify` function. A plain
`Verifier` cannot be used here: `Verifier.verify` returns an `OptionT (OracleComp oSpec) Stmt₂`,
whereas `extractMid` and `extractOut` are pure functions and so cannot run an oracle computation. -/
def RoundByRound.append
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) :
      Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂)
        (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) where
  eqIn := by
    simp only [Fin.append, Function.comp_apply, Fin.addCases, Fin.cast_zero,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, lt_add_iff_pos_left,
      Order.lt_add_one_iff, zero_le, ↓reduceDIte, Fin.castLT, Fin.zero_eta]
    exact E₁.eqIn
  extractMid := fun idx stmt₁ tr h => by
    have hidx := idx.isLt
    -- Re-expose the transcript with a transparent round bound, so that `omega` can discharge
    -- the index side conditions below.
    have tr' : (i : Fin (idx.val + 1)) →
        (pSpec₁ ++ₚ pSpec₂).«Type» ⟨i.val, by have := i.isLt; omega⟩ := tr
    by_cases hlt : idx.val < m
    · exact cast (witMid_append_left (WitMid₂ := WitMid₂) idx.castSucc ⟨idx.val, by omega⟩ rfl).symm
        (E₁.extractMid ⟨idx.val, hlt⟩ stmt₁
          (show pSpec₁.Transcript ⟨idx.val + 1, by omega⟩ from fun i =>
            cast (ProtocolSpec.append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
              ⟨i.val, by have := i.isLt; omega⟩) (tr' ⟨i.val, by have := i.isLt; omega⟩))
          (cast (witMid_append_left (WitMid₂ := WitMid₂) idx.succ ⟨idx.val + 1, by omega⟩ rfl) h))
    · have hm : m ≤ idx.val := by omega
      have tr₁ : pSpec₁.FullTranscript := fun i =>
        cast (ProtocolSpec.append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i)
          (tr' ⟨i.val, by have := i.isLt; omega⟩)
      by_cases heq : idx.val = m
      · have hn : 0 < n := by omega
        exact cast (witMid_append_left (WitMid₂ := WitMid₂) idx.castSucc (Fin.last m)
            (by simp [heq])).symm
          (E₁.extractOut stmt₁ tr₁
            (cast (show WitMid₂ (⟨0, hn⟩ : Fin n).castSucc = Wit₂ by
                rw [show ((⟨0, hn⟩ : Fin n).castSucc) = 0 from by ext; simp]; exact E₂.eqIn)
              (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ tr₁)
                (show pSpec₂.Transcript ⟨1, by omega⟩ from fun i =>
                  cast (ProtocolSpec.append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                    ⟨i.val, by have : i.val < 1 := i.isLt; omega⟩)
                    (tr' ⟨m + i.val, by have : i.val < 1 := i.isLt; omega⟩))
                (cast (witMid_append_right (WitMid₁ := WitMid₁) idx.succ (⟨0, hn⟩ : Fin n).succ
                  (by simp [heq]) (by simp)) h))))
      · have hk : idx.val - m < n := by omega
        exact cast (witMid_append_right (WitMid₁ := WitMid₁) idx.castSucc
            (⟨idx.val - m, hk⟩ : Fin n).castSucc (by simp; omega) (by simp; omega)).symm
          (E₂.extractMid ⟨idx.val - m, hk⟩ (verify stmt₁ tr₁)
            (show pSpec₂.Transcript ⟨idx.val - m + 1, by omega⟩ from fun i =>
              cast (ProtocolSpec.append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                ⟨i.val, by have : i.val < idx.val - m + 1 := i.isLt; omega⟩)
                (tr' ⟨m + i.val, by have : i.val < idx.val - m + 1 := i.isLt; omega⟩))
            (cast (witMid_append_right (WitMid₁ := WitMid₁) idx.succ
              (⟨idx.val - m, hk⟩ : Fin n).succ (by simp; omega) (by simp)) h))
  extractOut := fun stmt₁ tr wit₃ => by
    by_cases hn : 0 < n
    · exact cast (witMid_append_right (WitMid₁ := WitMid₁) (Fin.last (m + n)) (Fin.last n)
          (by simp) (by simpa using hn)).symm
        (E₂.extractOut (verify stmt₁ tr.fst) tr.snd wit₃)
    · exact cast (witMid_append_left (WitMid₂ := WitMid₂) (Fin.last (m + n)) (Fin.last m)
          (by simp; omega)).symm
        (E₁.extractOut stmt₁ tr.fst
          (cast (show WitMid₂ (Fin.last n) = Wit₂ by
              rw [show (Fin.last n) = 0 from by ext; simp; omega]; exact E₂.eqIn)
            (E₂.extractOut (verify stmt₁ tr.fst) tr.snd wit₃)))

end Extractor

section StateFunctionAppend

/-! ### Helpers for `Verifier.StateFunction.append`

These are index-bookkeeping lemmas for partial transcripts of an appended protocol. They are all
stated with `HEq` because the round indices involved (`min k m`, `k - m`, ...) are only
*propositionally* equal to the ones appearing in the goals. -/

/-- Transporting along a type equality is the identity up to `HEq`. Used to peel off the
coercions that `Verifier.StateFunction.append`'s `toFun` inserts when it re-indexes a partial
transcript. -/
private lemma heq_eqMp {α β : Sort u} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
  rw [eq_mp_eq_cast]; exact cast_heq _ _

/-- Extensionality for partial transcripts sitting at propositionally equal round indices. -/
private lemma transcript_heq_ext {N : ℕ} {pSpec : ProtocolSpec N} {k k' : Fin (N + 1)}
    {T : pSpec.Transcript k} {T' : pSpec.Transcript k'} (hk : k.val = k'.val)
    (h : ∀ (i : ℕ) (hi : i < k.val) (hi' : i < k'.val), HEq (T ⟨i, hi⟩) (T' ⟨i, hi'⟩)) :
    HEq T T' := by
  obtain rfl : k = k' := Fin.ext hk
  exact heq_of_eq (funext fun i => eq_of_heq (h i.val i.isLt i.isLt))

/-- Pointwise computation rule for `Transcript.fst`. -/
private lemma transcript_fst_apply {k : Fin (m + n + 1)}
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (i : ℕ) (hi : i < min k.val m) (hi' : i < k.val) :
    HEq (T.fst ⟨i, hi⟩) (T ⟨i, hi'⟩) := cast_heq _ _

/-- Pointwise computation rule for `Transcript.snd`. -/
private lemma transcript_snd_apply {k : Fin (m + n + 1)}
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (i : ℕ) (hi : i < k.val - m) (hi' : m + i < k.val) :
    HEq (T.snd ⟨i, hi⟩) (T ⟨m + i, hi'⟩) := cast_heq _ _

/-- Below the last round, `Transcript.concat` agrees with the transcript it extends. -/
private lemma transcript_concat_apply_lt {N : ℕ} {pSpec : ProtocolSpec N} {k : Fin N}
    (T : pSpec.Transcript k.castSucc) (msg : pSpec.«Type» k) (i : ℕ) (hi : i < k.val)
    (hi' : i < (k.succ : Fin (N + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) (T ⟨i, hi⟩) := by
  unfold Transcript.concat Fin.snoc
  rw [dif_pos hi]
  exact cast_heq _ _

/-- At the last round, `Transcript.concat` returns the newly appended message. -/
private lemma transcript_concat_apply_last {N : ℕ} {pSpec : ProtocolSpec N} {k : Fin N}
    (T : pSpec.Transcript k.castSucc) (msg : pSpec.«Type» k) (i : ℕ) (hik : i = k.val)
    (hi' : i < (k.succ : Fin (N + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) msg := by
  subst hik
  unfold Transcript.concat Fin.snoc
  rw [dif_neg (Nat.lt_irrefl k.val)]
  exact cast_heq _ _

/-- A state function's value only depends on the round index, statement, and transcript up to
(heterogeneous) equality. -/
private lemma stateFunction_toFun_heq {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    {N : ℕ} {pSpec : ProtocolSpec N} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {langIn : Set StmtIn} {langOut : Set StmtOut}
    {V : Verifier oSpec StmtIn StmtOut pSpec} (S : V.StateFunction init impl langIn langOut)
    {k k' : Fin (N + 1)} (hk : k = k') {stmt stmt' : StmtIn} (hstmt : stmt = stmt')
    {T : pSpec.Transcript k} {T' : pSpec.Transcript k'} (h : HEq T T')
    (hS : S.toFun k stmt T) : S.toFun k' stmt' T' := by
  subst hk
  subst hstmt
  obtain rfl := eq_of_heq h
  exact hS

/-- Pointwise computation rule for `FullTranscript.fst`. -/
private lemma fullTranscript_fst_apply (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (i : Fin m) :
    HEq (FullTranscript.fst T i) (T (Fin.castAdd n i)) := by
  unfold FullTranscript.fst; exact cast_heq _ _

/-- Pointwise computation rule for `FullTranscript.snd`. -/
private lemma fullTranscript_snd_apply (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (i : Fin n) :
    HEq (FullTranscript.snd T i) (T (Fin.natAdd m i)) := by
  unfold FullTranscript.snd; exact cast_heq _ _

/-- At the last round, the partial projection `Transcript.fst` is the full projection
`FullTranscript.fst`, up to the index rewriting `min (m + n) m = m`. -/
private lemma transcript_fst_eq_full (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (fun i : Fin m => (Transcript.fst (k := Fin.last (m + n)) T)
      ⟨i.val, by have := i.isLt; change i.val < min (m + n) m; omega⟩) =
      FullTranscript.fst T := by
  funext i
  have hi := i.isLt
  exact eq_of_heq ((transcript_fst_apply (k := Fin.last (m + n)) T i.val
    (show i.val < min (m + n) m by omega) (show i.val < m + n by omega)).trans
      (fullTranscript_fst_apply T i).symm)

/-- Heterogeneous form of `transcript_fst_eq_full`. -/
private lemma transcript_fst_heq_full (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    HEq (Transcript.fst (k := Fin.last (m + n)) T) (FullTranscript.fst T) := by
  refine transcript_heq_ext (k := ⟨min (m + n) m, by omega⟩) (k' := Fin.last m)
    (show min (m + n) m = m by omega) ?_
  intro i hi hi'
  exact (transcript_fst_apply (k := Fin.last (m + n)) T i hi (show i < m + n by omega)).trans
    (fullTranscript_fst_apply T ⟨i, hi'⟩).symm

/-- At the last round, the partial projection `Transcript.snd` is the full projection
`FullTranscript.snd`, up to the index rewriting `(m + n) - m = n`. -/
private lemma transcript_snd_heq_full (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    HEq (Transcript.snd (k := Fin.last (m + n)) T) (FullTranscript.snd T) := by
  refine transcript_heq_ext (k := ⟨(m + n) - m, by omega⟩) (k' := Fin.last n)
    (show (m + n) - m = n by omega) ?_
  intro i hi hi'
  exact (transcript_snd_apply (k := Fin.last (m + n)) T i (show i < (m + n) - m by omega)
    (show m + i < m + n by omega)).trans (fullTranscript_snd_apply T ⟨i, hi'⟩).symm

/-- If the first verifier is deterministic (`hVerify`), running the appended verifier is the same
as running the second verifier on the second half of the transcript, started from the first
verifier's output on the first half. -/
private lemma append_run_of_deterministic
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
    {verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂}
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (V₁.append V₂).run stmt tr = V₂.run (verify stmt tr.fst) tr.snd := by
  subst hVerify
  simp [Verifier.run, Verifier.append]

/-- The output of a deterministic verifier is reachable as soon as the initial-state computation
`init` can succeed. -/
private lemma mem_support_of_pure_run {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {x : Stmt₂} {s : σ} (hs : s ∈ support init) :
    x ∈ support (OptionT.mk do
      (simulateQ impl (pure x : OptionT (OracleComp oSpec) Stmt₂)).run' (← init)) := by
  rw [OptionT.mem_support_iff]
  simp only [OptionT.run_mk, StateT.run'_eq, mem_support_bind_iff]
  refine ⟨s, hs, ?_⟩
  change some x ∈ support ((fun p => p.1) <$> (pure (some x, s) : ProbComp (Option Stmt₂ × σ)))
  simp

/-- Every `ProbComp` has at least one possible outcome: `OracleComp` is a free monad with no
failure constructor, and every `unifSpec` query has an answer. (A general fact about `ProbComp`,
kept here only because it has no other home yet.) -/
private lemma probComp_support_nonempty {σ : Type} (init : ProbComp σ) :
    (support init).Nonempty := by
  induction init using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih =>
    obtain ⟨u⟩ : Nonempty (unifSpec.Range t) := by infer_instance
    obtain ⟨x, hx⟩ := ih u
    exact ⟨x, by simp only [support_bind, support_query, Set.mem_iUnion]; exact ⟨u, trivial, hx⟩⟩

/-- A deterministic verifier's run is a `pure` computation. -/
private lemma run_of_deterministic
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂}
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) :
    V₁.run stmt tr = (pure (verify stmt tr) : OptionT (OracleComp oSpec) Stmt₂) := by
  subst hVerify; rfl

/-- If a deterministic first verifier's state function rejects the completed first-half transcript,
then the statement it hands to the second verifier lies outside the intermediate language.

This step needs `init` to have at least one possible outcome, since a `StateFunction`'s
`toFun_full` field only constrains a *probability*. That is automatic for `ProbComp`
(`probComp_support_nonempty`), so no side condition is needed. -/
private lemma verify_notMem_of_not_toFun {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂}
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂}
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) (h : ¬ S₁.toFun (Fin.last m) stmt tr) :
    verify stmt tr ∉ lang₂ := by
  obtain ⟨s, hs⟩ := probComp_support_nonempty init
  have h₁ := S₁.toFun_full stmt tr h
  rw [run_of_deterministic hVerify, probEvent_eq_zero_iff] at h₁
  exact h₁ _ (mem_support_of_pure_run hs)

end StateFunctionAppend

namespace Verifier

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- The sequential composition of two state functions.

Rounds `0, …, m` of the appended protocol are scored by `S₁`, and rounds `m+1, …, m+n` are scored
by `S₂`, started at the statement `verify` produces from the first half of the transcript. In
particular the second half is scored by `S₂` **alone**: the first half's verdict is not carried
along as a conjunct.

The reason is that the *only* thing a `StateFunction` promises about a "bad" state is
`toFun_full`, and at a full transcript of the appended protocol it is `V₂` that produces the
output statement. Conjoining `S₁` would let the composite be bad on account of its first half
while `S₂` — the half that actually decides — is good and `V₂` accepts, contradicting
`toFun_full`. Handing the verdict to whichever half owns the last round is what makes the
composite honest.

The hand-off at round `m` uses `hVerify`: `V₁` is deterministic, so there is a single
intermediate statement `verify stmt tr₁` to start `S₂` from, and `S₁` rejecting the first half
forces that statement out of `lang₂`. -/
def StateFunction.append
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    -- Assume the first verifier is deterministic for now
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) :
      (V₁.append V₂).StateFunction init impl lang₁ lang₃ where
  toFun := fun roundIdx stmt₁ transcript =>
    if h : roundIdx.val ≤ m then
    -- If the round index falls in the first protocol, then we simply invokes the first state fn
      S₁ ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst)
    else
    -- If the round index falls in the second protocol, then the composite is winning if the
    -- first half was already won (`S₁` on the completed first transcript), or if the second
    -- state fn is winning on the remaining transcript, started from `verify`'s output.
      have hm : min roundIdx.val m = m := min_eq_right_of_lt (by omega)
      let transcript₁ : pSpec₁.FullTranscript := fun i => transcript.fst ⟨i, by simp [hm]⟩
      S₁ ⟨m, by omega⟩ stmt₁ transcript₁ ∨
      S₂ ⟨roundIdx - m, by omega⟩ (verify stmt₁ transcript₁)
        (by simpa [h] using transcript.snd)
  toFun_empty := by
    intro stmt
    split
    · constructor <;> intro h
      · have h' := (S₁.toFun_empty stmt).mp h
        convert h' using 2
        · rfl
        · apply heq_of_eq
          funext i
          exact Fin.elim0 i
      · exact (S₁.toFun_empty stmt).mpr
          (by
            convert h using 2
            · rfl
            · apply heq_of_eq
              funext i
              exact Fin.elim0 i)
    · exact absurd (Nat.zero_le m) ‹_›
  toFun_next := by
    intro j hDir stmt tr hnot msg
    have hj := j.isLt
    have hcs : ((j.castSucc : Fin (m + n + 1)) : ℕ) = j.val := rfl
    have hsc : ((j.succ : Fin (m + n + 1)) : ℕ) = j.val + 1 := rfl
    rcases lt_trichotomy j.val m with hlt | heq | hgt
    · -- Case 1: the new round lies strictly inside the first protocol, so both sides of the
      -- implication take the `then` branch and we may appeal to `S₁.toFun_next`.
      have hDir' : Fin.vappend pSpec₁.dir pSpec₂.dir j = Direction.P_to_V := hDir
      rw [Fin.vappend_left_of_lt _ _ j hlt] at hDir'
      have htype : (pSpec₁ ++ₚ pSpec₂).«Type» j = pSpec₁.«Type» ⟨j.val, hlt⟩ := by
        have h0 : (pSpec₁ ++ₚ pSpec₂).«Type» j = Fin.vappend pSpec₁.«Type» pSpec₂.«Type» j := rfl
        rw [h0, Fin.vappend_left_of_lt _ _ j hlt]
      let T₁ : pSpec₁.Transcript ⟨j.val, by omega⟩ := fun i =>
        cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
          ⟨i.val, by have hi : i.val < j.val := i.isLt; omega⟩)
          (tr ⟨i.val, by have hi : i.val < j.val := i.isLt; omega⟩)
      have hnot₁ : ¬ S₁.toFun ⟨j.val, by omega⟩ stmt T₁ := by
        intro hc
        apply hnot
        rw [dif_pos (show ((j.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)]
        refine stateFunction_toFun_heq S₁
          (Fin.ext (show j.val = ((j.castSucc : Fin (m + n + 1)) : ℕ) by omega)) rfl ?_ hc
        refine HEq.trans ?_ (heq_eqMp _ _).symm
        exact transcript_heq_ext (k := ⟨j.val, by omega⟩)
          (k' := ⟨min ((j.castSucc : Fin (m + n + 1)) : ℕ) m, by omega⟩)
          (show j.val = min ((j.castSucc : Fin (m + n + 1)) : ℕ) m by omega)
          (fun i hi hi' => HEq.rfl)
      have key := S₁.toFun_next ⟨j.val, hlt⟩ hDir' stmt T₁ hnot₁ (cast htype msg)
      intro hgoal
      rw [dif_pos (show ((j.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hgoal
      refine key ?_
      convert hgoal using 2
      · rfl
      refine eq_of_heq (HEq.symm ((heq_eqMp _ _).trans (transcript_heq_ext
        (show min ((j.succ : Fin (m + n + 1)) : ℕ) m = j.val + 1 by omega) ?_)))
      intro i hi hi'
      have hi'' : i < j.val + 1 := hi'
      rcases Nat.lt_or_ge i j.val with hij | hij
      · exact ((transcript_fst_apply _ i hi hi').trans
          (transcript_concat_apply_lt tr msg i hij hi')).trans
            ((transcript_concat_apply_lt T₁ (cast htype msg) i hij hi').trans (cast_heq _ _)).symm
      · obtain rfl : i = j.val := le_antisymm (by omega) hij
        exact ((transcript_fst_apply _ j.val hi hi').trans
          (transcript_concat_apply_last tr msg j.val rfl hi')).trans
            ((transcript_concat_apply_last T₁ (cast htype msg) j.val rfl hi').trans
              (cast_heq _ _)).symm
    · -- Case 2: the boundary round `j.val = m`. The hypothesis is the `then` branch (`S₁` at its
      -- last round) and the goal is the `else` branch (`S₂` at its round `1`). The appended
      -- protocol's direction at index `m` *is* `pSpec₂.dir 0`, so this is `S₂.toFun_next` at
      -- round `0`; its hypothesis `¬ S₂.toFun 0 _ default` is `S₂.toFun_empty` applied to
      -- `verify stmt _ ∉ lang₂`, which `S₁`'s rejection yields via determinism of `V₁`.
      have hn : 0 < n := by omega
      have hzm : (⟨j.val - m, by omega⟩ : Fin n) = ⟨0, hn⟩ :=
        Fin.ext (show j.val - m = 0 by omega)
      have hDir₂ : pSpec₂.dir ⟨0, hn⟩ = Direction.P_to_V := by
        have hDir' : Fin.vappend pSpec₁.dir pSpec₂.dir j = Direction.P_to_V := hDir
        rw [Fin.vappend_right_of_not_lt _ _ j (by omega)] at hDir'
        rwa [hzm] at hDir'
      have htype₂ : (pSpec₁ ++ₚ pSpec₂).«Type» j = pSpec₂.«Type» ⟨0, hn⟩ := by
        have h0 : (pSpec₁ ++ₚ pSpec₂).«Type» j = Fin.vappend pSpec₁.«Type» pSpec₂.«Type» j := rfl
        rw [h0, Fin.vappend_right_of_not_lt _ _ j (by omega), hzm]
      -- The first protocol's half of the transcript is unchanged by the new message.
      have hTr : ∀ (i : Fin m) (h1 : i.val < min ((j.succ : Fin (m + n + 1)) : ℕ) m)
          (h2 : i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m),
          HEq ((Transcript.concat msg tr).fst ⟨i.val, h1⟩) (tr.fst ⟨i.val, h2⟩) := by
        intro i h1 h2
        exact ((transcript_fst_apply _ i.val h1 (by omega)).trans
          (transcript_concat_apply_lt tr msg i.val (by omega) (by omega))).trans
            (transcript_fst_apply tr i.val h2 (by omega)).symm
      rw [dif_pos (show ((j.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hnot
      -- `S₁` rejects the completed first half.  This is the shared ingredient: it rules out the
      -- new `S₁` disjunct, and through `verify_notMem_of_not_toFun` it starts `S₂` off false.
      have hS₁ : ¬ S₁.toFun ⟨m, by omega⟩ stmt
          (fun i => tr.fst ⟨i.val,
            show i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m by
              have := i.isLt; omega⟩) := by
        intro hc₁
        refine hnot (stateFunction_toFun_heq S₁
          (Fin.ext (show m = ((j.castSucc : Fin (m + n + 1)) : ℕ) by omega)) rfl ?_ hc₁)
        refine HEq.trans ?_ (heq_eqMp _ _).symm
        exact transcript_heq_ext (k := ⟨m, by omega⟩)
          (k' := ⟨min ((j.castSucc : Fin (m + n + 1)) : ℕ) m, by omega⟩)
          (show m = min ((j.castSucc : Fin (m + n + 1)) : ℕ) m by omega)
          (fun i hi hi' => HEq.rfl)
      intro hgoal
      rw [dif_neg (show ¬ ((j.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hgoal
      -- The `S₁` disjunct is impossible: a message at round `m` leaves the first half unchanged.
      replace hgoal := hgoal.resolve_left (fun hc => hS₁ (stateFunction_toFun_heq S₁ rfl rfl
        (heq_of_eq (funext fun i => eq_of_heq (hTr i _ _))) hc))
      -- `S₁` rejects the completed first half, so `V₁`'s output misses `lang₂`, so `S₂` is false
      -- at its round `0` on that output.
      have h0 : ¬ S₂.toFun (⟨0, hn⟩ : Fin n).castSucc
          (verify stmt fun i => tr.fst ⟨i.val,
            show i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m by have := i.isLt; omega⟩)
          (fun i => Fin.elim0 i) := by
        intro hc
        exact verify_notMem_of_not_toFun S₁ hVerify stmt _ hS₁
          ((S₂.toFun_empty _).mpr (stateFunction_toFun_heq S₂ (Fin.ext (by simp)) rfl
            (heq_of_eq (funext fun i => Fin.elim0 i)) hc))
      -- The second protocol's half of the new transcript is exactly its single new message.
      have hSnd : HEq ((Transcript.concat msg tr).snd)
          (Transcript.concat (cast htype₂ msg) (fun i => Fin.elim0 i)) := by
        refine transcript_heq_ext (k := ⟨((j.succ : Fin (m + n + 1)) : ℕ) - m, by omega⟩)
          (k' := (⟨0, hn⟩ : Fin n).succ)
          (show ((j.succ : Fin (m + n + 1)) : ℕ) - m = 0 + 1 by omega) ?_
        intro i hi hi'
        obtain rfl : i = 0 := by have : i < 0 + 1 := hi'; omega
        exact ((transcript_snd_apply (Transcript.concat msg tr) 0 hi (by omega)).trans
          (transcript_concat_apply_last tr msg (m + 0) (by omega) (by omega))).trans
            ((transcript_concat_apply_last _ (cast htype₂ msg) 0 rfl hi').trans
              (cast_heq _ _)).symm
      refine S₂.toFun_next ⟨0, hn⟩ hDir₂ _ _ h0 (cast htype₂ msg)
        (stateFunction_toFun_heq S₂
          (Fin.ext (show ((j.succ : Fin (m + n + 1)) : ℕ) - m = 0 + 1 by omega))
          ?_ hSnd hgoal)
      exact congrArg (verify stmt) (funext fun i => eq_of_heq (hTr i _ _))
    · -- Case 3: the new round lies strictly inside the second protocol, so both sides take the
      -- `else` branch. The `S₁` disjunct carries over verbatim and the `S₂` disjunct is the
      -- contrapositive of `S₂.toFun_next` at round `⟨j.val - m, _⟩`.
      have hkn : j.val - m < n := by omega
      have hDir₂ : pSpec₂.dir ⟨j.val - m, hkn⟩ = Direction.P_to_V := by
        have hDir' : Fin.vappend pSpec₁.dir pSpec₂.dir j = Direction.P_to_V := hDir
        rw [Fin.vappend_right_of_not_lt _ _ j (by omega)] at hDir'
        exact hDir'
      have htype₂ : (pSpec₁ ++ₚ pSpec₂).«Type» j = pSpec₂.«Type» ⟨j.val - m, hkn⟩ := by
        have h0 : (pSpec₁ ++ₚ pSpec₂).«Type» j = Fin.vappend pSpec₁.«Type» pSpec₂.«Type» j := rfl
        rw [h0, Fin.vappend_right_of_not_lt _ _ j (by omega)]
      -- The first protocol's half of the transcript is unchanged by the new message.
      have hTr : ∀ (i : Fin m) (h1 : i.val < min ((j.succ : Fin (m + n + 1)) : ℕ) m)
          (h2 : i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m),
          HEq ((Transcript.concat msg tr).fst ⟨i.val, h1⟩) (tr.fst ⟨i.val, h2⟩) := by
        intro i h1 h2
        exact ((transcript_fst_apply _ i.val h1 (by omega)).trans
          (transcript_concat_apply_lt tr msg i.val (by omega) (by omega))).trans
            (transcript_fst_apply tr i.val h2 (by omega)).symm
      rw [dif_neg (show ¬ ((j.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hnot
      intro hgoal
      rw [dif_neg (show ¬ ((j.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hgoal
      -- The `S₁` disjunct carries over verbatim, so it cannot be the one that just became true.
      replace hgoal := hgoal.resolve_left (fun hc => hnot (Or.inl
        (stateFunction_toFun_heq S₁ rfl rfl
          (heq_of_eq (funext fun i => eq_of_heq (hTr i _ _))) hc)))
      -- The second protocol's half gains exactly the new message at its last position.
      have hSnd : HEq ((Transcript.concat msg tr).snd)
          (Transcript.concat (cast htype₂ msg) tr.snd) := by
        refine transcript_heq_ext (k := ⟨((j.succ : Fin (m + n + 1)) : ℕ) - m, by omega⟩)
          (k' := (⟨j.val - m, hkn⟩ : Fin n).succ) ?_ ?_
        · change ((j.succ : Fin (m + n + 1)) : ℕ) - m = j.val - m + 1
          omega
        intro i hi hi'
        have hi2 : i < j.val - m + 1 := hi'
        rcases Nat.lt_or_ge i (j.val - m) with hij | hij
        · exact ((transcript_snd_apply (Transcript.concat msg tr) i hi (by omega)).trans
            (transcript_concat_apply_lt tr msg (m + i) (by omega) (by omega))).trans
              ((transcript_concat_apply_lt tr.snd (cast htype₂ msg) i hij hi').trans
                (transcript_snd_apply tr i hij (by omega))).symm
        · exact ((transcript_snd_apply (Transcript.concat msg tr) i hi (by omega)).trans
            (transcript_concat_apply_last tr msg (m + i) (by omega) (by omega))).trans
              ((transcript_concat_apply_last tr.snd (cast htype₂ msg) i
                (by change i = j.val - m; omega) hi').trans (cast_heq _ _)).symm
      have hnot₂ : ¬ S₂.toFun (⟨j.val - m, hkn⟩ : Fin n).castSucc
          (verify stmt fun i => tr.fst ⟨i.val,
            show i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m by have := i.isLt; omega⟩)
          tr.snd := by
        intro hc
        refine hnot (Or.inr (stateFunction_toFun_heq S₂
          (Fin.ext (show j.val - m = ((j.castSucc : Fin (m + n + 1)) : ℕ) - m by omega))
          rfl ?_ hc))
        exact HEq.rfl
      refine absurd (stateFunction_toFun_heq S₂
        (Fin.ext (show ((j.succ : Fin (m + n + 1)) : ℕ) - m = j.val - m + 1 by omega))
        (congrArg (verify stmt) (funext fun i => eq_of_heq (hTr i _ _))) hSnd hgoal)
        (S₂.toFun_next ⟨j.val - m, hkn⟩ hDir₂ _ _ hnot₂ (cast htype₂ msg))
  toFun_full := by
    intro stmt tr hnot
    rw [append_run_of_deterministic hVerify stmt tr]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `pSpec₂` is empty, so the appended protocol's last round is `m` and `hnot` is about `S₁`.
      -- Determinism of `V₁` turns that into `verify stmt tr.fst ∉ lang₂`, which is `¬ S₂.toFun 0`
      -- by `S₂.toFun_empty`; and with `n = 0`, round `0` *is* `S₂`'s last round.
      subst hn
      rw [dif_pos (show (((Fin.last (m + 0)) : Fin (m + 0 + 1)) : ℕ) ≤ m by
        simp only [Fin.val_last]; omega)] at hnot
      have hS₁ : ¬ S₁.toFun (Fin.last m) stmt (FullTranscript.fst tr) := fun hc =>
        hnot (stateFunction_toFun_heq S₁ (Fin.ext (by simp)) rfl
          ((transcript_fst_heq_full tr).symm.trans (heq_eqMp _ _).symm) hc)
      refine S₂.toFun_full _ _ fun hc => ?_
      exact verify_notMem_of_not_toFun S₁ hVerify stmt (FullTranscript.fst tr) hS₁
        ((S₂.toFun_empty _).mpr (stateFunction_toFun_heq S₂ (Fin.ext (by simp)) rfl
          (heq_of_eq (funext fun i => Fin.elim0 i)) hc))
    · -- `pSpec₂` is non-empty, so the appended protocol's last round lies in the `else` branch and
      -- `hnot` is literally the hypothesis of `S₂`'s own `toFun_full`.
      rw [dif_neg (show ¬ (((Fin.last (m + n)) : Fin (m + n + 1)) : ℕ) ≤ m by
        simp only [Fin.val_last]; omega)] at hnot
      refine S₂.toFun_full _ _ fun hc => hnot (Or.inr ?_)
      exact stateFunction_toFun_heq S₂ (Fin.ext (by simp))
        (congrArg (verify stmt) (transcript_fst_eq_full tr).symm)
        (transcript_snd_heq_full tr).symm hc

end Verifier
