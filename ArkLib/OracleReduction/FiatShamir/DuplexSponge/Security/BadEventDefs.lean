/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

/-!
# Trace-only bad-event definitions (CO25 Definitions 5.5–5.7)

Lower module holding the trace-only surface of the duplex-sponge Fiat-Shamir bad-event analysis
(Section 5.6):

- **Redundant entries & base trace (Defs 5.5, 5.6):** `isRedundantEntryOfPrefix`,
  `hasNoRedundantEntries`, and `getBaseTrace` (plus the trace-only structural lemmas on
  membership, sublist, and prefix behaviour that the online `Monitor` needs).
- **Trace-only bad events (Def 5.7):** `E_h`, `E_p`, `E_pinv`, `E_dup`, `E_func`, and the
  combined `E`.

This module imports only the lower trace/data dependency `TraceDataStructures`; it never imports
`ProverTransform` or `TraceTransform`.  That is the dependency boundary that lets live algorithms
(`D2SQuery`, `StdTrace`) invoke `Monitor` against `E` without creating an import cycle.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

/-! ## Definition 5.5 and Definition 5.6 - Redundant entries in a trace -/
section Def_5_5_6_RedundantEntryDSHelpers

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- **Definition 5.5**: Redundancy test for a new entry against a prefix of the trace -/
def isRedundantEntryOfPrefix
    (pref : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  match entry with
  | ⟨.inl stmt, capSeg⟩ =>
      ⟨.inl stmt, capSeg⟩ ∈ pref
  | ⟨.inr (.inl stateIn), stateOut⟩ =>
      ⟨.inr (.inl stateIn), stateOut⟩ ∈ pref
      ∨ ⟨.inr (.inr stateOut), stateIn⟩ ∈ pref
  | ⟨.inr (.inr stateOut), stateIn⟩ =>
      ⟨.inr (.inr stateOut), stateIn⟩ ∈ pref
      ∨ ⟨.inr (.inl stateIn), stateOut⟩ ∈ pref

/-- CO25 Definition 5.6 — Base trace `tr̄` side condition.
`hasNoRedundantEntries log` holds iff no entry of `log` is redundant in the sense of
Definition 5.5.  The base trace `tr̄` is the unique sub-log satisfying this predicate
(see `getBaseTrace`). -/
def hasNoRedundantEntries (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ i : ℕ, ∀ hi : i < log.length,
    ¬ isRedundantEntryOfPrefix (log.take i) log[i]

private lemma noRedundantEntryDS_nil : hasNoRedundantEntries (StmtIn := StmtIn) (U := U) [] := by
  intro i hi _
  exact (Nat.not_lt_zero i) hi

private lemma noRedundantEntryDS_append_singleton
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : hasNoRedundantEntries acc)
    (hEntry : ¬ isRedundantEntryOfPrefix acc entry) :
    hasNoRedundantEntries (acc ++ [entry]) := by
  intro i hi
  have hi' : i < acc.length + 1 := by
    rw [List.length_append, List.length_singleton] at hi
    exact hi
  by_cases hlt : i < acc.length
  · have hOld :
      ¬ isRedundantEntryOfPrefix (acc.take i) acc[i] := hAcc i hlt
    simp only [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getElem_append_left hlt]
    exact hOld
  · have hEq : i = acc.length := Nat.eq_of_lt_succ_of_not_lt hi' hlt
    subst hEq
    revert hEntry
    simp [isRedundantEntryOfPrefix]

noncomputable def getBaseTraceAux
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) := by
  classical
  exact match remaining with
  | [] => acc
  | entry :: rest =>
      if hRed : isRedundantEntryOfPrefix acc entry then
        getBaseTraceAux rest acc
      else
        getBaseTraceAux rest (acc ++ [entry])

private lemma getBaseTraceAux_noRedundant
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : hasNoRedundantEntries acc) :
    hasNoRedundantEntries (getBaseTraceAux remaining acc) := by
  classical
  induction remaining generalizing acc with
  | nil => exact hAcc
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc hAcc
      · let hAcc' := noRedundantEntryDS_append_singleton acc entry hAcc hRed
        simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih (acc ++ [entry]) hAcc'

/-- CO25 Definition 5.6 — Compute the base trace `tr̄` of a duplex-sponge query-answer trace by
removing all redundant entries (in the sense of Definition 5.5). -/
noncomputable def getBaseTrace
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  getBaseTraceAux log []

lemma getBaseTrace_noRedundant
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    hasNoRedundantEntries (getBaseTrace log) :=
  getBaseTraceAux_noRedundant log [] (noRedundantEntryDS_nil (StmtIn := StmtIn) (U := U))

/-! ### Structural lemmas about `getBaseTrace` (membership / order bridge)

These connect the *external* `trace` (where backtrack sequences live) to its base trace `tr̄`
(`getBaseTrace`, where the bad events `E_dup`/`E_func` are evaluated).  They are used by the
toolbox lemmas (B1)/(B2) and Lemmas 5.12/5.14/5.16. -/

/-- Redundancy is monotone in the prefix: enlarging the prefix can only make an entry *more*
redundant. -/
private lemma isRedundantEntryOfPrefix_mono
    {acc acc' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hsub : acc ⊆ acc')
    (h : isRedundantEntryOfPrefix acc entry) : isRedundantEntryOfPrefix acc' entry := by
  obtain ⟨q, r⟩ := entry
  match q with
  | .inl stmt =>
      exact hsub h
  | .inr (.inl stateIn) =>
      rcases h with h | h
      · exact Or.inl (hsub h)
      · exact Or.inr (hsub h)
  | .inr (.inr stateOut) =>
      rcases h with h | h
      · exact Or.inl (hsub h)
      · exact Or.inr (hsub h)

/-- Entries already in the accumulator survive `getBaseTraceAux`. -/
private lemma mem_getBaseTraceAux_of_mem_acc
    (remaining acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {e : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (he : e ∈ acc) : e ∈ getBaseTraceAux remaining acc := by
  classical
  induction remaining generalizing acc with
  | nil => simpa [getBaseTraceAux] using he
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc he
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih (acc ++ [entry]) (List.mem_append_left _ he)

/-- `getBaseTraceAux` is a fold: processing `l₁ ++ l₂` is processing `l₂` after `l₁`. -/
private lemma getBaseTraceAux_append
    (l₁ l₂ acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    getBaseTraceAux (l₁ ++ l₂) acc = getBaseTraceAux l₂ (getBaseTraceAux l₁ acc) := by
  classical
  induction l₁ generalizing acc with
  | nil => simp [getBaseTraceAux]
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [List.cons_append, getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc
      · simp only [List.cons_append, getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih (acc ++ [entry])

/-- `getBaseTraceAux remaining acc` is a sublist of `acc ++ remaining`. -/
private lemma getBaseTraceAux_sublist
    (remaining acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    (getBaseTraceAux remaining acc).Sublist (acc ++ remaining) := by
  classical
  induction remaining generalizing acc with
  | nil => simp [getBaseTraceAux]
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        have h1 : (getBaseTraceAux rest acc).Sublist (acc ++ rest) := ih acc
        refine h1.trans ?_
        exact List.Sublist.append_left (List.sublist_cons_self entry rest) acc
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        have h1 : (getBaseTraceAux rest (acc ++ [entry])).Sublist ((acc ++ [entry]) ++ rest) :=
          ih (acc ++ [entry])
        simpa using h1

/-- `getBaseTrace` is a sublist of the original trace. -/
lemma getBaseTrace_sublist
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    (getBaseTrace log).Sublist log := by
  have := getBaseTraceAux_sublist log ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))
  simpa [getBaseTrace] using this

/-- Bridge: if the entry at position `k` of `trace` is not redundant relative to the literal
prefix `trace.take k`, then it survives into `getBaseTrace trace`. -/
private lemma mem_getBaseTrace_of_not_redundant_take
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (k : ℕ) (hk : k < trace.length)
    (hnr : ¬ isRedundantEntryOfPrefix (trace.take k) (trace.get ⟨k, hk⟩)) :
    (trace.get ⟨k, hk⟩) ∈ getBaseTrace trace := by
  classical
  set e := trace.get ⟨k, hk⟩ with he
  -- Split the fold at position `k`.
  have key : getBaseTraceAux (trace.drop k) (getBaseTrace (trace.take k))
           = getBaseTrace trace := by
    rw [getBaseTrace, getBaseTrace, ← getBaseTraceAux_append, List.take_append_drop]
  -- `e` is not redundant relative to the (smaller) filtered prefix.
  have hsub : getBaseTrace (trace.take k) ⊆ trace.take k :=
    (getBaseTrace_sublist (trace.take k)).subset
  have hnr' : ¬ isRedundantEntryOfPrefix (getBaseTrace (trace.take k)) e := by
    intro hc
    exact hnr (isRedundantEntryOfPrefix_mono hsub hc)
  -- Unfold one step of the fold: `e` is appended and then persists.
  have hdrop : trace.drop k = e :: trace.drop (k + 1) := by
    rw [he, List.get_eq_getElem]; exact List.drop_eq_getElem_cons hk
  rw [← key, hdrop]
  simp only [getBaseTraceAux, hnr', ↓reduceDIte]
  exact mem_getBaseTraceAux_of_mem_acc _ _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

/-- `getElem?` form of `mem_getBaseTrace_of_not_redundant_take`. -/
private lemma mem_getBaseTrace_of_getElem?_not_redundant
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {k : ℕ} {e : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : (trace)[k]? = some e)
    (hnr : ¬ isRedundantEntryOfPrefix (trace.take k) e) :
    e ∈ getBaseTrace trace := by
  rw [List.getElem?_eq_some_iff] at hget
  obtain ⟨hk, hek⟩ := hget
  have hmem := mem_getBaseTrace_of_not_redundant_take trace k hk
    (by rw [List.get_eq_getElem, hek]; exact hnr)
  rwa [List.get_eq_getElem, hek] at hmem

/-- A forward-permutation entry indexed by a `getElem?` whose two query forms do not occur earlier
survives into `getBaseTrace`. -/
lemma permFwd_mem_getBaseTrace
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {sIn sOut : CanonicalSpongeState U} {k : ℕ}
    (hget : (trace)[k]? = some ⟨.inr (.inl sIn), sOut⟩)
    (hnrA : (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k)
    (hnrB : (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k) :
    (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace := by
  refine mem_getBaseTrace_of_getElem?_not_redundant trace hget ?_
  intro hred
  simp only [isRedundantEntryOfPrefix] at hred
  rcases hred with h | h
  · exact hnrA h
  · exact hnrB h

/-- An inverse-permutation entry indexed by a `getElem?` whose two query forms do not occur earlier
survives into `getBaseTrace`. -/
lemma permInv_mem_getBaseTrace
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {sOut sIn : CanonicalSpongeState U} {k : ℕ}
    (hget : (trace)[k]? = some ⟨.inr (.inr sOut), sIn⟩)
    (hnrB : (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k)
    (hnrA : (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k) :
    (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace := by
  refine mem_getBaseTrace_of_getElem?_not_redundant trace hget ?_
  intro hred
  simp only [isRedundantEntryOfPrefix] at hred
  rcases hred with h | h
  · exact hnrB h
  · exact hnrA h

/-- Every normalized permutation pair represented anywhere in a raw trace has a representative in
its base trace.  The proof selects the first occurrence in either direction; Definition 5.5 then
ensures that this occurrence is retained.  This is the missing set-to-base bridge for transferring
the D2SQuery table mirror to bad-event reasoning. -/
lemma normalizedPermPair_mem_getBaseTrace_of_mem
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sIn sOut : CanonicalSpongeState U)
    (hmem : (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace ∨
      ⟨.inr (.inr sOut), sIn⟩ ∈ trace) :
    (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace ∨
      ⟨.inr (.inr sOut), sIn⟩ ∈ getBaseTrace trace := by
  classical
  let P : ℕ → Prop := fun k =>
    ((trace)[k]? = some ⟨.inr (.inl sIn), sOut⟩) ∨
      (trace)[k]? = some ⟨.inr (.inr sOut), sIn⟩
  have hExists : ∃ k, P k := by
    rcases hmem with hFwd | hInv
    · obtain ⟨k, hget⟩ := List.mem_iff_getElem?.mp hFwd
      exact ⟨k, Or.inl hget⟩
    · obtain ⟨k, hget⟩ := List.mem_iff_getElem?.mp hInv
      exact ⟨k, Or.inr hget⟩
  let k := Nat.find hExists
  have hk : P k := Nat.find_spec hExists
  have hFirst : ∀ m < k, ¬ P m := by
    intro m hmk hm
    have hle : k ≤ m := Nat.find_min' hExists hm
    omega
  have hnotEarlierFwd :
      (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k := by
    rw [List.mem_take_iff_getElem]
    rintro ⟨m, hm, hget⟩
    have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
    have hmLen : m < trace.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    apply hFirst m hmk
    left
    rw [List.getElem?_eq_getElem hmLen]
    exact congrArg some hget
  have hnotEarlierInv :
      (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k := by
    rw [List.mem_take_iff_getElem]
    rintro ⟨m, hm, hget⟩
    have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
    have hmLen : m < trace.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    apply hFirst m hmk
    right
    rw [List.getElem?_eq_getElem hmLen]
    exact congrArg some hget
  rcases hk with hFwd | hInv
  · exact Or.inl (permFwd_mem_getBaseTrace trace hFwd hnotEarlierFwd hnotEarlierInv)
  · exact Or.inr (permInv_mem_getBaseTrace trace hInv hnotEarlierInv hnotEarlierFwd)

/-- The accumulator is a prefix of `getBaseTraceAux` (entries are only ever appended). -/
private lemma getBaseTraceAux_prefix
    (remaining acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    acc <+: getBaseTraceAux remaining acc := by
  classical
  induction remaining generalizing acc with
  | nil => simp [getBaseTraceAux]
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact (List.prefix_append acc [entry]).trans (ih (acc ++ [entry]))

/-- Base traces preserve raw-trace prefix order: filtering a shorter raw prefix gives a prefix of
the filtered longer prefix.  This is the public raw-to-base bridge used by the Lemma 5.8
first-witness argument. -/
lemma getBaseTrace_take_prefix
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) {a b : ℕ} (hab : a ≤ b) :
    getBaseTrace (trace.take a) <+: getBaseTrace (trace.take b) := by
  classical
  have hsplit : trace.take b = trace.take a ++ (trace.take b).drop a := by
    conv_lhs => rw [← List.take_append_drop a (trace.take b)]
    rw [List.take_take, Nat.min_eq_left hab]
  calc getBaseTrace (trace.take a)
      <+: getBaseTraceAux ((trace.take b).drop a) (getBaseTrace (trace.take a)) :=
        getBaseTraceAux_prefix _ _
    _ = getBaseTrace (trace.take b) := by
        unfold getBaseTrace
        rw [← getBaseTraceAux_append, ← hsplit]

/-- Normalization never changes the order of already processed base entries.  More precisely,
if a raw trace is a prefix of another raw trace, then its normalized base trace is a prefix of
the latter normalized base trace.  This is the general, non-indexed form of
`getBaseTrace_take_prefix`; it is the bridge needed to carry a monitored bad-event witness from
an early stopped execution to the complete raw trace. -/
lemma getBaseTrace_prefix_of_prefix
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hprefix : trace <+: trace') :
    getBaseTrace trace <+: getBaseTrace trace' := by
  classical
  have htrace' : trace ++ trace'.drop trace.length = trace' :=
    List.prefix_iff_eq_append.mp hprefix
  rw [← htrace']
  unfold getBaseTrace
  rw [getBaseTraceAux_append]
  exact getBaseTraceAux_prefix _ _

/-- Length form of `getBaseTrace_take_prefix`. -/
lemma getBaseTrace_take_length_mono
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) {a b : ℕ} (hab : a ≤ b) :
    (getBaseTrace (trace.take a)).length ≤ (getBaseTrace (trace.take b)).length :=
  (getBaseTrace_take_prefix trace hab).length_le

/-- The base index of a non-redundant trace position `k` is `|getBaseTrace (trace.take k)|`, and the
base trace there carries that entry.  This is the order-preserving "first occurrence ↦ base index"
map used for Lemma 5.16. -/
lemma baseIdx_of_getElem?_not_redundant
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {k : ℕ} {e : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : (trace)[k]? = some e)
    (hnr : ¬ isRedundantEntryOfPrefix (trace.take k) e) :
    ∃ hb : (getBaseTrace (trace.take k)).length < (getBaseTrace trace).length,
      (getBaseTrace trace)[(getBaseTrace (trace.take k)).length]'hb = e := by
  classical
  rw [List.getElem?_eq_some_iff] at hget
  obtain ⟨hk, hek⟩ := hget
  -- Decompose the fold and unfold one step at position `k`.
  have key : getBaseTraceAux (trace.drop k) (getBaseTrace (trace.take k)) = getBaseTrace trace := by
    rw [getBaseTrace, getBaseTrace, ← getBaseTraceAux_append, List.take_append_drop]
  have hsub : getBaseTrace (trace.take k) ⊆ trace.take k :=
    (getBaseTrace_sublist (trace.take k)).subset
  have hnr' : ¬ isRedundantEntryOfPrefix (getBaseTrace (trace.take k)) e :=
    fun hc => hnr (isRedundantEntryOfPrefix_mono hsub hc)
  have hdrop : trace.drop k = e :: trace.drop (k + 1) := by
    rw [← hek]; exact List.drop_eq_getElem_cons hk
  have hstep : getBaseTrace trace
      = getBaseTraceAux (trace.drop (k + 1)) (getBaseTrace (trace.take k) ++ [e]) := by
    rw [← key, hdrop]; simp only [getBaseTraceAux, hnr', ↓reduceDIte]
  have hpre : (getBaseTrace (trace.take k) ++ [e]) <+: getBaseTrace trace := by
    rw [hstep]; exact getBaseTraceAux_prefix _ _
  have hlen : (getBaseTrace (trace.take k)).length
      < (getBaseTrace (trace.take k) ++ [e]).length := by simp
  refine ⟨lt_of_lt_of_le hlen hpre.length_le, ?_⟩
  set b := (getBaseTrace (trace.take k)).length with hbdef
  have h2 : (getBaseTrace (trace.take k) ++ [e])[b]'hlen = e := by simp [hbdef]
  exact (hpre.getElem hlen).symm.trans h2

/-- Strengthening of `baseIdx_of_getElem?_not_redundant`: the base prefix before the retained raw
entry is exactly the base trace of the raw prefix before that entry. -/
lemma basePrefix_of_getElem?_not_redundant
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {k : ℕ} {e : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : (trace)[k]? = some e)
    (hnr : ¬ isRedundantEntryOfPrefix (trace.take k) e) :
    ∃ hb : (getBaseTrace (trace.take k)).length < (getBaseTrace trace).length,
      (getBaseTrace trace).take (getBaseTrace (trace.take k)).length =
          getBaseTrace (trace.take k) ∧
        (getBaseTrace trace)[(getBaseTrace (trace.take k)).length]'hb = e := by
  classical
  rw [List.getElem?_eq_some_iff] at hget
  obtain ⟨hk, hek⟩ := hget
  have key : getBaseTraceAux (trace.drop k) (getBaseTrace (trace.take k)) = getBaseTrace trace := by
    rw [getBaseTrace, getBaseTrace, ← getBaseTraceAux_append, List.take_append_drop]
  have hsub : getBaseTrace (trace.take k) ⊆ trace.take k :=
    (getBaseTrace_sublist (trace.take k)).subset
  have hnr' : ¬ isRedundantEntryOfPrefix (getBaseTrace (trace.take k)) e :=
    fun hc => hnr (isRedundantEntryOfPrefix_mono hsub hc)
  have hdrop : trace.drop k = e :: trace.drop (k + 1) := by
    rw [← hek]; exact List.drop_eq_getElem_cons hk
  have hstep : getBaseTrace trace
      = getBaseTraceAux (trace.drop (k + 1)) (getBaseTrace (trace.take k) ++ [e]) := by
    rw [← key, hdrop]; simp only [getBaseTraceAux, hnr', ↓reduceDIte]
  have hpre : (getBaseTrace (trace.take k) ++ [e]) <+: getBaseTrace trace := by
    rw [hstep]; exact getBaseTraceAux_prefix _ _
  have hpreBase : getBaseTrace (trace.take k) <+: getBaseTrace trace :=
    (List.prefix_append (getBaseTrace (trace.take k)) [e]).trans hpre
  have htake : (getBaseTrace trace).take (getBaseTrace (trace.take k)).length =
      getBaseTrace (trace.take k) := by
    have hprefixEq := (List.prefix_iff_eq_append.mp hpreBase).symm
    rw [hprefixEq, List.take_left]
  have hlen : (getBaseTrace (trace.take k)).length
      < (getBaseTrace (trace.take k) ++ [e]).length := by simp
  refine ⟨lt_of_lt_of_le hlen hpre.length_le, htake, ?_⟩
  set b := (getBaseTrace (trace.take k)).length with hbdef
  have h2 : (getBaseTrace (trace.take k) ++ [e])[b]'hlen = e := by simp [hbdef]
  exact (hpre.getElem hlen).symm.trans h2

/-- A hash entry indexed by a `getElem?` not occurring earlier survives into `getBaseTrace`. -/
lemma hash_mem_getBaseTrace
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {cap : Vector U SpongeSize.C} {k : ℕ}
    (hget : (trace)[k]? = some ⟨.inl stmt, cap⟩)
    (hnr : (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉ trace.take k) :
    (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace := by
  refine mem_getBaseTrace_of_getElem?_not_redundant trace hget ?_
  intro hred
  simp only [isRedundantEntryOfPrefix] at hred
  exact hnr hred

/-- Every hash pair represented anywhere in a raw trace has a representative in its base trace.
The proof selects the first raw occurrence of the exact hash pair; Definition 5.5 then keeps it
because no equal hash pair occurs earlier. -/
lemma hash_pair_mem_getBaseTrace_of_mem
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (hmem : (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace) :
    (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
      getBaseTrace trace := by
  classical
  let P : ℕ → Prop := fun k =>
    (trace)[k]? = some (⟨.inl stmt, cap⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U))
  have hExists : ∃ k, P k := by
    rw [List.mem_iff_getElem?] at hmem
    exact hmem
  let k := Nat.find hExists
  have hk : P k := Nat.find_spec hExists
  have hFirst : ∀ m < k, ¬ P m := by
    intro m hmk hm
    have hle : k ≤ m := Nat.find_min' hExists hm
    omega
  have hnotEarlier :
      (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k := by
    rw [List.mem_take_iff_getElem]
    rintro ⟨m, hm, hget⟩
    have hmk : m < k := lt_of_lt_of_le hm (Nat.min_le_left _ _)
    have hmLen : m < trace.length := lt_of_lt_of_le hm (Nat.min_le_right _ _)
    exact hFirst m hmk (by
      unfold P
      rw [List.getElem?_eq_getElem hmLen]
      exact congrArg some hget)
  exact hash_mem_getBaseTrace trace hk hnotEarlier

/-- Appending an entry that is already redundant relative to the current base trace does not
change the base trace.  This is the generic cache-hit/consistency-response eliminator: if the
new raw entry is already represented by `getBaseTrace trace`, it cannot become a fresh base
representative. -/
lemma getBaseTrace_append_singleton_of_redundant_base
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hred : isRedundantEntryOfPrefix (getBaseTrace trace) entry) :
    getBaseTrace (trace ++ [entry]) = getBaseTrace trace := by
  classical
  unfold getBaseTrace
  rw [getBaseTraceAux_append]
  change getBaseTraceAux [entry] (getBaseTraceAux trace []) = getBaseTraceAux trace []
  change isRedundantEntryOfPrefix (getBaseTraceAux trace []) entry at hred
  rw [show getBaseTraceAux [entry] (getBaseTraceAux trace []) =
      if hRed : isRedundantEntryOfPrefix (getBaseTraceAux trace []) entry then
        getBaseTraceAux [] (getBaseTraceAux trace [])
      else
        getBaseTraceAux [] (getBaseTraceAux trace [] ++ [entry]) by rfl]
  rw [dif_pos hred]
  rfl

/-- Appending an entry that is not redundant relative to the current base trace appends that entry
to the base trace.  This is the generic fresh-representative counterpart of
`getBaseTrace_append_singleton_of_redundant_base`. -/
lemma getBaseTrace_append_singleton_of_not_redundant_base
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hnot : ¬ isRedundantEntryOfPrefix (getBaseTrace trace) entry) :
    getBaseTrace (trace ++ [entry]) = getBaseTrace trace ++ [entry] := by
  classical
  unfold getBaseTrace
  rw [getBaseTraceAux_append]
  change getBaseTraceAux [entry] (getBaseTraceAux trace []) =
    getBaseTraceAux trace [] ++ [entry]
  change ¬ isRedundantEntryOfPrefix (getBaseTraceAux trace []) entry at hnot
  rw [show getBaseTraceAux [entry] (getBaseTraceAux trace []) =
      if hRed : isRedundantEntryOfPrefix (getBaseTraceAux trace []) entry then
        getBaseTraceAux [] (getBaseTraceAux trace [])
      else
        getBaseTraceAux [] (getBaseTraceAux trace [] ++ [entry]) by rfl]
  rw [dif_neg hnot]
  rfl

/-- Adding one raw query-answer occurrence can introduce at most one new base-trace
representative.  This is deliberately phrased as a length inequality, so callers need not
distinguish an already-represented query from a fresh representative. -/
lemma getBaseTrace_append_singleton_length_le_succ
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) :
    (getBaseTrace (trace ++ [entry])).length ≤ (getBaseTrace trace).length + 1 := by
  classical
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace trace) entry
  · rw [getBaseTrace_append_singleton_of_redundant_base trace entry hred]
    omega
  · rw [getBaseTrace_append_singleton_of_not_redundant_base trace entry hred]
    simp

end Def_5_5_6_RedundantEntryDSHelpers

namespace BadEventDS
open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)

/-! ## Definition 5.7 — trace-only bad events (`E_h`, `E_p`, `E_{p⁻¹}`, `E_dup`, `E_func`, `E`) -/

section Def57_TraceOnlyBadEvents

/-! The main bad event `E` (Def 5.7) is the disjunction of two conditions: a capacity-segment
duplication on the base trace (`E_dup`), or `p` behaving non-functionally (`E_func`). -/

/- NOTE: the paper write `∃ j > 0`, which can be confusing since we don't know whether the intended
indexing is from 0 or from 1. We assume they mean from 1, and since indexing here is from 0, we just
write `∃ j`. -/

/-- A unified check for whether a capacity segment `capSeg` has appeared previously as an
output capacity (strictly before `j`) or as an input capacity (up to and including `j`).
This exactly captures the redundancy conditions in `E_h`, `E_p`, and `E_{p⁻¹}`. -/
def isDuplicatedPriorCapacity (baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j : Fin baseTrace.length) (capSeg : Vector U SpongeSize.C) : Prop :=
  (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
  (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
    stateOut1.capacitySegment = capSeg) ∨
  (∃ j' < j, ∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
    stateIn2.capacitySegment = capSeg) ∨
  (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
    stateIn3.capacitySegment = capSeg) ∨
  (∃ j' ≤ j, ∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
    stateOut4.capacitySegment = capSeg)

/-- CO25 Definition 5.7 — Event `E_h(tr)` (Eq. 23).
An output capacity segment `s_C` of an `h`-entry in the base trace `tr̄` previously appears
as an output or input capacity segment of `h`, `p`, or `p⁻¹`:

```
E_h(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (h, ·, s_C)  and  ∃ j' < j :
  tr̄_{j'} = (h, ·, s_C)  ∨  tr̄_{j'} = (p, ·, (·, s_C))  ∨  tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  tr̄_{j'} = (p, (·, s_C), ·)  ∨  tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

All five prior-entry branches are unified via `isDuplicatedPriorCapacity`. -/
def capacitySegmentDupHash : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stmt : StmtIn, baseTrace[j] = ⟨.inl stmt, capSeg⟩) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_h := capacitySegmentDupHash

/-- CO25 Definition 5.7 — Event `E_p(tr)` (Eq. 24).
An output capacity segment `s_C` of a `p`-entry in the base trace `tr̄` previously (or
simultaneously for some branches) appears as an output or input capacity segment of `h`, `p`,
or `p⁻¹`:

```
E_p(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (p, ·, (·, s_C))  and
  ∃ j' < j : tr̄_{j'} = (h, ·, s_C)  ∨  ∃ j' < j : tr̄_{j'} = (p, ·, (·, s_C))
  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  ∃ j' ≤ j : tr̄_{j'} = (p, (·, s_C), ·)  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

Branches realized by `isDuplicatedPriorCapacity`'s uniform `≤ j`; extensionally equal to the
paper's asymmetric `< j`/`≤ j` (the extra `j' = j` cases are vacuous). -/
def capacitySegmentDupPerm : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_p := capacitySegmentDupPerm

/-- CO25 Definition 5.7 — Event `E_{p⁻¹}(tr)` (Eq. 25).
An output capacity segment `s_C` (i.e. the output of `p⁻¹`, which is the input side `s_in`) of a
`p⁻¹`-entry in the base trace `tr̄` previously (or simultaneously for some branches) appears as
an output or input capacity segment of `h`, `p`, or `p⁻¹`:

```
E_{p⁻¹}(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (p⁻¹, ·, (·, s_C))  and
  ∃ j' < j : tr̄_{j'} = (h, ·, s_C)  ∨  ∃ j' < j : tr̄_{j'} = (p, ·, (·, s_C))
  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  ∃ j' ≤ j : tr̄_{j'} = (p, (·, s_C), ·)  ∨  ∃ j' ≤ j : tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

Same uniform-`≤ j` caveat as `E_p` (via `isDuplicatedPriorCapacity`); extensionally equal to
Eq. 25's asymmetric quantifiers. -/
def capacitySegmentDupPermInv : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_pinv := capacitySegmentDupPermInv

/-- CO25 Definition 5.7 — Combined capacity-segment duplication event `E_dup(tr)`.
Holds iff at least one of `E_h(tr)`, `E_p(tr)`, or `E_{p⁻¹}(tr)` holds: there exists an output
capacity segment in the base trace `tr̄` that previously appeared as an output or input capacity
segment. -/
def capacitySegmentDup : Prop :=
  capacitySegmentDupHash trace ∨ capacitySegmentDupPerm trace ∨ capacitySegmentDupPermInv trace

alias E_dup := capacitySegmentDup

/-- CO25 Definition 5.7 — Event `E_func(tr)` (Eq. 26).
**The same query to `p` leads to different answers**, or there are inconsistent queries across `p`
and `p⁻¹`:

```
E_func(tr) := ∃ j > 0 :
  [Case 1] tr̄_j = (p, s_in, s_out)  and  ∃ j' < j :
    (tr̄_{j'} = (p, s_in, s_out') ∧ s_out' ≠ s_out)
    ∨ (tr̄_{j'} = (p⁻¹, s_out', s_in) ∧ s_out' ≠ s_out)
  or
  [Case 2] tr̄_j = (p⁻¹, s_out, s_in)  and  ∃ j' < j :
    (tr̄_{j'} = (p⁻¹, s_out, s_in') ∧ s_in' ≠ s_in)
    ∨ (tr̄_{j'} = (p, s_in', s_out) ∧ s_in' ≠ s_in)
```

Note: `E_func(tr)` never holds for a true permutation `p` and its inverse `p⁻¹`, but may hold
(with small probability) for the D2SQuery simulator.

**Strengthening:** bidirectional. Case 1 (`j`-th entry `p`-forward) is Eq. 26; Case 2 (`j`-th entry
`p⁻¹`) has no paper counterpart but is *required* by `not_collisionFwdBwd_of_not_combined`
(Lemma 5.10, Item 3). The `≠`-output conditions are forced by base-trace non-redundancy. -/
def E_func : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    (baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      ∃ j' < j,
        (∃ stateOut1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)) ∨
    (baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      ∃ j' < j,
        (∃ stateIn1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inr stateOut, stateIn1⟩ ∧ stateIn1 ≠ stateIn) ∨
        (∃ stateIn2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inl stateIn2, stateOut⟩ ∧ stateIn2 ≠ stateIn))

/-- CO25 Definition 5.7 — Combined bad event `E(tr)`.
`E(tr)` is the disjunction `E_dup(tr) ∨ E_func(tr)`, i.e., either a capacity-segment
duplication occurs or `p` behaves non-functionally.  Lemma 5.8 bounds `Pr[E(tr_P̃ ‖ tr_V)]`
in both the sponge `𝒟_𝔖` and simulator `𝒟_Σ` experiments. -/
def E : Prop :=
  capacitySegmentDup trace ∨ E_func trace

end Def57_TraceOnlyBadEvents

end BadEventDS

end DuplexSpongeFS
