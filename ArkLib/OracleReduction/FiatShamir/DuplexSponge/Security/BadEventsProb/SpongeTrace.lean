/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Core

/-!
# Sponge trace support and deterministic trace maps for Lemma 5.8
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))


variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]


/-! ### Function violation (sponge) — the sponge permutation is a genuine function


On the `𝒟_𝔖` side every trace entry is answered by the *fixed* sampled realization `(h, p, p⁻¹)`,
so the projected log is functionally consistent (`e.2 = spongeAnswer fam e.1`) and `E_func`
(two conflicting permutation entries) is impossible — CO25 Eq. 33, sponge branch. -/
section SpongePermutationGenuineFunction

variable
  (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
  (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))

/-- The deterministic answer of one sampled sponge `(h, p, p⁻¹)` realization on a narrow DS point. -/
def spongeAnswer (fam : (D_𝔖 StmtIn U).Carrier) :
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      (duplexSpongeChallengeOracle StmtIn U).Range t
  | .inl q => fam.1 q
  | .inr (.inl sIn) => (show Equiv.Perm (CanonicalSpongeState U) from fam.2) sIn
  | .inr (.inr sOut) => (show Equiv.Perm (CanonicalSpongeState U) from fam.2).symm sOut

/-- A functionally-consistent trace (every entry answered by the fixed sponge realization) has no
`E_func` conflict at any position: `p` is a genuine bijection, so no two entries disagree. -/
lemma E_func_at_false_of_consistent
    (fam : (D_𝔖 StmtIn U).Carrier)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hc : ∀ e ∈ getBaseTrace trace, e.2 = spongeAnswer fam e.1) (j : ℕ) :
    ¬ E_func_at trace j := by
  rintro ⟨hj, sIn, sOut, hdisj⟩
  have key : ∀ (k : ℕ) (hk : k < (getBaseTrace trace).length)
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
      (a : (duplexSpongeChallengeOracle StmtIn U).Range q),
      (getBaseTrace trace)[k] = ⟨q, a⟩ → a = spongeAnswer fam q := by
    intro k hk q a hka
    have hmem : (getBaseTrace trace)[k] ∈ getBaseTrace trace := List.getElem_mem _
    have := hc _ hmem
    rw [hka] at this
    exact this
  set p : Equiv.Perm (CanonicalSpongeState U) := fam.2 with hp
  have eF : ∀ s, spongeAnswer fam (.inr (.inl s)) = p s := fun _ => rfl
  have eB : ∀ s, spongeAnswer fam (.inr (.inr s)) = p.symm s := fun _ => rfl
  rcases hdisj with ⟨hbtj, j', _, hprior⟩ | ⟨hbtj, j', _, hprior⟩
  · -- forward query at `j`: `sOut = p sIn`.
    have hj0 : sOut = p sIn := by rw [← eF]; exact key j hj _ _ hbtj
    rcases hprior with ⟨sOut1, hbtj', hne⟩ | ⟨sOut2, hbtj', hne⟩
    · have hj1 : sOut1 = p sIn := by rw [← eF]; exact key j' j'.2 _ _ hbtj'
      exact hne (hj1.trans hj0.symm)
    · have hj1 : sIn = p.symm sOut2 := by rw [← eB]; exact key j' j'.2 _ _ hbtj'
      exact hne (by rw [hj0, hj1, Equiv.apply_symm_apply])
  · -- inverse query at `j`: `sIn = p⁻¹ sOut`.
    have hj0 : sIn = p.symm sOut := by rw [← eB]; exact key j hj _ _ hbtj
    rcases hprior with ⟨sIn1, hbtj', hne⟩ | ⟨sIn2, hbtj', hne⟩
    · have hj1 : sIn1 = p.symm sOut := by rw [← eB]; exact key j' j'.2 _ _ hbtj'
      exact hne (hj1.trans hj0.symm)
    · have hj1 : sOut = p sIn2 := by rw [← eF]; exact key j' j'.2 _ _ hbtj'
      exact hne (by rw [hj0, hj1, Equiv.symm_apply_apply])

/-- Consistency of a wide (`[]ₒ + DS`) trace entry with a sponge realization: DS entries must carry
the deterministic sponge answer; the (uncallable) empty branch is vacuously consistent. -/
def wideSpongeConsistent (fam : (D_𝔖 StmtIn U).Carrier)
    (e : (t : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain) ×
      ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range t) : Prop :=
  match e with
  | ⟨.inl _, _⟩ => True
  | ⟨.inr q, r⟩ => r = spongeAnswer fam q

/-- **Generic support invariant** for the combined Lemma-5.8 implementation under a *deterministic*
DS oracle `impl` (each query returns the table answer `ans s q` and preserves the carrier `s`).
Abstract `impl`/`σ` so the `OptionT`-monad membership normalizes exactly as in
`logLength_le_of_isQueryBoundP`; the eager sponge oracle is a special case. -/
lemma combinedImpl_support_invariant {σ α : Type}
    (spongeImpl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)))
    (ans : σ → (q : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      (duplexSpongeChallengeOracle StmtIn U).Range q)
    (hdet : ∀ (q : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : σ),
        (spongeImpl q s).run = pure (some (ans s q, s)))
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (st : σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {r : Option α × (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (((simulateQ (lemma5_8CombinedImpl spongeImpl) oa).run).run st)) :
    r.2.1 = st.1 ∧ ∀ e ∈ r.2.2, e ∈ st.2 ∨ ∃ q, e = ⟨Sum.inr q, ans st.1 q⟩ := by
  induction oa using OracleComp.inductionOn generalizing st r with
  | pure x =>
    simp only [simulateQ_pure] at hr
    have : r = (some x, st) := by simpa using hr
    subst this
    exact ⟨rfl, fun e he => Or.inl he⟩
  | query_bind t mx ih =>
    match t with
    | Sum.inl q => exact PEmpty.elim q
    | Sum.inr q =>
      simp only [simulateQ_query_bind, lemma5_8CombinedImpl, OracleQuery.input_query,
        OracleQuery.cont_query, QueryImpl.add_apply_inr, lemma5_8WrappedDSImpl,
        Option.elimM, monadLift_self, OptionT.run_bind, OptionT.run_mk, StateT.run_bind,
        support_bind, Set.mem_iUnion] at hr
      obtain ⟨i, hi, hri⟩ := hr
      have hi' : i ∈ support ((spongeImpl q st.1).run >>= fun r₀ =>
          match r₀ with
          | none => (pure (none, st) :
              ProbComp (Option (([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q)) ×
                (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))
          | some (a, s') => pure (some a, (s', st.2 ++ [⟨Sum.inr q, a⟩]))) := hi
      rw [hdet, mem_support_bind_iff] at hi'
      obtain ⟨r₀, hr₀, hi'⟩ := hi'
      rw [mem_support_pure_iff] at hr₀
      subst hr₀
      rw [mem_support_pure_iff] at hi'
      subst hi'
      have hri' : r ∈ support ((simulateQ (lemma5_8CombinedImpl spongeImpl)
          (mx (ans st.1 q))).run.run (st.1, st.2 ++ [⟨Sum.inr q, ans st.1 q⟩])) := hri
      have hIH := ih (ans st.1 q) (st.1, st.2 ++ [⟨Sum.inr q, ans st.1 q⟩]) hri'
      refine ⟨hIH.1, fun e he => ?_⟩
      rcases hIH.2 e he with hmem | hcons
      · rcases List.mem_append.mp hmem with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h
          subst h
          exact Or.inr ⟨q, rfl⟩
      · exact Or.inr hcons

/-- **Inner D2S step trace append (foundational bridge).** Any successful support point of the
simulated `d2sQueryStep` extends the internal D2S trace by exactly the answered narrow query.

This is the one-step operational fact needed to discharge the generic `happend` premise used by
the combined-log/internal-trace bridge.  It is intentionally stated against the simulated
`OptionT.run ((d2sQueryStep q).run st)` surface, so the remaining proof obligation is purely about
the §5.4 simulator step and not about the outer Lemma-5.8 wrapper. -/
lemma d2sQueryStep_support_trace_append
    {T_H T_P : Type}
    [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {i : Option (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sQueryStep
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run) :
    ∀ a st', i = some (some (a, st')) →
      st'.trace = st.trace ++ [⟨q, a⟩] := by
  exact ProverTransform.d2sQueryStep_support_trace_append
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    gImpl auxImpl q st hi

/-- **Sponge-side support invariant.** Running any computation under the sponge (eager-table)
implementation preserves the sampled carrier and appends only table-consistent entries. -/
lemma spongeConsistent_of_mem_support {α : Type}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (st : (D_𝔖 StmtIn U).Carrier × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {r : Option α × ((D_𝔖 StmtIn U).Carrier ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (((simulateQ (lemma5_8CombinedImpl
        (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl))) oa).run).run st)) :
    r.2.1 = st.1 ∧ ∀ e ∈ r.2.2, e ∈ st.2 ∨ wideSpongeConsistent st.1 e := by
  have hdet : ∀ (q : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : (D_𝔖 StmtIn U).Carrier),
      (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl) q s).run
        = pure (some (spongeAnswer s q, s)) := by
    intro q s
    rcases q with hq | (sIn | sOut) <;> rfl
  have hinv := combinedImpl_support_invariant
    (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl)) spongeAnswer hdet st hr
  refine ⟨hinv.1, fun e he => (hinv.2 e he).imp id ?_⟩
  rintro ⟨q, rfl⟩
  rfl

/-- **Projection bridge.** A wide log that is entirely `wideSpongeConsistent` projects to a narrow
log that is `spongeAnswer`-consistent (`e.2 = spongeAnswer fam e.1`). -/
lemma projectTraceLog_spongeConsistent (fam : (D_𝔖 StmtIn U).Carrier)
    (L : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (h : ∀ e ∈ L, wideSpongeConsistent fam e) :
    ∀ e ∈ lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) L, e.2 = spongeAnswer fam e.1 := by
  intro e he
  rw [lemma5_8ProjectTraceLog, List.mem_filterMap] at he
  obtain ⟨⟨wi, wr⟩, hwe, heq⟩ := he
  rcases wi with q | q
  · exact q.elim
  · rw [Option.some.injEq] at heq
    subst heq
    have := h _ hwe
    simpa [wideSpongeConsistent] using this

/-! ### Determinism of the eager sponge execution

The eager `(h, p, p⁻¹)` implementation performs no probabilistic sampling and never aborts, so
running any `oa : OracleComp ([]ₒ + DS) α` under it is a *deterministic* table walk.  We package
this as an explicit `Id`-executor `eagerDetExec` and prove the probabilistic run equals `pure` of
it (`eagerRun_eq_pure`).  This collapses every downstream `ProbComp` bind over the eager run to a
pure substitution — turning the whole experiment into `G <$> 𝒟_𝔖.sample` for a deterministic `G`,
and reducing all causality reasoning to a pure structural induction. -/
section EagerDeterminism

/-- Deterministic `Id`-executor mirroring `lemma5_8CombinedImpl` under the eager sponge table:
each DS query returns `spongeAnswer` of the fixed carrier and appends the wide-tagged entry; the
empty summand is uncallable. -/
def eagerDetImpl :
    QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
      (StateT ((D_𝔖 StmtIn U).Carrier ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) Id) :=
  fun q => match q with
    | .inl e => PEmpty.elim e
    | .inr q' => fun st =>
        (spongeAnswer st.1 q', (st.1, st.2 ++ [⟨.inr q', spongeAnswer st.1 q'⟩]))

/-- The deterministic value produced by walking `oa` under the eager sponge table from state `st`. -/
def eagerDetExec {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : (D_𝔖 StmtIn U).Carrier ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    α × ((D_𝔖 StmtIn U).Carrier ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :=
  (simulateQ eagerDetImpl oa).run st

/-- **Determinism.** The probabilistic eager run is a point mass at the deterministic executor. -/
lemma eagerRun_eq_pure {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : (D_𝔖 StmtIn U).Carrier ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    ((simulateQ (lemma5_8CombinedImpl
        (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl))) oa).run).run st
      = (pure (some (eagerDetExec oa st).1, (eagerDetExec oa st).2) :
          ProbComp (Option α × _)) := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
    simp only [simulateQ_pure, eagerDetExec]
    rfl
  | query_bind t mx ih =>
    match t with
    | Sum.inl q => exact PEmpty.elim q
    | Sum.inr q =>
      have hstep : ((lemma5_8WrappedDSImpl
          (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl)) q).run).run st
          = pure (some (spongeAnswer st.1 q),
              (st.1, st.2 ++ [⟨.inr q, spongeAnswer st.1 q⟩])) := by
        rcases q with a | (b | c) <;> rfl
      have hrhs : eagerDetExec (liftM (OracleSpec.query (Sum.inr q)) >>= mx) st
          = eagerDetExec (mx (spongeAnswer st.1 q))
              (st.1, st.2 ++ [⟨Sum.inr q, spongeAnswer st.1 q⟩]) := by
        simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
          OracleQuery.cont_query, QueryImpl.add_apply_inr, eagerDetImpl, StateT.run_bind,
          monadLift_self]
        rfl
      have hlhs : ((simulateQ (lemma5_8CombinedImpl
            (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl)))
            (liftM (OracleSpec.query (Sum.inr q)) >>= mx)).run).run st
          = ((simulateQ (lemma5_8CombinedImpl
              (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl)))
              (mx (spongeAnswer st.1 q))).run).run
              (st.1, st.2 ++ [⟨Sum.inr q, spongeAnswer st.1 q⟩]) := by
        simp only [simulateQ_query_bind, lemma5_8CombinedImpl, OracleQuery.input_query,
          QueryImpl.add_apply_inr, Option.elimM, monadLift_self,
          OptionT.run_bind, StateT.run_bind]
        erw [hstep]
        rfl
      rw [hlhs, hrhs]
      exact ih (spongeAnswer st.1 q) (st.1, st.2 ++ [⟨Sum.inr q, spongeAnswer st.1 q⟩])

/-- Deterministic eager execution never changes the sampled sponge family. -/
lemma eagerDetExec_carrier_eq {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : (D_𝔖 StmtIn U).Carrier ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    (eagerDetExec oa st).2.1 = st.1 := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
      simp only [eagerDetExec, simulateQ_pure]
      rfl
  | query_bind t mx ih =>
      match t with
      | Sum.inl q => exact PEmpty.elim q
      | Sum.inr q =>
          simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
            OracleQuery.cont_query, QueryImpl.add_apply_inr, eagerDetImpl, StateT.run_bind,
            monadLift_self]
          exact ih (spongeAnswer st.1 q)
            (st.1, st.2 ++ [⟨Sum.inr q, spongeAnswer st.1 q⟩])

/-- Deterministic eager execution appends a suffix of entries consistent with the fixed sampled
sponge family. -/
lemma eagerDetExec_log_eq_append {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : (D_𝔖 StmtIn U).Carrier ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    ∃ suffix : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U),
      (eagerDetExec oa st).2.2 = st.2 ++ suffix ∧
        ∀ e ∈ suffix, wideSpongeConsistent st.1 e := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
      refine ⟨[], ?_, ?_⟩
      · simp only [eagerDetExec, simulateQ_pure, List.append_nil]
        rfl
      · intro e he
        simp at he
  | query_bind t mx ih =>
      match t with
      | Sum.inl q => exact PEmpty.elim q
      | Sum.inr q =>
          let entry : Sigma ([]ₒ + duplexSpongeChallengeOracle StmtIn U) :=
            ⟨Sum.inr q, spongeAnswer st.1 q⟩
          obtain ⟨suffix, hsuffix, hsuffixCons⟩ :=
            ih (spongeAnswer st.1 q) (st.1, st.2 ++ [entry])
          refine ⟨[entry] ++ suffix, ?_, ?_⟩
          · simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
              OracleQuery.cont_query, QueryImpl.add_apply_inr, eagerDetImpl, StateT.run_bind,
              monadLift_self]
            change
              (eagerDetExec (mx (spongeAnswer st.1 q))
                (st.1, st.2 ++ [entry])).2.2 =
                  st.2 ++ ([entry] ++ suffix)
            rw [hsuffix]
            rw [List.append_assoc]
          · intro e he
            rw [List.mem_append] at he
            rcases he with he | he
            · rw [List.mem_singleton] at he
              subst e
              simp only [entry, wideSpongeConsistent]
            · exact hsuffixCons e he

/-- Deterministic eager execution does not inspect the incoming log.  Starting from a non-empty
log only prefixes that log to the generated suffix, and leaves the returned value unchanged. -/
lemma eagerDetExec_value_log_eq_append_initial {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (fam : (D_𝔖 StmtIn U).Carrier)
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    (eagerDetExec oa (fam, log)).1 = (eagerDetExec oa (fam, [])).1 ∧
      (eagerDetExec oa (fam, log)).2.2 = log ++ (eagerDetExec oa (fam, [])).2.2 := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x =>
      simp only [eagerDetExec, simulateQ_pure]
      constructor
      · rfl
      · change log = log ++ []
        rw [List.append_nil]
  | query_bind t mx ih =>
      match t with
      | Sum.inl q => exact PEmpty.elim q
      | Sum.inr q =>
          simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
            eagerDetImpl, StateT.run_bind, monadLift_self]
          change
            (eagerDetExec (mx (spongeAnswer fam q))
              (fam, log ++ [⟨Sum.inr q, spongeAnswer fam q⟩])).1 =
                (eagerDetExec (mx (spongeAnswer fam q))
                  (fam, [] ++ [⟨Sum.inr q, spongeAnswer fam q⟩])).1 ∧
            (eagerDetExec (mx (spongeAnswer fam q))
              (fam, log ++ [⟨Sum.inr q, spongeAnswer fam q⟩])).2.2 =
                log ++
                  (eagerDetExec (mx (spongeAnswer fam q))
                    (fam, [] ++ [⟨Sum.inr q, spongeAnswer fam q⟩])).2.2
          simp only [List.nil_append]
          have hih := ih (spongeAnswer fam q) [⟨Sum.inr q, spongeAnswer fam q⟩]
          have hihLog := ih (spongeAnswer fam q)
            (log ++ [⟨Sum.inr q, spongeAnswer fam q⟩])
          constructor
          · rw [hihLog.1, hih.1]
          · rw [hihLog.2, hih.2, List.append_assoc]

/-- Wide-log predicate used by deterministic deferred-decision prefix lemmas.  Entries in the
uncallable empty summand are treated as good; actual eager logs only append `.inr` DS entries. -/
def eagerDetWideEntryGood
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (e : Sigma ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) : Bool :=
  match e with
  | ⟨.inl _, _⟩ => true
  | ⟨.inr q, _⟩ => ! bad q

/-- Narrow-log counterpart of `eagerDetWideEntryGood`: a projected DS entry is good exactly when
its DS query is outside the deferred-decision set. -/
def eagerDetNarrowEntryGood
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (e : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Bool :=
  ! bad e.1

/-- Local lightweight form of `List.mem_takeWhile_imp`, avoiding an extra import just for this
basic list fact. -/
private lemma mem_takeWhile_imp_bool {α : Type} {p : α → Bool} {x : α} {l : List α}
    (hx : x ∈ List.takeWhile p l) : p x = true := by
  induction l with
  | nil =>
      simp at hx
  | cons hd tl ih =>
      cases hp : p hd
      · simp [List.takeWhile, hp] at hx
      · simp [List.takeWhile, hp] at hx
        rcases hx with hEq | hTail
        · rw [hEq]
          exact hp
        · exact ih hTail

/-- If `takeWhile` consumes the entire left list, it distributes over append. -/
private lemma takeWhile_append_of_eq_self {α : Type} {p : α → Bool}
    {l₁ l₂ : List α} (hfull : List.takeWhile p l₁ = l₁) :
    List.takeWhile p (l₁ ++ l₂) = l₁ ++ List.takeWhile p l₂ := by
  induction l₁ with
  | nil =>
      rfl
  | cons hd tl ih =>
      cases hp : p hd
      · simp [List.takeWhile, hp] at hfull
      · simp [List.takeWhile, hp] at hfull
        have htl : List.takeWhile p tl = tl := by
          exact hfull
        simp [List.takeWhile, hp, ih htl]

/-- If `takeWhile` stops inside the left list, appending a suffix does not change the result. -/
private lemma takeWhile_append_of_ne_self {α : Type} {p : α → Bool}
    {l₁ l₂ : List α} (hstop : List.takeWhile p l₁ ≠ l₁) :
    List.takeWhile p (l₁ ++ l₂) = List.takeWhile p l₁ := by
  induction l₁ with
  | nil =>
      exact False.elim (hstop rfl)
  | cons hd tl ih =>
      by_cases hp : p hd = true
      · have htlStop : List.takeWhile p tl ≠ tl := by
          intro htl
          apply hstop
          simp [List.takeWhile, hp, htl]
        simp [List.takeWhile, hp, ih htlStop]
      · have hpFalse : p hd = false := by
          cases h : p hd <;> simp [h] at hp ⊢
        simp [List.takeWhile, hpFalse]

/-- If `takeWhile` does not consume the whole list, it stops at a strict prefix. -/
private lemma length_takeWhile_lt_of_ne_self_bool {α : Type} {p : α → Bool}
    {l : List α} (hstop : List.takeWhile p l ≠ l) :
    (List.takeWhile p l).length < l.length := by
  induction l with
  | nil =>
      exact False.elim (hstop rfl)
  | cons hd tl ih =>
      by_cases hp : p hd = true
      · have htlStop : List.takeWhile p tl ≠ tl := by
          intro htl
          apply hstop
          simp [List.takeWhile, hp, htl]
        simp [List.takeWhile, hp]
        exact ih htlStop
      · have hpFalse : p hd = false := by
          cases h : p hd <;> simp [h] at hp ⊢
        simp [List.takeWhile, hpFalse]

/-- If `takeWhile` consumes the left list, appending preserves the stopping-test exactly in the
right suffix. -/
private lemma takeWhile_append_full_length_lt_iff {α : Type} {p : α → Bool}
    {l₁ l₂ : List α} (hfull : List.takeWhile p l₁ = l₁) :
    (List.takeWhile p (l₁ ++ l₂)).length < (l₁ ++ l₂).length ↔
      (List.takeWhile p l₂).length < l₂.length := by
  rw [takeWhile_append_of_eq_self hfull]
  simp only [List.length_append]
  omega

/-- If `takeWhile` stops inside the left list, appending a suffix keeps the stopping index inside
the left list. -/
private lemma takeWhile_append_stops_left_length_lt {α : Type} {p : α → Bool}
    {l₁ l₂ : List α} (hstop : List.takeWhile p l₁ ≠ l₁) :
    (List.takeWhile p (l₁ ++ l₂)).length < l₁.length := by
  rw [takeWhile_append_of_ne_self hstop]
  exact length_takeWhile_lt_of_ne_self_bool hstop

/-- Optional-index form of `takeWhile_append_of_eq_self` at the first stopping element. -/
private lemma getElem?_takeWhile_append_of_eq_self {α : Type} {p : α → Bool}
    {l₁ l₂ : List α} (hfull : List.takeWhile p l₁ = l₁) :
    (l₁ ++ l₂)[(List.takeWhile p (l₁ ++ l₂)).length]? =
      l₂[(List.takeWhile p l₂).length]? := by
  rw [takeWhile_append_of_eq_self hfull, List.length_append]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- Optional-index form of `takeWhile_append_of_ne_self` at the first stopping element. -/
private lemma getElem?_takeWhile_append_of_ne_self {α : Type} {p : α → Bool}
    {l₁ l₂ : List α} (hstop : List.takeWhile p l₁ ≠ l₁) :
    (l₁ ++ l₂)[(List.takeWhile p (l₁ ++ l₂)).length]? =
      l₁[(List.takeWhile p l₁).length]? := by
  rw [takeWhile_append_of_ne_self hstop]
  rw [List.getElem?_append_left (length_takeWhile_lt_of_ne_self_bool hstop)]

/-- Projecting the wide Lemma-5.8 log commutes with taking the prefix before the first bad DS
query.  This transports the deterministic eager-prefix replay lemma from the raw `[]ₒ + DS` log to
the projected DS trace used by `getBaseTrace`. -/
lemma lemma5_8ProjectTraceLog_takeWhile_eagerDetWideEntryGood
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U)
        (List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad) log)
      =
    List.takeWhile (eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad)
      (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) log) := by
  induction log with
  | nil =>
      rfl
  | cons entry rest ih =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl q => exact PEmpty.elim q
      | inr q =>
          by_cases hb : bad q = true
          · simp [lemma5_8ProjectTraceLog, eagerDetWideEntryGood,
              eagerDetNarrowEntryGood, hb]
          · have hbFalse : bad q = false := by
              cases hbad : bad q <;> simp [hbad] at hb ⊢
            simp [lemma5_8ProjectTraceLog, eagerDetWideEntryGood,
              eagerDetNarrowEntryGood, hbFalse]
            exact ih

/-- If two fixed sponge families agree on every query outside a chosen deferred-decision set
`bad`, then deterministic eager execution produces the same wide-log prefix until the first
`bad` query.  This packages the adaptive causality fact used by hash/permutation freshness:
changing the answer at a deferred point cannot affect the trace before that point is queried. -/
lemma eagerDetExec_takeWhile_good_eq {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (hagree : ∀ q, bad q = false → spongeAnswer fam₁ q = spongeAnswer fam₂ q) :
    List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
        (eagerDetExec oa (fam₁, [])).2.2 =
      List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
        (eagerDetExec oa (fam₂, [])).2.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      change
        List.takeWhile (eagerDetWideEntryGood bad) [] =
          List.takeWhile (eagerDetWideEntryGood bad) []
      rfl
  | query_bind t mx ih =>
      match t with
      | Sum.inl q => exact PEmpty.elim q
      | Sum.inr q =>
          simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
            eagerDetImpl, StateT.run_bind, monadLift_self]
          change
            List.takeWhile (eagerDetWideEntryGood bad)
              (eagerDetExec (mx (spongeAnswer fam₁ q))
                (fam₁, [⟨Sum.inr q, spongeAnswer fam₁ q⟩])).2.2 =
            List.takeWhile (eagerDetWideEntryGood bad)
              (eagerDetExec (mx (spongeAnswer fam₂ q))
                (fam₂, [⟨Sum.inr q, spongeAnswer fam₂ q⟩])).2.2
          have hlog₁ := (eagerDetExec_value_log_eq_append_initial
            (StmtIn := StmtIn) (U := U)
            (oa := mx (spongeAnswer fam₁ q)) (fam := fam₁)
            (log := [⟨Sum.inr q, spongeAnswer fam₁ q⟩])).2
          have hlog₂ := (eagerDetExec_value_log_eq_append_initial
            (StmtIn := StmtIn) (U := U)
            (oa := mx (spongeAnswer fam₂ q)) (fam := fam₂)
            (log := [⟨Sum.inr q, spongeAnswer fam₂ q⟩])).2
          rw [hlog₁, hlog₂]
          by_cases hb : bad q = true
          · simp [eagerDetWideEntryGood, hb]
          · have hbFalse : bad q = false := by
              cases hbad : bad q <;> simp [hbad] at hb ⊢
            have hAns : spongeAnswer fam₁ q = spongeAnswer fam₂ q := hagree q hbFalse
            rw [hAns]
            simp [eagerDetWideEntryGood, hbFalse]
            exact ih (spongeAnswer fam₂ q)

/-- If two fixed eager sponge families agree outside a deferred-decision set `bad`, then the
first bad *query domain* reached by a deterministic execution is the same on both sides.

The answers attached to that first bad query may differ — this is precisely the deferred random
choice — but the computation has seen only good answers before choosing the query, so the queried
domain is fixed. -/
lemma eagerDetExec_first_bad_domain_eq {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (hagree : ∀ q, bad q = false → spongeAnswer fam₁ q = spongeAnswer fam₂ q) :
    let good := eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad
    let log₁ := (eagerDetExec oa (fam₁, [])).2.2
    let log₂ := (eagerDetExec oa (fam₂, [])).2.2
    List.takeWhile good log₁ = List.takeWhile good log₂ ∧
      ((List.takeWhile good log₁).length < log₁.length ↔
        (List.takeWhile good log₂).length < log₂.length) ∧
      (∀ (h₁ : (List.takeWhile good log₁).length < log₁.length)
          (h₂ : (List.takeWhile good log₂).length < log₂.length),
        log₁[(List.takeWhile good log₁).length].1 =
          log₂[(List.takeWhile good log₂).length].1) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp only [eagerDetExec, simulateQ_pure]
      refine ⟨rfl, Iff.rfl, ?_⟩
      intro h₁ _h₂
      change
        (List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
          ([] : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))).length <
          ([] : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)).length at h₁
      exact False.elim (Nat.not_lt_zero _ h₁)
  | query_bind t mx ih =>
      match t with
      | Sum.inl q => exact PEmpty.elim q
      | Sum.inr q =>
          let a₁ := spongeAnswer fam₁ q
          let a₂ := spongeAnswer fam₂ q
          let e₁ : Sigma ([]ₒ + duplexSpongeChallengeOracle StmtIn U) := ⟨Sum.inr q, a₁⟩
          let e₂ : Sigma ([]ₒ + duplexSpongeChallengeOracle StmtIn U) := ⟨Sum.inr q, a₂⟩
          have hlog₁ :
              (eagerDetExec (liftM (OracleSpec.query (Sum.inr q)) >>= mx) (fam₁, [])).2.2 =
                e₁ :: (eagerDetExec (mx a₁) (fam₁, [])).2.2 := by
            simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
              eagerDetImpl, StateT.run_bind, monadLift_self, a₁, e₁]
            change (eagerDetExec (mx a₁) (fam₁, [] ++ [e₁])).2.2 =
              e₁ :: (eagerDetExec (mx a₁) (fam₁, [])).2.2
            have h :=
              (eagerDetExec_value_log_eq_append_initial (StmtIn := StmtIn) (U := U)
                (oa := mx a₁) (fam := fam₁) (log := [e₁])).2
            rw [List.nil_append]
            rw [h]
            rfl
          have hlog₂ :
              (eagerDetExec (liftM (OracleSpec.query (Sum.inr q)) >>= mx) (fam₂, [])).2.2 =
                e₂ :: (eagerDetExec (mx a₂) (fam₂, [])).2.2 := by
            simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
              eagerDetImpl, StateT.run_bind, monadLift_self, a₂, e₂]
            change (eagerDetExec (mx a₂) (fam₂, [] ++ [e₂])).2.2 =
              e₂ :: (eagerDetExec (mx a₂) (fam₂, [])).2.2
            have h :=
              (eagerDetExec_value_log_eq_append_initial (StmtIn := StmtIn) (U := U)
                (oa := mx a₂) (fam := fam₂) (log := [e₂])).2
            rw [List.nil_append]
            rw [h]
            rfl
          by_cases hb : bad q = true
          · rw [hlog₁, hlog₂]
            simp [eagerDetWideEntryGood, hb, e₁, e₂]
          · have hbFalse : bad q = false := by
              cases hbad : bad q <;> simp [hbad] at hb ⊢
            have hAns : a₁ = a₂ := hagree q hbFalse
            rw [hlog₁, hlog₂]
            have hih := ih a₂
            simp [eagerDetWideEntryGood, hbFalse, e₁, e₂, a₁, a₂, hAns] at hih ⊢
            exact hih

/-- Local version of `eagerDetExec_value_log_eq_of_spongeAnswer_eq`.

It is enough for the two fixed sponge families to agree on the DS queries that the *left*
execution actually makes.  This is the reusable deterministic-causality brick needed for
deferred-decision arguments: changing an oracle table entry that is not read by a prefix cannot
change that prefix. -/
lemma eagerDetExec_value_log_eq_of_spongeAnswer_eq_on_left_log {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (hagree : ∀ q,
      (⟨Sum.inr q, spongeAnswer fam₁ q⟩ :
        Sigma ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ∈
          (eagerDetExec oa (fam₁, log)).2.2 →
        spongeAnswer fam₁ q = spongeAnswer fam₂ q) :
    (eagerDetExec oa (fam₁, log)).1 = (eagerDetExec oa (fam₂, log)).1 ∧
      (eagerDetExec oa (fam₁, log)).2.2 = (eagerDetExec oa (fam₂, log)).2.2 := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x =>
      simp only [eagerDetExec, simulateQ_pure]
      constructor <;> rfl
  | query_bind t mx ih =>
      match t with
      | Sum.inl q => exact PEmpty.elim q
      | Sum.inr q =>
          let a₁ := spongeAnswer fam₁ q
          let entry₁ : Sigma ([]ₒ + duplexSpongeChallengeOracle StmtIn U) := ⟨Sum.inr q, a₁⟩
          have hfullPair :
              eagerDetExec (liftM (OracleSpec.query (Sum.inr q)) >>= mx) (fam₁, log) =
                eagerDetExec (mx a₁) (fam₁, log ++ [entry₁]) := by
            simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
              eagerDetImpl, StateT.run_bind, monadLift_self, a₁, entry₁]
            rfl
          have hfull :
              (eagerDetExec (liftM (OracleSpec.query (Sum.inr q)) >>= mx) (fam₁, log)).2.2 =
                (eagerDetExec (mx a₁) (fam₁, log ++ [entry₁])).2.2 := by
            exact congrArg (fun z => z.2.2) hfullPair
          have hlogAppend := eagerDetExec_log_eq_append
            (StmtIn := StmtIn) (U := U) (oa := mx a₁) (st := (fam₁, log ++ [entry₁]))
          obtain ⟨suffix, hsuffix, _⟩ := hlogAppend
          have hmemCurrentCont :
              entry₁ ∈ (eagerDetExec (mx a₁) (fam₁, log ++ [entry₁])).2.2 := by
            rw [hsuffix]
            simp [entry₁]
          have hmemCurrentFull :
              entry₁ ∈
                (eagerDetExec (liftM (OracleSpec.query (Sum.inr q)) >>= mx)
                  (fam₁, log)).2.2 := by
            rw [hfull]
            exact hmemCurrentCont
          have hqagree : spongeAnswer fam₁ q = spongeAnswer fam₂ q := by
            exact hagree q hmemCurrentFull
          simp only [eagerDetExec, simulateQ_query_bind, OracleQuery.input_query,
            eagerDetImpl, StateT.run_bind, monadLift_self]
          change
            (eagerDetExec (mx (spongeAnswer fam₁ q))
                (fam₁, log ++ [⟨Sum.inr q, spongeAnswer fam₁ q⟩])).1 =
              (eagerDetExec (mx (spongeAnswer fam₂ q))
                (fam₂, log ++ [⟨Sum.inr q, spongeAnswer fam₂ q⟩])).1 ∧
            (eagerDetExec (mx (spongeAnswer fam₁ q))
                (fam₁, log ++ [⟨Sum.inr q, spongeAnswer fam₁ q⟩])).2.2 =
              (eagerDetExec (mx (spongeAnswer fam₂ q))
                (fam₂, log ++ [⟨Sum.inr q, spongeAnswer fam₂ q⟩])).2.2
          rw [hqagree]
          exact ih (spongeAnswer fam₂ q)
            (log ++ [⟨Sum.inr q, spongeAnswer fam₂ q⟩])
            (fun q' hmem => by
              apply hagree q'
              rw [hfull]
              simpa [a₁, entry₁, hqagree] using hmem)

/-- If the left deterministic eager run never reaches a query in the deferred-decision set `bad`,
then agreement outside `bad` is enough to identify the entire returned value and log.

This is the "full good prefix" companion to `eagerDetExec_takeWhile_good_eq`: it lets the
Lemma-5.8 prover/verifier concatenation argument pass from the prover to the verifier when the
prover side did not consume the freshly re-randomized oracle point. -/
lemma eagerDetExec_value_log_eq_of_takeWhile_good_eq_self {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (hagree : ∀ q, bad q = false → spongeAnswer fam₁ q = spongeAnswer fam₂ q)
    (hfull :
      List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
          (eagerDetExec oa (fam₁, log)).2.2 =
        (eagerDetExec oa (fam₁, log)).2.2) :
    (eagerDetExec oa (fam₁, log)).1 = (eagerDetExec oa (fam₂, log)).1 ∧
      (eagerDetExec oa (fam₁, log)).2.2 = (eagerDetExec oa (fam₂, log)).2.2 := by
  refine eagerDetExec_value_log_eq_of_spongeAnswer_eq_on_left_log
    (StmtIn := StmtIn) (U := U) oa fam₁ fam₂ log ?_
  intro q hmem
  have hmemTake :
      (⟨Sum.inr q, spongeAnswer fam₁ q⟩ :
        Sigma ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ∈
        List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
          (eagerDetExec oa (fam₁, log)).2.2 := by
    rw [hfull]
    exact hmem
  have hgood := mem_takeWhile_imp_bool hmemTake
  have hb : bad q = false := by
    unfold eagerDetWideEntryGood at hgood
    cases hbad : bad q <;> simp [hbad] at hgood ⊢
  exact hagree q hb

end EagerDeterminism

/-- Deterministic prover execution for the sponge-side Lemma-5.8 experiment under a fixed sampled
oracle family `fam = (h, p, p⁻¹)`. -/
noncomputable def spongeDetProverExec
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier) :
    (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
      ((D_𝔖 StmtIn U).Carrier ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :=
  eagerDetExec maliciousProver (fam, [])

/-- Deterministic verifier execution for the sponge-side Lemma-5.8 experiment under a fixed sampled
oracle family `fam = (h, p, p⁻¹)`. -/
noncomputable def spongeDetVerifierExec
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier) :
    Option StmtOut ×
      ((D_𝔖 StmtIn U).Carrier ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :=
  let proverExec := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam
  let stmtIn := proverExec.1.1
  let proof := proverExec.1.2
  eagerDetExec (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof) (proverExec.2.1, [])

/-- Deterministic projected trace pair produced by the sponge-side Lemma-5.8 experiment under a
fixed sampled oracle family `fam = (h, p, p⁻¹)`. -/
noncomputable def spongeDetTrace
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  let proverExec := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam
  let verifierExec := spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam
  (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) proverExec.2.2,
    lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) verifierExec.2.2)

/-- The unprojected wide log behind `spongeDetTrace`: prover wide log followed by verifier wide
log.  Keeping this as a named object lets prefix-causality lemmas work before projection, then
transport through `lemma5_8ProjectTraceLog`. -/
noncomputable def spongeDetFullWideLog
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier) :
    QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U) :=
  let proverExec := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam
  let verifierExec := spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam
  proverExec.2.2 ++ verifierExec.2.2

/-- If two eager sponge realizations agree outside a bad query set, then the complete
prover-then-verifier wide log has the same prefix before the first bad query.

The small wrinkle is that the verifier program depends on the prover output.  If the prover log
already hits a bad query, `takeWhile` stops before the verifier.  If it does not, the prover value
and log agree by `eagerDetExec_value_log_eq_of_takeWhile_good_eq_self`, so the verifier programs
are identical and the one-computation prefix lemma applies again. -/
lemma spongeDetFullWideLog_takeWhile_good_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (hagree : ∀ q, bad q = false → spongeAnswer fam₁ q = spongeAnswer fam₂ q) :
    List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
        (spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
          (U := U) (δ := δ) V maliciousProver fam₁) =
      List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
        (spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
          (U := U) (δ := δ) V maliciousProver fam₂) := by
  classical
  let good := eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad
  let p₁ := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam₁
  let p₂ := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam₂
  let v₁ := spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁
  let v₂ := spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₂
  have hpTake : List.takeWhile good p₁.2.2 = List.takeWhile good p₂.2.2 := by
    simpa [good, p₁, p₂, spongeDetProverExec] using
      (eagerDetExec_takeWhile_good_eq (StmtIn := StmtIn) (U := U)
        (oa := maliciousProver) fam₁ fam₂ bad hagree)
  by_cases hfull₁ : List.takeWhile good p₁.2.2 = p₁.2.2
  · have hProverEq :
        p₁.1 = p₂.1 ∧ p₁.2.2 = p₂.2.2 := by
      simpa [good, p₁, p₂, spongeDetProverExec] using
        (eagerDetExec_value_log_eq_of_takeWhile_good_eq_self
          (StmtIn := StmtIn) (U := U) (oa := maliciousProver)
          fam₁ fam₂ [] bad hagree (by simpa [good, p₁, spongeDetProverExec] using hfull₁))
    have hfull₂ : List.takeWhile good p₂.2.2 = p₂.2.2 := by
      rw [← hProverEq.2, hfull₁]
    have hp₁Carrier : p₁.2.1 = fam₁ := by
      simpa [p₁, spongeDetProverExec] using
        (eagerDetExec_carrier_eq (StmtIn := StmtIn) (U := U)
          (oa := maliciousProver) (st := (fam₁, [])))
    have hp₂Carrier : p₂.2.1 = fam₂ := by
      simpa [p₂, spongeDetProverExec] using
        (eagerDetExec_carrier_eq (StmtIn := StmtIn) (U := U)
          (oa := maliciousProver) (st := (fam₂, [])))
    have hvTake : List.takeWhile good v₁.2.2 = List.takeWhile good v₂.2.2 := by
      have hvRaw :=
        eagerDetExec_takeWhile_good_eq (StmtIn := StmtIn) (U := U)
          (oa := runForwardVerifierWide (oSpec := []ₒ) δ V p₁.1.1 p₁.1.2)
          fam₁ fam₂ bad hagree
      simpa [good, v₁, v₂, spongeDetVerifierExec, p₁, p₂, hp₁Carrier, hp₂Carrier,
        hProverEq.1] using hvRaw
    change List.takeWhile good (p₁.2.2 ++ v₁.2.2) =
      List.takeWhile good (p₂.2.2 ++ v₂.2.2)
    rw [takeWhile_append_of_eq_self hfull₁, takeWhile_append_of_eq_self hfull₂,
      hProverEq.2, hvTake]
  · have hagreeSymm : ∀ q, bad q = false → spongeAnswer fam₂ q = spongeAnswer fam₁ q := by
      intro q hb
      rw [hagree q hb]
    have hstop₂ : List.takeWhile good p₂.2.2 ≠ p₂.2.2 := by
      intro hfull₂
      have hProverEq₂ :
          p₂.1 = p₁.1 ∧ p₂.2.2 = p₁.2.2 := by
        simpa [good, p₁, p₂, spongeDetProverExec] using
          (eagerDetExec_value_log_eq_of_takeWhile_good_eq_self
            (StmtIn := StmtIn) (U := U) (oa := maliciousProver)
            fam₂ fam₁ [] bad hagreeSymm
            (by simpa [good, p₂, spongeDetProverExec] using hfull₂))
      apply hfull₁
      rw [← hProverEq₂.2, hfull₂]
    change List.takeWhile good (p₁.2.2 ++ v₁.2.2) =
      List.takeWhile good (p₂.2.2 ++ v₂.2.2)
    rw [takeWhile_append_of_ne_self hfull₁, takeWhile_append_of_ne_self hstop₂, hpTake]

set_option maxHeartbeats 400000

/-- If two eager sponge realizations agree outside a bad query set, then the complete
prover-then-verifier wide logs stop in lockstep at the same first bad query domain.

This is the deterministic deferred-decision causality lemma used by the sponge-side atom
invariants: changing answers on the charged domain cannot alter the transcript before that
domain is first queried. -/
lemma spongeDetFullWideLog_first_bad_domain_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (hagree : ∀ q, bad q = false → spongeAnswer fam₁ q = spongeAnswer fam₂ q) :
    let good := eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad
    let log₁ := spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁
    let log₂ := spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₂
    List.takeWhile good log₁ = List.takeWhile good log₂ ∧
      ((List.takeWhile good log₁).length < log₁.length ↔
        (List.takeWhile good log₂).length < log₂.length) ∧
      (∀ (h₁ : (List.takeWhile good log₁).length < log₁.length)
          (h₂ : (List.takeWhile good log₂).length < log₂.length),
        log₁[(List.takeWhile good log₁).length].1 =
          log₂[(List.takeWhile good log₂).length].1) := by
  classical
  let good := eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad
  let p₁ := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam₁
  let p₂ := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam₂
  let v₁ := spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁
  let v₂ := spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₂
  have htake :
      List.takeWhile good
          (spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁) =
        List.takeWhile good
          (spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₂) := by
    simpa [good] using
      (spongeDetFullWideLog_takeWhile_good_eq (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁ fam₂ bad hagree)
  have hpRaw :=
    eagerDetExec_first_bad_domain_eq (StmtIn := StmtIn) (U := U)
      (oa := maliciousProver) fam₁ fam₂ bad hagree
  by_cases hfull₁ : List.takeWhile good p₁.2.2 = p₁.2.2
  · have hProverEq :
        p₁.1 = p₂.1 ∧ p₁.2.2 = p₂.2.2 := by
      simpa [good, p₁, p₂, spongeDetProverExec] using
        (eagerDetExec_value_log_eq_of_takeWhile_good_eq_self
          (StmtIn := StmtIn) (U := U) (oa := maliciousProver)
          fam₁ fam₂ [] bad hagree (by simpa [good, p₁, spongeDetProverExec] using hfull₁))
    have hfull₂ : List.takeWhile good p₂.2.2 = p₂.2.2 := by
      rw [← hProverEq.2, hfull₁]
    have hp₁Carrier : p₁.2.1 = fam₁ := by
      simpa [p₁, spongeDetProverExec] using
        (eagerDetExec_carrier_eq (StmtIn := StmtIn) (U := U)
          (oa := maliciousProver) (st := (fam₁, [])))
    have hp₂Carrier : p₂.2.1 = fam₂ := by
      simpa [p₂, spongeDetProverExec] using
        (eagerDetExec_carrier_eq (StmtIn := StmtIn) (U := U)
          (oa := maliciousProver) (st := (fam₂, [])))
    have hvRaw :=
      eagerDetExec_first_bad_domain_eq (StmtIn := StmtIn) (U := U)
        (oa := runForwardVerifierWide (oSpec := []ₒ) δ V p₁.1.1 p₁.1.2)
        fam₁ fam₂ bad hagree
    have hvStop :
        ((List.takeWhile good v₁.2.2).length < v₁.2.2.length ↔
          (List.takeWhile good v₂.2.2).length < v₂.2.2.length) := by
      simpa [good, v₁, v₂, spongeDetVerifierExec, p₁, p₂, hp₁Carrier, hp₂Carrier,
        hProverEq.1] using hvRaw.2.1
    have hvDomain :
        ∀ (hv₁ : (List.takeWhile good v₁.2.2).length < v₁.2.2.length)
          (hv₂ : (List.takeWhile good v₂.2.2).length < v₂.2.2.length),
          v₁.2.2[(List.takeWhile good v₁.2.2).length].1 =
            v₂.2.2[(List.takeWhile good v₂.2.2).length].1 := by
      intro hv₁ hv₂
      have hv₁raw :
          (List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
              (eagerDetExec (runForwardVerifierWide (oSpec := []ₒ) δ V p₁.1.1 p₁.1.2)
                (fam₁, [])).2.2).length <
            (eagerDetExec (runForwardVerifierWide (oSpec := []ₒ) δ V p₁.1.1 p₁.1.2)
                (fam₁, [])).2.2.length := by
        simpa [good, v₁, spongeDetVerifierExec, p₁, hp₁Carrier] using hv₁
      have hv₂raw :
          (List.takeWhile (eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad)
              (eagerDetExec (runForwardVerifierWide (oSpec := []ₒ) δ V p₁.1.1 p₁.1.2)
                (fam₂, [])).2.2).length <
            (eagerDetExec (runForwardVerifierWide (oSpec := []ₒ) δ V p₁.1.1 p₁.1.2)
                (fam₂, [])).2.2.length := by
        simpa [good, v₂, spongeDetVerifierExec, p₁, p₂, hp₂Carrier, hProverEq.1] using hv₂
      have hdom := hvRaw.2.2 hv₁raw hv₂raw
      simpa [good, v₁, v₂, spongeDetVerifierExec, p₁, p₂, hp₁Carrier, hp₂Carrier,
        hProverEq.1] using hdom
    refine ⟨htake, ?_, ?_⟩
    · change
        (List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length <
            (p₁.2.2 ++ v₁.2.2).length ↔
          (List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length <
            (p₂.2.2 ++ v₂.2.2).length
      rw [takeWhile_append_full_length_lt_iff hfull₁,
        takeWhile_append_full_length_lt_iff hfull₂]
      exact hvStop
    · intro h₁ h₂
      change
        (p₁.2.2 ++ v₁.2.2)[(List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length].1 =
          (p₂.2.2 ++ v₂.2.2)[(List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length].1
      have hv₁ : (List.takeWhile good v₁.2.2).length < v₁.2.2.length :=
        (takeWhile_append_full_length_lt_iff hfull₁).mp h₁
      have hv₂ : (List.takeWhile good v₂.2.2).length < v₂.2.2.length :=
        (takeWhile_append_full_length_lt_iff hfull₂).mp h₂
      have hidx₁ :
          (List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length =
            p₁.2.2.length + (List.takeWhile good v₁.2.2).length := by
        rw [takeWhile_append_of_eq_self hfull₁, List.length_append]
      have hidx₂ :
          (List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length =
            p₂.2.2.length + (List.takeWhile good v₂.2.2).length := by
        rw [takeWhile_append_of_eq_self hfull₂, List.length_append]
      have hfullLen₁ :
          (List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length <
            (p₁.2.2 ++ v₁.2.2).length := by
        rw [hidx₁]
        simp only [List.length_append]
        omega
      have hfullLen₂ :
          (List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length <
            (p₂.2.2 ++ v₂.2.2).length := by
        rw [hidx₂]
        simp only [List.length_append]
        omega
      have hget₁ := getElem?_takeWhile_append_of_eq_self
        (p := good) (l₁ := p₁.2.2) (l₂ := v₁.2.2) hfull₁
      have hget₂ := getElem?_takeWhile_append_of_eq_self
        (p := good) (l₁ := p₂.2.2) (l₂ := v₂.2.2) hfull₂
      rw [List.getElem?_eq_getElem hfullLen₁, List.getElem?_eq_getElem hv₁] at hget₁
      rw [List.getElem?_eq_getElem hfullLen₂, List.getElem?_eq_getElem hv₂] at hget₂
      injection hget₁ with hentry₁
      injection hget₂ with hentry₂
      exact (congrArg Sigma.fst hentry₁).trans
        ((hvDomain hv₁ hv₂).trans (congrArg Sigma.fst hentry₂).symm)
  · have hpStop₁ : (List.takeWhile good p₁.2.2).length < p₁.2.2.length :=
      length_takeWhile_lt_of_ne_self_bool hfull₁
    have hpStop₂ : (List.takeWhile good p₂.2.2).length < p₂.2.2.length := by
      have hiff : ((List.takeWhile good p₁.2.2).length < p₁.2.2.length ↔
          (List.takeWhile good p₂.2.2).length < p₂.2.2.length) := by
        simpa [good, p₁, p₂, spongeDetProverExec] using hpRaw.2.1
      exact hiff.mp hpStop₁
    have hstop₂ : List.takeWhile good p₂.2.2 ≠ p₂.2.2 := by
      intro hfull₂
      exact (not_lt_of_ge (by rw [hfull₂])) hpStop₂
    have hpDomain :
        p₁.2.2[(List.takeWhile good p₁.2.2).length].1 =
          p₂.2.2[(List.takeWhile good p₂.2.2).length].1 := by
      simpa [good, p₁, p₂, spongeDetProverExec] using hpRaw.2.2 hpStop₁ hpStop₂
    refine ⟨htake, ?_, ?_⟩
    · change
        (List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length <
            (p₁.2.2 ++ v₁.2.2).length ↔
          (List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length <
            (p₂.2.2 ++ v₂.2.2).length
      have hleft :
          (List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length <
            (p₁.2.2 ++ v₁.2.2).length := by
        exact lt_of_lt_of_le (takeWhile_append_stops_left_length_lt hfull₁)
          (by simp only [List.length_append]; omega)
      have hright :
          (List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length <
            (p₂.2.2 ++ v₂.2.2).length := by
        exact lt_of_lt_of_le (takeWhile_append_stops_left_length_lt hstop₂)
          (by simp only [List.length_append]; omega)
      constructor <;> intro _ <;> assumption
    · intro h₁ h₂
      change
        (p₁.2.2 ++ v₁.2.2)[(List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length].1 =
          (p₂.2.2 ++ v₂.2.2)[(List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length].1
      have hidx₁ :
          (List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length =
            (List.takeWhile good p₁.2.2).length := by
        rw [takeWhile_append_of_ne_self hfull₁]
      have hidx₂ :
          (List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length =
            (List.takeWhile good p₂.2.2).length := by
        rw [takeWhile_append_of_ne_self hstop₂]
      have hfullLen₁ :
          (List.takeWhile good (p₁.2.2 ++ v₁.2.2)).length <
            (p₁.2.2 ++ v₁.2.2).length := by
        rw [hidx₁]
        simp only [List.length_append]
        omega
      have hfullLen₂ :
          (List.takeWhile good (p₂.2.2 ++ v₂.2.2)).length <
            (p₂.2.2 ++ v₂.2.2).length := by
        rw [hidx₂]
        simp only [List.length_append]
        omega
      have hget₁ := getElem?_takeWhile_append_of_ne_self
        (p := good) (l₁ := p₁.2.2) (l₂ := v₁.2.2) hfull₁
      have hget₂ := getElem?_takeWhile_append_of_ne_self
        (p := good) (l₁ := p₂.2.2) (l₂ := v₂.2.2) hstop₂
      rw [List.getElem?_eq_getElem hfullLen₁, List.getElem?_eq_getElem hpStop₁] at hget₁
      rw [List.getElem?_eq_getElem hfullLen₂, List.getElem?_eq_getElem hpStop₂] at hget₂
      injection hget₁ with hentry₁
      injection hget₂ with hentry₂
      exact (congrArg Sigma.fst hentry₁).trans
        (hpDomain.trans (congrArg Sigma.fst hentry₂).symm)

/-- Projecting a `[]ₒ + DS` log to the DS component preserves length, because the empty-oracle
summand has no queries. -/
lemma lemma5_8ProjectTraceLog_length
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) log).length = log.length := by
  induction log with
  | nil =>
      rfl
  | cons entry rest ih =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl q => exact PEmpty.elim q
      | inr q =>
          change (⟨q, rng⟩ :: lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) rest).length =
            (⟨Sum.inr q, rng⟩ ::
              (rest : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))).length
          rw [List.length_cons, List.length_cons, ih]

/-- Domain projection at a valid index. -/
lemma lemma5_8ProjectTraceLog_getElem_domain
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {i : ℕ} (hi : i < (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) log).length) :
    ∃ hfull : i < log.length,
      (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) log)[i].1 =
        match log[i].1 with
        | .inl q => PEmpty.elim q
        | .inr q => q := by
  induction log generalizing i with
  | nil =>
      cases hi
  | cons entry rest ih =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl q =>
          exact PEmpty.elim q
      | inr q =>
          cases i with
          | zero =>
              refine ⟨Nat.succ_pos rest.length, ?_⟩
              rfl
          | succ i =>
              have hiRest :
                  i < (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) rest).length :=
                Nat.lt_of_succ_lt_succ hi
              rcases ih hiRest with ⟨hfull, hdom⟩
              refine ⟨Nat.succ_lt_succ hfull, ?_⟩
              exact hdom

/-- Projecting the full wide eager log gives exactly the concatenated narrow trace used by
Lemma 5.8 bad events. -/
lemma spongeDetTrace_append_eq_project_fullWideLog
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier) :
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2 =
    lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U)
      (spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam) := by
  simp [spongeDetTrace, spongeDetFullWideLog, lemma5_8ProjectTraceLog, List.filterMap_append]

/-- Projected DS traces inherit the deterministic prefix-causality theorem from the full wide log. -/
lemma spongeDetTrace_append_takeWhile_good_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (hagree : ∀ q, bad q = false → spongeAnswer fam₁ q = spongeAnswer fam₂ q) :
    let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
    let log₁ :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₁).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₁).2
    let log₂ :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₂).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₂).2
    List.takeWhile good log₁ = List.takeWhile good log₂ := by
  classical
  have hwide :=
    spongeDetFullWideLog_takeWhile_good_eq (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁ fam₂ bad hagree
  have hproj := congrArg (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U)) hwide
  rw [lemma5_8ProjectTraceLog_takeWhile_eagerDetWideEntryGood,
    lemma5_8ProjectTraceLog_takeWhile_eagerDetWideEntryGood] at hproj
  rw [← spongeDetTrace_append_eq_project_fullWideLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₁,
    ← spongeDetTrace_append_eq_project_fullWideLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₂] at hproj
  exact hproj

/-- Projected DS traces inherit the first-bad-domain lockstep theorem from the full wide log. -/
lemma spongeDetTrace_append_first_bad_domain_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam₁ fam₂ : (D_𝔖 StmtIn U).Carrier)
    (bad : (duplexSpongeChallengeOracle StmtIn U).Domain → Bool)
    (hagree : ∀ q, bad q = false → spongeAnswer fam₁ q = spongeAnswer fam₂ q) :
    let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
    let log₁ :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₁).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₁).2
    let log₂ :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₂).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₂).2
    List.takeWhile good log₁ = List.takeWhile good log₂ ∧
      ((List.takeWhile good log₁).length < log₁.length ↔
        (List.takeWhile good log₂).length < log₂.length) ∧
      (∀ (h₁ : (List.takeWhile good log₁).length < log₁.length)
          (h₂ : (List.takeWhile good log₂).length < log₂.length),
        log₁[(List.takeWhile good log₁).length].1 =
          log₂[(List.takeWhile good log₂).length].1) := by
  classical
  let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
  let wideGood := eagerDetWideEntryGood (StmtIn := StmtIn) (U := U) bad
  let log₁ :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₁).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₁).2
  let log₂ :=
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₂).1 ++
    (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver fam₂).2
  let wide₁ := spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁
  let wide₂ := spongeDetFullWideLog (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₂
  have htake :=
    spongeDetTrace_append_takeWhile_good_eq (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁ fam₂ bad hagree
  change List.takeWhile good log₁ = List.takeWhile good log₂ at htake
  have hwide :=
    spongeDetFullWideLog_first_bad_domain_eq (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam₁ fam₂ bad hagree
  change List.takeWhile wideGood wide₁ = List.takeWhile wideGood wide₂ ∧
      ((List.takeWhile wideGood wide₁).length < wide₁.length ↔
        (List.takeWhile wideGood wide₂).length < wide₂.length) ∧
      (∀ (h₁ : (List.takeWhile wideGood wide₁).length < wide₁.length)
          (h₂ : (List.takeWhile wideGood wide₂).length < wide₂.length),
        wide₁[(List.takeWhile wideGood wide₁).length].1 =
          wide₂[(List.takeWhile wideGood wide₂).length].1) at hwide
  have hproj₁ :
      log₁ = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₁ := by
    change log₁ = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₁
    exact spongeDetTrace_append_eq_project_fullWideLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₁
  have hproj₂ :
      log₂ = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₂ := by
    change log₂ = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₂
    exact spongeDetTrace_append_eq_project_fullWideLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) V maliciousProver fam₂
  have htakeLen₁ :
      (List.takeWhile good log₁).length = (List.takeWhile wideGood wide₁).length := by
    have hprojTake :=
      lemma5_8ProjectTraceLog_takeWhile_eagerDetWideEntryGood
        (StmtIn := StmtIn) (U := U) bad wide₁
    have hlen := congrArg List.length hprojTake
    rw [lemma5_8ProjectTraceLog_length (StmtIn := StmtIn) (U := U)] at hlen
    rw [← hproj₁] at hlen
    change (List.takeWhile wideGood wide₁).length =
      (List.takeWhile good log₁).length at hlen
    exact hlen.symm
  have htakeLen₂ :
      (List.takeWhile good log₂).length = (List.takeWhile wideGood wide₂).length := by
    have hprojTake :=
      lemma5_8ProjectTraceLog_takeWhile_eagerDetWideEntryGood
        (StmtIn := StmtIn) (U := U) bad wide₂
    have hlen := congrArg List.length hprojTake
    rw [lemma5_8ProjectTraceLog_length (StmtIn := StmtIn) (U := U)] at hlen
    rw [← hproj₂] at hlen
    change (List.takeWhile wideGood wide₂).length =
      (List.takeWhile good log₂).length at hlen
    exact hlen.symm
  have hlogLen₁ : log₁.length = wide₁.length := by
    rw [hproj₁, lemma5_8ProjectTraceLog_length (StmtIn := StmtIn) (U := U)]
  have hlogLen₂ : log₂.length = wide₂.length := by
    rw [hproj₂, lemma5_8ProjectTraceLog_length (StmtIn := StmtIn) (U := U)]
  refine ⟨htake, ?_, ?_⟩
  · constructor
    · intro hn₁
      have hw₁ : (List.takeWhile wideGood wide₁).length < wide₁.length := by
        rw [← htakeLen₁, ← hlogLen₁]
        exact hn₁
      have hw₂ := hwide.2.1.mp hw₁
      rw [htakeLen₂, hlogLen₂]
      exact hw₂
    · intro hn₂
      have hw₂ : (List.takeWhile wideGood wide₂).length < wide₂.length := by
        rw [← htakeLen₂, ← hlogLen₂]
        exact hn₂
      have hw₁ := hwide.2.1.mpr hw₂
      rw [htakeLen₁, hlogLen₁]
      exact hw₁
  · intro hn₁ hn₂
    have hw₁ : (List.takeWhile wideGood wide₁).length < wide₁.length := by
      rw [← htakeLen₁, ← hlogLen₁]
      exact hn₁
    have hw₂ : (List.takeWhile wideGood wide₂).length < wide₂.length := by
      rw [← htakeLen₂, ← hlogLen₂]
      exact hn₂
    have hdomWide := hwide.2.2 hw₁ hw₂
    let proj₁ := lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₁
    let proj₂ := lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₂
    have hprojLocal₁ : log₁ = proj₁ := by
      change log₁ = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₁
      exact hproj₁
    have hprojLocal₂ : log₂ = proj₂ := by
      change log₂ = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₂
      exact hproj₂
    have htakeLenLocal₁ :
        (List.takeWhile good proj₁).length = (List.takeWhile wideGood wide₁).length := by
      rw [← hprojLocal₁]
      exact htakeLen₁
    have htakeLenLocal₂ :
        (List.takeWhile good proj₂).length = (List.takeWhile wideGood wide₂).length := by
      rw [← hprojLocal₂]
      exact htakeLen₂
    have hidx₁ :
        (List.takeWhile wideGood wide₁).length < proj₁.length := by
      change (List.takeWhile wideGood wide₁).length <
        (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₁).length
      rw [lemma5_8ProjectTraceLog_length (StmtIn := StmtIn) (U := U)]
      exact hw₁
    have hidx₂ :
        (List.takeWhile wideGood wide₂).length < proj₂.length := by
      change (List.takeWhile wideGood wide₂).length <
        (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) wide₂).length
      rw [lemma5_8ProjectTraceLog_length (StmtIn := StmtIn) (U := U)]
      exact hw₂
    obtain ⟨_, hdom₁⟩ :=
      lemma5_8ProjectTraceLog_getElem_domain (StmtIn := StmtIn) (U := U) wide₁ hidx₁
    obtain ⟨_, hdom₂⟩ :=
      lemma5_8ProjectTraceLog_getElem_domain (StmtIn := StmtIn) (U := U) wide₂ hidx₂
    change proj₁[(List.takeWhile wideGood wide₁).length].1 =
      match wide₁[(List.takeWhile wideGood wide₁).length].1 with
      | .inl q => PEmpty.elim q
      | .inr q => q at hdom₁
    change proj₂[(List.takeWhile wideGood wide₂).length].1 =
      match wide₂[(List.takeWhile wideGood wide₂).length].1 with
      | .inl q => PEmpty.elim q
      | .inr q => q at hdom₂
    calc
      log₁[(List.takeWhile good log₁).length].1
          = proj₁[(List.takeWhile wideGood wide₁).length].1 := by
            have hget : log₁[(List.takeWhile good log₁).length]? =
                proj₁[(List.takeWhile wideGood wide₁).length]? := by
              rw [hprojLocal₁, htakeLenLocal₁]
            rw [List.getElem?_eq_getElem hn₁, List.getElem?_eq_getElem hidx₁] at hget
            injection hget with hentry
            exact congrArg Sigma.fst hentry
      _ = match wide₁[(List.takeWhile wideGood wide₁).length].1 with
          | .inl q => PEmpty.elim q
          | .inr q => q := hdom₁
      _ = match wide₂[(List.takeWhile wideGood wide₂).length].1 with
          | .inl q => PEmpty.elim q
          | .inr q => q := by
            rw [hdomWide]
      _ = proj₂[(List.takeWhile wideGood wide₂).length].1 := hdom₂.symm
      _ = log₂[(List.takeWhile good log₂).length].1 := by
            have hget : log₂[(List.takeWhile good log₂).length]? =
                proj₂[(List.takeWhile wideGood wide₂).length]? := by
              rw [hprojLocal₂, htakeLenLocal₂]
            rw [List.getElem?_eq_getElem hn₂, List.getElem?_eq_getElem hidx₂] at hget
            injection hget with hentry
            exact (congrArg Sigma.fst hentry).symm

/-- The sponge-side Lemma-5.8 experiment is a deterministic trace map over the sampled eager
oracle family `fam = (h, p, p⁻¹)`. -/
lemma lemma5_8SpongeTraceDist_eq_map_spongeDetTrace
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
      (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
      (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver
      = spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver <$> (D_𝔖 StmtIn U).sample := by
  rw [lemma5_8SpongeTraceDist, lemma5_8ProjectedTraceDistAbortable]
  simp only [monad_norm]
  refine bind_congr fun fam => ?_
  have hprover :
      (simulateQ (lemma5_8CombinedImpl (StmtIn := StmtIn) (U := U)
        (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl))) maliciousProver).run (fam, [])
        = pure (some (spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            maliciousProver fam).1,
            (spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
              maliciousProver fam).2) := by
    simpa [spongeDetProverExec] using
      (eagerRun_eq_pure (StmtIn := StmtIn) (U := U) (oa := maliciousProver) (st := (fam, [])))
  rw [hprover]
  simp only [pure_bind]
  have hvør :
      (simulateQ (lemma5_8CombinedImpl (StmtIn := StmtIn) (U := U)
        (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl)))
          (runForwardVerifierWide (oSpec := []ₒ) δ V
            (spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
              maliciousProver fam).1.1
            (spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
              maliciousProver fam).1.2)).run
          ((spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
              maliciousProver fam).2.1, [])
        = pure (some (spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
            (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam).1,
            (spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
              (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam).2) := by
    simpa [spongeDetVerifierExec, spongeDetProverExec] using
      (eagerRun_eq_pure (StmtIn := StmtIn) (U := U)
        (oa := runForwardVerifierWide (oSpec := []ₒ) δ V
          (spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            maliciousProver fam).1.1
          (spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            maliciousProver fam).1.2)
        (st := ((spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            maliciousProver fam).2.1, [])))
  rw [hvør]
  simp [spongeDetTrace, spongeDetVerifierExec, spongeDetProverExec]

/-- Probability-level rewrite of the sponge-side Lemma-5.8 experiment through the deterministic
trace map `spongeDetTrace`. -/
lemma probEvent_lemma5_8SpongeTraceDist_eq_map
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (Q : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U) → Prop) :
    Pr[ Q | lemma5_8SpongeTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
      (pSpec := pSpec) (U := U) (δ := δ) (initSponge := (D_𝔖 StmtIn U).sample)
      (implSponge := (D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      = Pr[ Q ∘ spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
          (U := U) (δ := δ) V maliciousProver | (D_𝔖 StmtIn U).sample] := by
  rw [lemma5_8SpongeTraceDist_eq_map_spongeDetTrace
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) (δ := δ)
    V maliciousProver]
  rw [probEvent_map]


/-- Every raw projected entry of the deterministic sponge execution is answered by the concrete
eager oracle family `fam = (h,p)`. -/
lemma spongeDetTrace_append_consistent
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier) :
    ∀ e ∈
        (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
        (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2,
      e.2 = spongeAnswer fam e.1 := by
  intro e he
  let proverExec := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam
  let verifierExec := spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam
  let trP : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) proverExec.2.2
  let trV : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) verifierExec.2.2
  have hpr :
      (some proverExec.1, proverExec.2) ∈ support
        (((simulateQ (lemma5_8CombinedImpl
          (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl))) maliciousProver).run).run
            (fam, [])) := by
    rw [eagerRun_eq_pure (StmtIn := StmtIn) (U := U) (oa := maliciousProver) (st := (fam, []))]
    simp [proverExec, spongeDetProverExec]
  have hProver := spongeConsistent_of_mem_support (StmtIn := StmtIn) (U := U)
    (oa := maliciousProver) (st := (fam, [])) hpr
  have hProverCons : ∀ e ∈ proverExec.2.2, wideSpongeConsistent fam e := by
    intro e he
    exact (hProver.2 e he).resolve_left (by simp)
  have htrP : ∀ e ∈ trP, e.2 = spongeAnswer fam e.1 :=
    projectTraceLog_spongeConsistent (StmtIn := StmtIn) (U := U) fam proverExec.2.2 hProverCons
  have hvr :
      (some verifierExec.1, verifierExec.2) ∈ support
        (((simulateQ (lemma5_8CombinedImpl
          (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl)))
            (runForwardVerifierWide (oSpec := []ₒ) δ V proverExec.1.1 proverExec.1.2)).run).run
              (proverExec.2.1, [])) := by
    rw [eagerRun_eq_pure (StmtIn := StmtIn) (U := U)
      (oa := runForwardVerifierWide (oSpec := []ₒ) δ V proverExec.1.1 proverExec.1.2)
      (st := (proverExec.2.1, []))]
    simp [verifierExec, spongeDetVerifierExec, proverExec, spongeDetProverExec]
  have hVerif := spongeConsistent_of_mem_support (StmtIn := StmtIn) (U := U)
    (oa := runForwardVerifierWide (oSpec := []ₒ) δ V proverExec.1.1 proverExec.1.2)
    (st := (proverExec.2.1, [])) hvr
  have hs : proverExec.2.1 = fam := hProver.1
  have hVerifCons : ∀ e ∈ verifierExec.2.2, wideSpongeConsistent fam e := by
    intro e he
    have htmp : wideSpongeConsistent proverExec.2.1 e :=
      (hVerif.2 e he).resolve_left (by simp)
    rw [hs] at htmp
    exact htmp
  have htrV : ∀ e ∈ trV, e.2 = spongeAnswer fam e.1 :=
    projectTraceLog_spongeConsistent (StmtIn := StmtIn) (U := U) fam verifierExec.2.2 hVerifCons
  have hraw : e ∈ trP ++ trV := by
    simpa [spongeDetTrace, trP, trV, proverExec, verifierExec] using he
  rcases List.mem_append.mp hraw with h | h
  · exact htrP e h
  · exact htrV e h

/-- Every base-trace entry of the deterministic sponge execution is answered by the concrete eager
oracle family `fam = (h,p)`, by replaying the eager support argument through
`eagerRun_eq_pure`. -/
lemma spongeDetTrace_baseTrace_consistent
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier) :
    ∀ e ∈ getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2),
      e.2 = spongeAnswer fam e.1 := by
  intro e he
  let proverExec := spongeDetProverExec (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    maliciousProver fam
  let verifierExec := spongeDetVerifierExec (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ) V maliciousProver fam
  let trP : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) proverExec.2.2
  let trV : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) verifierExec.2.2
  have hpr :
      (some proverExec.1, proverExec.2) ∈ support
        (((simulateQ (lemma5_8CombinedImpl
          (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl))) maliciousProver).run).run
            (fam, [])) := by
    rw [eagerRun_eq_pure (StmtIn := StmtIn) (U := U) (oa := maliciousProver) (st := (fam, []))]
    simp [proverExec, spongeDetProverExec]
  have hProver := spongeConsistent_of_mem_support (StmtIn := StmtIn) (U := U)
    (oa := maliciousProver) (st := (fam, [])) hpr
  have hProverCons : ∀ e ∈ proverExec.2.2, wideSpongeConsistent fam e := by
    intro e he
    exact (hProver.2 e he).resolve_left (by simp)
  have htrP : ∀ e ∈ trP, e.2 = spongeAnswer fam e.1 :=
    projectTraceLog_spongeConsistent (StmtIn := StmtIn) (U := U) fam proverExec.2.2 hProverCons
  have hvr :
      (some verifierExec.1, verifierExec.2) ∈ support
        (((simulateQ (lemma5_8CombinedImpl
          (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl)))
            (runForwardVerifierWide (oSpec := []ₒ) δ V proverExec.1.1 proverExec.1.2)).run).run
              (proverExec.2.1, [])) := by
    rw [eagerRun_eq_pure (StmtIn := StmtIn) (U := U)
      (oa := runForwardVerifierWide (oSpec := []ₒ) δ V proverExec.1.1 proverExec.1.2)
      (st := (proverExec.2.1, []))]
    simp [verifierExec, spongeDetVerifierExec, proverExec, spongeDetProverExec]
  have hVerif := spongeConsistent_of_mem_support (StmtIn := StmtIn) (U := U)
    (oa := runForwardVerifierWide (oSpec := []ₒ) δ V proverExec.1.1 proverExec.1.2)
    (st := (proverExec.2.1, [])) hvr
  have hs : proverExec.2.1 = fam := hProver.1
  have hVerifCons : ∀ e ∈ verifierExec.2.2, wideSpongeConsistent fam e := by
    intro e he
    have htmp : wideSpongeConsistent proverExec.2.1 e :=
      (hVerif.2 e he).resolve_left (by simp)
    simpa [hs] using htmp
  have htrV : ∀ e ∈ trV, e.2 = spongeAnswer fam e.1 :=
    projectTraceLog_spongeConsistent (StmtIn := StmtIn) (U := U) fam verifierExec.2.2 hVerifCons
  have hbase : e ∈ getBaseTrace (trP ++ trV) := by
    simpa [spongeDetTrace, trP, trV, proverExec, verifierExec] using he
  rcases List.mem_append.mp ((getBaseTrace_sublist (StmtIn := StmtIn) (U := U) (trP ++ trV)).subset hbase) with h | h
  · exact htrP e h
  · exact htrV e h

end SpongePermutationGenuineFunction

end BadEventDS

end DuplexSpongeFS
