/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
  # Sequential Composition of Many Oracle Reductions

  This file defines the sequential composition of an arbitrary `m + 1` number of oracle reductions.
  This is defined by iterating the composition of two reductions, as defined in `Append.lean`.

  Ordinary soundness and knowledge soundness are proved for guarded components with bounds
  uniform over deterministic shared oracle states. Knowledge soundness names a computable fold
  of pure transcript-and-output extractors. Per-step error reindexing is given by
  `ProtocolSpec.apply_seqComposeChallengeIdxToSigma_eq_sumElim`. The worst-case
  round-by-round knowledge-soundness interface for guarded chains is
  `Sequential/GuardedRoundByRound.lean`.
  The false fixed-init completeness contracts have been removed. Proved completeness interfaces
  live in `Sequential/Completeness.lean`, `Sequential/GuardedNary.lean`, and
  `Sequential/OracleCompleteness.lean`, with explicit shared-state hypotheses.
-/

@[expose] public section

open ProtocolSpec OracleComp

universe u v

variable {ι : Type} {oSpec : OracleSpec ι}

section Composition

namespace Prover

/-- Sequential composition of provers, defined via iteration of the composition (append) of two
  provers. Specifically, we have the following definitional equalities:
- `seqCompose (m := 0) P = Prover.id`
- `seqCompose (m := m + 1) P = append (P 0) (seqCompose (m := m) P)`

TODO: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
      Prover oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) :=
  match m with
  | 0 => Prover.id
  | _ + 1 => append (P 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => P (Fin.succ i)))

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type) (Wit : Fin 1 → Type) {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin 0) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit P = Prover.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin (m + 1)) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit P =
      append (P 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => P (Fin.succ i))) := rfl

end Prover

namespace Verifier

/-- Sequential composition of verifiers, defined via iteration of the composition (append) of
two verifiers. Specifically, we have the following definitional equalities:
- `seqCompose (m := 0) V = Verifier.id`
- `seqCompose (m := m + 1) V = append (V 0) (seqCompose (m := m) V)`

TODO: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose {m : ℕ} (Stmt : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    Verifier oSpec (Stmt 0) (Stmt (Fin.last m)) (seqCompose pSpec) := match m with
  | 0 => Verifier.id
  | _ + 1 => append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i)))

@[simp]
lemma seqCompose_zero (Stmt : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin 0) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    seqCompose Stmt V = Verifier.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ} (Stmt : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin (m + 1)) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    seqCompose Stmt V = append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i))) := rfl

/-- A deterministic invariant for sequential verification. If each component takes its
designated input state to the next one, the composed verifier takes the first state to the
last. This statement concerns verification only and imposes no honesty on transcripts. -/
theorem seqCompose_run_eq_pure {m : ℕ} (Stmt : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (tr : ∀ i, (pSpec i).FullTranscript) (state : ∀ i, Stmt i)
    (hstep : ∀ i, (V i).run (state i.castSucc) (tr i) = pure (state i.succ)) :
    (seqCompose Stmt V).run (state 0) (FullTranscript.seqCompose tr) =
      pure (state (Fin.last m)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hzero := hstep 0
    simp only [Fin.castSucc_zero] at hzero
    change ((V 0).append (seqCompose (Stmt ∘ Fin.succ) (fun i ↦ V i.succ))).run
      (state 0) (tr 0 ++ₜ FullTranscript.seqCompose (fun i ↦ tr i.succ)) = _
    erw [append_run,
      FullTranscript.append_fst, FullTranscript.append_snd, hzero, pure_bind]
    exact ih (Stmt ∘ Fin.succ) (fun i ↦ V i.succ) (fun i ↦ tr i.succ)
      (fun i ↦ state i.succ) (fun i ↦ hstep i.succ)

/-- Fold pure extractors backwards through a chain of guarded verifier outputs. The empty
chain returns its output witness; every nonempty step uses `GuardedForm.appendExtract`. -/
def seqComposeExtract {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    (e : (i : Fin m) → Stmt i.castSucc → Wit i.succ →
      (pSpec i).FullTranscript → Option (Wit i.castSucc)) :
    Stmt 0 → Wit (Fin.last m) → (ProtocolSpec.seqCompose pSpec).FullTranscript →
      Option (Wit 0) := match m with
  | 0 => fun _ w _ => some w
  | _ + 1 => (G 0).appendExtract (e 0)
      (seqComposeExtract (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => V i.succ)
        (fun i => G i.succ) (fun i => e i.succ))

end Verifier

namespace Extractor.RoundByRound

/-- Intermediate witnesses for a finite chain, retaining each first factor's seam witness. -/
def seqComposeWitMid {m : ℕ} (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ}
    (WitMid : ∀ i, Fin (n i + 1) → Type) : Fin (Fin.vsum n + 1) → Type :=
  match m with
  | 0 => fun _ => Wit 0
  | _ + 1 => Fin.append (WitMid 0)
      (Fin.tail (seqComposeWitMid (Wit ∘ Fin.succ) (fun i => WitMid i.succ))) ∘
        Fin.cast (by simp only [Fin.vsum_succ, Function.comp_def]; omega)

/-- Fold round-by-round extractors along the guarded outputs, with the identity at the end. -/
def seqCompose {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    {WitMid : ∀ i, Fin (n i + 1) → Type}
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Wit i.succ) (pSpec i) (WitMid i)) :
    Extractor.RoundByRound oSpec (Stmt 0) (Wit 0) (Wit (Fin.last m))
      (ProtocolSpec.seqCompose pSpec) (seqComposeWitMid Wit WitMid) :=
  match m with
  | 0 => .id
  | _ + 1 => (E 0).append
      (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => V i.succ)
        (fun i => G i.succ) (fun i => E i.succ)) (G 0).out

end Extractor.RoundByRound

namespace Verifier.KnowledgeStateFunction

/-- Fold named knowledge states by guarded append along the same recursion as `seqCompose`.
Every component guard is used, including the last component before the terminal identity. -/
def seqComposeGuarded {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    {WitMid : ∀ i, Fin (n i + 1) → Type}
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Wit i.succ) (pSpec i) (WitMid i))
    (K : ∀ i, (V i).KnowledgeStateFunction init impl (rel i.castSucc) (rel i.succ) (E i)) :
    (Verifier.seqCompose Stmt V).KnowledgeStateFunction init impl (rel 0) (rel (Fin.last m))
      (Extractor.RoundByRound.seqCompose Stmt Wit V G E) :=
  match m with
  | 0 => .id init impl
  | _ + 1 => (K 0).appendGuarded (G 0)
      (seqComposeGuarded (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => rel i.succ)
        (fun i => V i.succ) (fun i => G i.succ) (fun i => E i.succ) (fun i => K i.succ))

end Verifier.KnowledgeStateFunction

namespace Reduction

/-- Sequential composition of reductions, defined via sequential composition of provers and
  verifiers (or equivalently, folding over the append of reductions).

TODO: improve efficiency, this might be `O(m^2)`
-/
@[inline]
def seqCompose {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    Reduction oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) where
  prover := Prover.seqCompose Stmt Wit (fun i => (R i).prover)
  verifier := Verifier.seqCompose Stmt (fun i => (R i).verifier)

@[simp]
lemma seqCompose_zero (Stmt : Fin 1 → Type) (Wit : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin 0) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit R = Reduction.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (R : (i : Fin (m + 1)) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt Wit R =
      append (R 0) (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))) := rfl

end Reduction

namespace OracleProver

/-- Sequential composition of provers in oracle reductions, defined via sequential composition of
  provers in non-oracle reductions. -/
@[inline]
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      OracleProver oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    OracleProver oSpec (Stmt 0) (OStmt 0) (Wit 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (Wit (Fin.last m)) (seqCompose pSpec) :=
  Prover.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit P

@[simp]
lemma seqCompose_def {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (P : (i : Fin m) →
      OracleProver oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt OStmt Wit P = Prover.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit P :=
  rfl

end OracleProver

namespace OracleVerifier

/-- Sequential composition of verifiers in oracle reductions.

This is the auxiliary version that has instance parameters as implicit parameters, so that matching
on `m` can properly specialize those parameters.

TODO: have to fix instance diamonds to make this work -/
def seqCompose' {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i)) :
    OracleVerifier oSpec (Stmt 0) (OStmt 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (seqCompose pSpec) := match m with
  | 0 => @OracleVerifier.id ι oSpec (Stmt 0) (ιₛ 0) (OStmt 0) (Oₛ := Oₛ 0)
  | _ + 1 => append (V 0) (seqCompose' (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
      (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i)))

/-- Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the
  composition (append) of two oracle verifiers. -/
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i)) :
    OracleVerifier oSpec (Stmt 0) (OStmt 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (seqCompose pSpec) :=
  seqCompose' Stmt OStmt Oₛ Oₘ V

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type)
    {ιₛ : Fin 1 → Type} (OStmt : (i : Fin 1) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin 0) → OracleVerifier oSpec
      (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ) (pSpec i)) :
    seqCompose Stmt OStmt V = OracleVerifier.id := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type)
    {ιₛ : Fin (m + 2) → Type} (OStmt : (i : Fin (m + 2)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin (m + 1)) → OracleVerifier oSpec
      (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ) (pSpec i)) :
    seqCompose Stmt OStmt V =
      append (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
          (fun i => V (Fin.succ i))) := rfl

@[simp]
lemma seqCompose_toVerifier {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i)) :
    (seqCompose Stmt OStmt V).toVerifier =
      Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier) := by
  induction m with
  | zero =>
    simp only [Fin.isValue, Fin.reduceLast, Fin.vsum_zero, seqCompose_zero, Nat.reduceAdd,
      Verifier.seqCompose_zero]
    exact OracleVerifier.id_toVerifier
  | succ m ih =>
    simp only [seqCompose_succ, Verifier.seqCompose_succ]
    have h1 := OracleVerifier.append_toVerifier (V 0) (seqCompose (Stmt ∘ Fin.succ)
      (fun i => OStmt (Fin.succ i)) (fun i => V (Fin.succ i)))
    exact h1.trans (congrArg ((V 0).toVerifier.append ·)
      (ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (fun i => V (Fin.succ i))))

/-- The folded named knowledge state transported to the oracle chain's verifier semantics. -/
def seqComposeKnowledgeStateFunction {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type}
    (OStmt : (i : Fin (m + 1)) → ιₛ i → Type) [∀ i j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, OracleInterface ((pSpec i).Message j)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : ∀ i, OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ)
      (OStmt i.succ) (pSpec i))
    (G : ∀ i, (V i).toVerifier.GuardedForm)
    {WitMid : ∀ i, Fin (n i + 1) → Type}
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc × ∀ j, OStmt i.castSucc j)
      (Wit i.castSucc) (Wit i.succ) (pSpec i) (WitMid i))
    (K : ∀ i, (V i).toVerifier.KnowledgeStateFunction init impl
      (rel i.castSucc) (rel i.succ) (E i)) :
    (seqCompose Stmt OStmt V).toVerifier.KnowledgeStateFunction init impl
      (rel 0) (rel (Fin.last m))
      (Extractor.RoundByRound.seqCompose (fun i => Stmt i × ∀ j, OStmt i j) Wit
        (fun i => (V i).toVerifier) G E) :=
  let state := Verifier.KnowledgeStateFunction.seqComposeGuarded
    (fun i => Stmt i × ∀ j, OStmt i j) Wit rel (fun i => (V i).toVerifier) G E K
  { toFun := state.toFun
    toFun_empty := state.toFun_empty
    toFun_next := state.toFun_next
    toFun_full := by simpa only [seqCompose_toVerifier] using state.toFun_full }

end OracleVerifier

namespace OracleReduction

/-- Sequential composition of oracle reductions, defined via sequential composition of oracle
  provers and oracle verifiers. -/
def seqCompose {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    OracleReduction oSpec (Stmt 0) (OStmt 0) (Wit 0)
      (Stmt (Fin.last m)) (OStmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) where
  prover := OracleProver.seqCompose Stmt OStmt Wit (fun i => (R i).prover)
  verifier := OracleVerifier.seqCompose Stmt OStmt (fun i => (R i).verifier)

@[simp]
lemma seqCompose_zero
    (Stmt : Fin 1 → Type)
    {ιₛ : Fin 1 → Type} (OStmt : (i : Fin 1) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin 1 → Type)
    {n : Fin 0 → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin 0) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt OStmt Wit R =
      @OracleReduction.id ι oSpec (Stmt 0) (ιₛ 0) (OStmt 0) (Wit 0) (Oₛ 0) := rfl

@[simp]
lemma seqCompose_succ {m : ℕ}
    (Stmt : Fin (m + 2) → Type)
    {ιₛ : Fin (m + 2) → Type} (OStmt : (i : Fin (m + 2)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 2) → Type)
    {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin (m + 1)) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    seqCompose Stmt OStmt Wit R =
      append (R 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ)
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
          (fun i => R (Fin.succ i))) := rfl

@[simp]
lemma seqCompose_toReduction {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    (seqCompose Stmt OStmt Wit R).toReduction =
      Reduction.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit
        (fun i => (R i).toReduction) := by
  induction m with
  | zero =>
    simp only [Fin.isValue, Fin.reduceLast, Fin.vsum_zero, seqCompose_zero, Nat.reduceAdd,
      Reduction.seqCompose_zero]
    exact OracleReduction.id_toReduction
  | succ m ih =>
    simp only [seqCompose_succ, Reduction.seqCompose_succ]
    have h1 := OracleReduction.append_toReduction (R 0) (seqCompose (Stmt ∘ Fin.succ)
      (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i)))
    exact h1.trans (congrArg ((R 0).toReduction.append ·)
      (ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (Wit ∘ Fin.succ)
        (fun i => R (Fin.succ i))))

end OracleReduction

end Composition

variable {m : ℕ}
    {Stmt : Fin (m + 1) → Type}
    {ιₛ : Fin (m + 1) → Type} {OStmt : (i : Fin (m + 1)) → ιₛ i → Type}
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {Wit : Fin (m + 1) → Type}
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

namespace ProtocolSpec

/-- A function of a component challenge index, evaluated at the decoding of a combined challenge
index, is its value at any component index the combined index's round splits into. -/
theorem apply_seqComposeChallengeIdxToSigma {m : ℕ} {n : Fin m → ℕ}
    {pSpec : ∀ i, ProtocolSpec (n i)} {α : Sort*}
    (f : (i : Fin m) → (pSpec i).ChallengeIdx → α) (k : (seqCompose pSpec).ChallengeIdx)
    (a : Fin m) (b : (pSpec a).ChallengeIdx) (h : Fin.splitSum k.1 = ⟨a, b.1⟩) :
    f (seqComposeChallengeIdxToSigma k).1 (seqComposeChallengeIdxToSigma k).2 = f a b := by
  have key : ∀ (s : (i : Fin m) × Fin (n i)) (hs : (pSpec s.1).dir s.2 = .V_to_P),
      s = ⟨a, b.1⟩ → f s.1 ⟨s.2, hs⟩ = f a b := by
    rintro s hs rfl
    rfl
  exact key _ _ h

/-- **Error reindexing for one step of `seqCompose`.** A per-component function of challenge
indices, read through `seqComposeChallengeIdxToSigma` on `pSpec 0 ++ₚ seqCompose (pSpec ∘ succ)`,
is the first component's function on the left and the reindexed tail's on the right. This is the
error bookkeeping of an induction that composes the head with the tail by `append`. -/
theorem apply_seqComposeChallengeIdxToSigma_eq_sumElim {m : ℕ} {n : Fin (m + 1) → ℕ}
    {pSpec : ∀ i, ProtocolSpec (n i)} {α : Type*}
    (f : (i : Fin (m + 1)) → (pSpec i).ChallengeIdx → α) :
    (fun k => f (seqComposeChallengeIdxToSigma k).1 (seqComposeChallengeIdxToSigma k).2) =
      Sum.elim (f 0) (fun k => f (seqComposeChallengeIdxToSigma k).1.succ
        (seqComposeChallengeIdxToSigma k).2) ∘
        (ChallengeIdx.sumEquiv (pSpec₁ := pSpec 0)
          (pSpec₂ := seqCompose fun i => pSpec i.succ)).symm := by
  funext k
  obtain ⟨k, rfl⟩ := (ChallengeIdx.sumEquiv (pSpec₁ := pSpec 0)
    (pSpec₂ := seqCompose fun i => pSpec i.succ)).surjective k
  rcases k with i | k
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    exact apply_seqComposeChallengeIdxToSigma f _ 0 i (Fin.splitSum_embedSum (n := n) 0 i.1)
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    refine apply_seqComposeChallengeIdxToSigma f _ _ _ ?_
    have h := Fin.splitSum_embedSum (n := n) (Fin.splitSum k.1).1.succ (Fin.splitSum k.1).2
    rw [Fin.embedSum_succ_succ, Fin.embedSum_splitSum] at h
    exact h

end ProtocolSpec

section Security

open scoped NNReal

namespace Verifier

omit Oₘ in
/-- Guarded verifiers that are sound from every deterministic oracle state compose with the
sum of their errors, for an arbitrary initialization of the shared oracle state.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. This excludes oracle states that hide a
secret from the prover (a trapdoor or an eagerly sampled random function); lazily sampled
oracles satisfy this requirement. -/
theorem seqCompose_soundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (soundnessError : Fin m → ℝ≥0)
    [∀ i, (V i).IsGuarded]
    (h : ∀ i, ∀ s : σ,
      (V i).soundness (pure s) impl (lang i.castSucc) (lang i.succ) (soundnessError i)) :
      (Verifier.seqCompose Stmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) := by
  induction m generalizing init with
  | zero =>
    simp only [Fin.isValue, Fin.reduceLast, Fin.vsum_zero, seqCompose_zero,
      Finset.univ_eq_empty, Finset.sum_empty]
    exact Verifier.id_soundness init impl
  | succ m ih =>
    simp only [Fin.vsum_succ, seqCompose_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, Fin.succ_last, Nat.succ_eq_add_one]
    rw [Fin.sum_univ_succ]
    apply append_soundness (V 0) (seqCompose (Stmt ∘ Fin.succ) (fun i => V i.succ))
      (soundness_of_forall_pure (h 0))
    intro s
    exact ih (init := pure s) (fun i => lang i.succ) (fun i => V i.succ)
      (fun i => soundnessError i.succ) (fun i => h i.succ)

omit Oₘ in
/-- A chain of guarded verifiers with named pure extractors has the sum of the component
knowledge errors. Each component bound is uniform over deterministic initial oracle states.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. This excludes oracle states that hide a
secret from the prover (a trapdoor or an eagerly sampled random function); lazily sampled
oracles satisfy this requirement. -/
theorem seqCompose_knowledgeSoundnessWith
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (knowledgeError : Fin m → ℝ≥0) (G : ∀ i, (V i).GuardedForm)
    (e : (i : Fin m) → Stmt i.castSucc → Wit i.succ →
      (pSpec i).FullTranscript → Option (Wit i.castSucc))
    (h : ∀ i, ∀ s : σ, (V i).knowledgeSoundnessWith (pure s) impl
      (rel i.castSucc) (rel i.succ) (Extractor.Straightline.ofTranscriptAndOutput (e i))
      (knowledgeError i)) :
    (Verifier.seqCompose Stmt V).knowledgeSoundnessWith init impl (rel 0) (rel (Fin.last m))
      (Extractor.Straightline.ofTranscriptAndOutput (seqComposeExtract Stmt Wit V G e))
      (∑ i, knowledgeError i) := by
  induction m generalizing init with
  | zero =>
    simp only [Fin.isValue, Fin.reduceLast, Fin.vsum_zero, seqCompose_zero,
      Finset.univ_eq_empty, Finset.sum_empty, seqComposeExtract]
    exact id_knowledgeSoundnessWith init impl (rel 0)
  | succ m ih =>
    simp only [Fin.vsum_succ, seqCompose_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, Fin.succ_last, Nat.succ_eq_add_one, seqComposeExtract]
    rw [Fin.sum_univ_succ]
    apply append_knowledgeSoundnessWith
      (V₂ := seqCompose (Stmt ∘ Fin.succ) (fun i => V i.succ)) (G 0) (e 0)
      (seqComposeExtract (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => V i.succ)
        (fun i => G i.succ) (fun i => e i.succ))
      (knowledgeSoundnessWith_of_forall_pure (h 0))
    intro s
    exact ih (init := pure s) (fun i => rel i.succ) (fun i => V i.succ)
      (fun i => knowledgeError i.succ) (fun i => G i.succ) (fun i => e i.succ)
      (fun i => h i.succ)

omit Oₘ in
/-- Pure transcript-and-output extractors give ordinary knowledge soundness of a guarded chain.
Each extractor is fixed before the initial oracle state is chosen.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. This excludes oracle states that hide a
secret from the prover (a trapdoor or an eagerly sampled random function); lazily sampled
oracles satisfy this requirement. -/
theorem seqCompose_knowledgeSoundness
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (knowledgeError : Fin m → ℝ≥0) (G : ∀ i, (V i).GuardedForm)
    (h : ∀ i, ∃ e, ∀ s : σ, (V i).knowledgeSoundnessWith (pure s) impl
      (rel i.castSucc) (rel i.succ) (Extractor.Straightline.ofTranscriptAndOutput e)
      (knowledgeError i)) :
      (Verifier.seqCompose Stmt V).knowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (∑ i, knowledgeError i) := by
  choose e he using h
  exact knowledgeSoundness_of_with init impl
    (seqCompose_knowledgeSoundnessWith rel V knowledgeError G e he)

end Verifier

namespace OracleVerifier

/-- Oracle verifiers whose induced verifiers are guarded and sound from every deterministic
oracle state compose with the sum of their errors, for arbitrary initialization.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. This excludes oracle states that hide a
secret from the prover (a trapdoor or an eagerly sampled random function); lazily sampled
oracles satisfy this requirement. -/
theorem seqCompose_soundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i × ∀ j, OStmt i j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (soundnessError : Fin m → ℝ≥0)
    [∀ i, (V i).toVerifier.IsGuarded]
    (h : ∀ i, ∀ s : σ,
      (V i).soundness (pure s) impl (lang i.castSucc) (lang i.succ) (soundnessError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) := by
  unfold OracleVerifier.soundness
  convert Verifier.seqCompose_soundness lang (fun i => (V i).toVerifier) soundnessError h
  simp only [seqCompose_toVerifier]

/-- Named pure extractors compose along a chain of oracle verifiers with guarded induced
verifiers and component bounds uniform over deterministic shared oracle states.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. This excludes oracle states that hide a
secret from the prover (a trapdoor or an eagerly sampled random function); lazily sampled
oracles satisfy this requirement. -/
theorem seqCompose_knowledgeSoundnessWith
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (knowledgeError : Fin m → ℝ≥0) (G : ∀ i, (V i).toVerifier.GuardedForm)
    (e : (i : Fin m) → (Stmt i.castSucc × ∀ j, OStmt i.castSucc j) → Wit i.succ →
      (pSpec i).FullTranscript → Option (Wit i.castSucc))
    (h : ∀ i, ∀ s : σ, (V i).knowledgeSoundnessWith (pure s) impl
      (rel i.castSucc) (rel i.succ) (Extractor.Straightline.ofTranscriptAndOutput (e i))
      (knowledgeError i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).knowledgeSoundnessWith init impl
      (rel 0) (rel (Fin.last m))
      (Extractor.Straightline.ofTranscriptAndOutput
        (Verifier.seqComposeExtract (fun i => Stmt i × ∀ j, OStmt i j) Wit
          (fun i => (V i).toVerifier) G e)) (∑ i, knowledgeError i) := by
  unfold OracleVerifier.knowledgeSoundnessWith
  rw [seqCompose_toVerifier]
  exact Verifier.seqCompose_knowledgeSoundnessWith rel (fun i => (V i).toVerifier)
    knowledgeError G e h

/-- Pure transcript-and-output extractors give ordinary knowledge soundness of a guarded oracle
chain, with the sum of the component errors.

The second-stage bound is required from every fixed oracle state because the intermediate
statement is chosen adaptively after oracle answers. This excludes oracle states that hide a
secret from the prover (a trapdoor or an eagerly sampled random function); lazily sampled
oracles satisfy this requirement. -/
theorem seqCompose_knowledgeSoundness
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (knowledgeError : Fin m → ℝ≥0) (G : ∀ i, (V i).toVerifier.GuardedForm)
    (h : ∀ i, ∃ e, ∀ s : σ, (V i).knowledgeSoundnessWith (pure s) impl
      (rel i.castSucc) (rel i.succ) (Extractor.Straightline.ofTranscriptAndOutput e)
      (knowledgeError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).knowledgeSoundness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, knowledgeError i) := by
  unfold OracleVerifier.knowledgeSoundness
  rw [seqCompose_toVerifier]
  exact Verifier.seqCompose_knowledgeSoundness rel (fun i => (V i).toVerifier) knowledgeError G h

end OracleVerifier

end Security
