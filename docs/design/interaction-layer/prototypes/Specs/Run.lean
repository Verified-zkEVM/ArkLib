/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Core

/-!
# Running a description

This module turns a description into ArkLib objects and proves the two generic theorems.

* `Desc.run` is the verifier's decision in any monad. It walks the description along a view,
  sends input-oracle queries to `inp` and oracle-message queries to `lift`, and returns `none` at
  the first failed check.
* `Desc.verdict` is the pure verdict on a full transcript, with the input oracles answered by
  `ans` and the oracle messages read from the transcript.
* `Desc.prove` is the honest prover.
* `Spec.verifier` is an `OracleVerifier` that keeps its input oracles. Its decision routes input
  queries to `.inr (.inl _)` and oracle-message queries to `.inr (.inr _)` of
  `pathBundle In t p`.
* `Desc.run_hom` (decision as evaluation): a monad morphism that answers the input queries by
  `ans` and the message queries from the transcript sends the decision to `pure` of the verdict.
  `Spec.decide_eq_verdict` is its instance for ArkLib's `decide`.
* `Desc.verdict_isSome` (honest acceptance): on an honest transcript the verdict accepts when
  every check holds on the honest values for every choice of challenges (`Desc.Complete`).
* `tr⟦a, …, x⟧` reads a move by hierarchical label: the stages and rounds that enclose it,
  then the base of its name.

## Design choices

* The decision is generic in the monad. *Why:* ArkLib's verifier instantiates it at
  `OracleComp (ambient + pathBundle In t p).spec` with no `simulateQ` layer, and the verdict
  theorem is one induction for every monad morphism.
* Oracle handles resolve through `Handlers m`, a table from levels to query functions. The table
  lookup compares types with classical decidability and casts. *Why:* the handle a continuation
  receives must be the same value in every interpreter, so it cannot carry a monadic function.
  The cast never fires on a description built from the combinators.
* The verdict is a separate pure function on transcripts, not the decision at `Id`. *Why:* proofs
  about a fixed protocol (honest acceptance, the agreement with ArkLib's sum-check verdict)
  then destructure the transcript directly, with no view erasure.
* Stage claims are not checked by any interpreter. *Why:* they state what a stage reduces, and a
  soundness proof uses them as relations, not as verifier steps.
* The accessor is an elaborator that walks the skeleton in the specification's type and emits a
  chain of `.2` and `.1` projections. *Why:* the result is a projection term, so it reduces by
  `rfl` and `simp` for every `n` at which the skeleton prefix up to the move is concrete.
-/

namespace Specs
open Interaction PFunctor FreeM OracleComp OracleSpec Interaction.TwoParty.Lens

/-! ## Oracle handlers -/

/-- Query functions for the oracle messages seen so far, indexed by level. -/
def Handlers (m : Type → Type) : Type 1 :=
  ℕ → Option ((Q : Type) × (A : Type) × (Q → m A))

namespace Handlers
variable {m m' : Type → Type}

/-- No oracle message seen yet. -/
def empty : Handlers m := fun _ => none

/-- Record the query function `f` at level `ℓ`. -/
def ext (env : Handlers m) (ℓ : ℕ) {Q A : Type} (f : Q → m A) : Handlers m :=
  fun i => if i = ℓ then some ⟨Q, A, f⟩ else env i

/-- Apply `φ` to every query function. -/
def map (φ : ∀ {α : Type}, m α → m' α) (env : Handlers m) : Handlers m' :=
  fun i => (env i).map fun e => ⟨e.1, e.2.1, fun q => φ (e.2.2 q)⟩

open Classical in
/-- The query function at level `ℓ` with queries `Q` and answers `A`. A missing level or a type
mismatch answers `dflt`. -/
noncomputable def find [Pure m] (env : Handlers m) {Q A : Type} (dflt : A) (ℓ : ℕ) (q : Q) :
    m A :=
  match env ℓ with
  | some e =>
    if h : e.1 = Q ∧ e.2.1 = A then cast (congrArg m h.2) (e.2.2 (cast h.1.symm q))
    else pure dflt
  | none => pure dflt

theorem map_ext (φ : ∀ {α : Type}, m α → m' α) (env : Handlers m) (ℓ : ℕ) {Q A : Type}
    (f : Q → m A) : (env.ext ℓ f).map φ = (env.map φ).ext ℓ fun q => φ (f q) := by
  funext i
  simp only [map, ext]
  split <;> rfl

theorem find_map [Pure m] [Pure m'] (φ : ∀ {α : Type}, m α → m' α)
    (hpure : ∀ {α : Type} (a : α), φ (pure a) = pure a) (env : Handlers m) {Q A : Type}
    (dflt : A) (ℓ : ℕ) (q : Q) : φ (env.find dflt ℓ q) = (env.map φ).find dflt ℓ q := by
  simp only [find, map]
  rcases env ℓ with _ | ⟨Q', A', f⟩
  · exact hpure dflt
  · simp only [Option.map_some]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · exact hpure dflt

/-- The query function just recorded at a level answers the queries at that level. -/
@[simp] theorem find_ext_self [Pure m] (env : Handlers m) (ℓ : ℕ) {Q A : Type} (f : Q → m A)
    (dflt : A) (q : Q) : (env.ext ℓ f).find dflt ℓ q = f q := by
  simp [find, ext]

/-- A level below the recorded one is unaffected. -/
theorem find_ext_ne [Pure m] (env : Handlers m) {ℓ ℓ' : ℕ} (h : ℓ' ≠ ℓ) {Q A : Type}
    (f : Q → m A) {Q' A' : Type} (dflt : A') (q : Q') :
    (env.ext ℓ f).find dflt ℓ' q = env.find dflt ℓ' q := by
  simp [find, ext, h]

end Handlers

/-! ## Resolving references -/

variable {In : OracleBundle} {W T : Type}

/-- The formula oracle of an interpreter: a reference reads the handler at its level. -/
noncomputable abbrev askOf {m : Type → Type} [Monad m] (env : Handlers m) :
    ∀ ⦃Q A : Type⦄, Ref Q A → Q → m A :=
  fun ⦃_ _⦄ r q => env.find r.dflt r.lvl q

/-- The pure formula oracle of the verdict and the prover. -/
noncomputable abbrev askId (env : Handlers Id) : ∀ ⦃Q A : Type⦄, Ref Q A → Q → A :=
  fun ⦃_ _⦄ r q => (env.find r.dflt r.lvl q).run

/-- The handler entry of an input read: the query `q` goes to `embed q` of the input bundle. -/
abbrev inputEntry {m : Type → Type} [Monad m] (inp : QueryImpl In.spec m) {Q A : Type}
    (embed : Q → In.Query) (resp : ∀ q, In.spec (embed q) = A) : Q → m A :=
  fun q => cast (resp q) <$> inp (embed q)

/-! ## Views -/

/-- The view after a node whose branch is `Unit` (a challenge or an oracle message). -/
def View.tail {a : OraclePos} {t : OracleProtocol}
    {p : Path (FreeM.liftBind (P := OraclePoly) a fun _ => t)}
    (v : View (.liftBind a fun _ => t) p) : View t p.2 :=
  ⟨v.1.2, congrArg (fun q : (_ : OraclePoly.B a) × Path t => q.2) v.2⟩

/-- The challenge at the root of a view. -/
def View.head {C : Type} {t : OracleProtocol}
    {p : Path (FreeM.liftBind (P := OraclePoly) (OraclePos.challenge C) fun _ => t)}
    (v : View (FreeM.liftBind (P := OraclePoly) (OraclePos.challenge C) fun _ => t) p) : C :=
  v.1.1

/-- The view after a plain message. The path fixes the message. -/
def View.msgTail {X : Type} {t : X → OracleProtocol}
    {p : Path (FreeM.liftBind (P := OraclePoly) (OraclePos.message X) t)}
    (v : View (FreeM.liftBind (P := OraclePoly) (OraclePos.message X) t) p) :
    View (t p.1) p.2 := by
  obtain ⟨⟨x', tr⟩, h⟩ := v
  obtain ⟨x, p⟩ := p
  have h' : (⟨x', Transcript.path (l := viewSig) tr⟩ : (y : X) × Path (t y)) = ⟨x, p⟩ := h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj h'
  exact ⟨tr, eq_of_heq h2⟩

/-! ## The three interpreters -/

namespace Desc

/-- The verifier's decision in the monad `m`. It walks the description along the view `v`,
sends input queries to `inp` and the queries to the oracle messages of the path to `lift`,
records each input oracle and each oracle message in the handlers at the next level, and returns
`none` at the first failed check. -/
noncomputable def run {m : Type → Type} [Monad m] (inp : QueryImpl In.spec m) :
    {t : OracleProtocol} → {ks : Skel} → Desc In W T t ks →
      (p : Path t) → View t p → QueryImpl (oracleMessageSpec t p) m → Handlers m → ℕ →
        m (Option T)
  | _, _, .done out, _, _, _, _, _ => pure (some out)
  | _, _, .message _ _ _ _ _ _ rest, p, v, lift, env, ℓ =>
      (rest p.1).run inp p.2 (View.msgTail v) lift env ℓ
  | _, _, .oracle _ _ _ _ hA dflt _ _ _ _ rest, p, v, lift, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).run inp p.2 (View.tail v) (fun q => lift (.inr q))
        (env.ext ℓ fun q => cast (hA q) <$> lift (.inl q)) (ℓ + 1)
  | _, _, .challenge _ _ _ _ rest, p, v, lift, env, ℓ =>
      (rest (View.head v)).run inp p.2 (View.tail v) lift env ℓ
  | _, _, .check _ _ φ args _ rest, p, v, lift, env, ℓ => do
      if (← (φ.inst args).evalM (askOf env)) then rest.run inp p v lift env ℓ
      else pure none
  | _, _, .compute _ _ _ _ φ args _ rest, p, v, lift, env, ℓ => do
      (rest (← (φ.inst args).evalM (askOf env))).run inp p v lift env ℓ
  | _, _, .input _ _ _ _ embed resp dflt rest, p, v, lift, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).run inp p v lift (env.ext ℓ (inputEntry inp embed resp)) (ℓ + 1)
  | _, _, .branch _ _ _ _ _ _ rest, p, v, lift, env, ℓ =>
      (rest p.1).run inp p.2 (View.msgTail v) lift env ℓ
  | _, _, .stageIn _ _ _ _ _ _ rest, p, v, lift, env, ℓ => rest.run inp p v lift env ℓ
  | _, _, .stageOut _ _ _ rest, p, v, lift, env, ℓ => rest.run inp p v lift env ℓ
  | _, _, .mark _ rest, p, v, lift, env, ℓ => rest.run inp p v lift env ℓ

/-- The handler entry of the oracle message `x`: it answers from the value. -/
abbrev honestEntry {X : Type} (I : OracleInterface X) {A : Type} (hA : ∀ q, I.spec q = A)
    (x : X) : I.Query → Id A :=
  fun q => pure (cast (hA q) (I.answer x q))

/-- The verdict on a full transcript. Input queries go to `ans`, and each oracle message answers
from its value in the transcript. -/
noncomputable def verdict (ans : QueryImpl In.spec Id) :
    {t : OracleProtocol} → {ks : Skel} → Desc In W T t ks →
      Transcript oracleSig t → Handlers Id → ℕ → Option T
  | _, _, .done out, _, _, _ => some out
  | _, _, .message _ _ _ _ _ _ rest, ⟨x, tr⟩, env, ℓ => (rest x).verdict ans tr env ℓ
  | _, _, .oracle _ _ I _ hA dflt _ _ _ _ rest, ⟨x, tr⟩, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).verdict ans tr (env.ext ℓ (honestEntry I hA x)) (ℓ + 1)
  | _, _, .challenge _ _ _ _ rest, ⟨c, tr⟩, env, ℓ => (rest c).verdict ans tr env ℓ
  | _, _, .check _ _ φ args _ rest, tr, env, ℓ =>
      if (φ.inst args).eval (askId env) then rest.verdict ans tr env ℓ else none
  | _, _, .compute _ _ _ _ φ args _ rest, tr, env, ℓ =>
      (rest ((φ.inst args).eval (askId env))).verdict ans tr env ℓ
  | _, _, .input _ _ _ _ embed resp dflt rest, tr, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).verdict ans tr
        (env.ext ℓ (inputEntry ans embed resp)) (ℓ + 1)
  | _, _, .branch _ _ _ _ _ _ rest, ⟨x, tr⟩, env, ℓ => (rest x).verdict ans tr env ℓ
  | _, _, .stageIn _ _ _ _ _ _ rest, tr, env, ℓ => rest.verdict ans tr env ℓ
  | _, _, .stageOut _ _ _ rest, tr, env, ℓ => rest.verdict ans tr env ℓ
  | _, _, .mark _ rest, tr, env, ℓ => rest.verdict ans tr env ℓ

/-- The honest prover. It sends `honest w` at each message, answers input queries by `ans` and
its own oracle queries from its honest messages, and computes the local values. -/
noncomputable def prove {m : Type → Type} [Monad m] (w : W) (ans : QueryImpl In.spec Id) :
    {t : OracleProtocol} → {ks : Skel} → Desc In W T t ks → Handlers Id → ℕ →
      Focal oracleSig m t (fun _ => T)
  | _, _, .done out, _, _ => (pure out : m T)
  | _, _, .message _ _ _ _ _ honest rest, env, ℓ =>
      pure ⟨honest w, (rest (honest w)).prove w ans env ℓ⟩
  | _, _, .oracle _ _ I _ hA dflt _ _ _ honest rest, env, ℓ =>
      pure ⟨honest w, (rest ⟨⟨ℓ, dflt⟩⟩).prove w ans
        (env.ext ℓ (honestEntry I hA (honest w))) (ℓ + 1)⟩
  | _, _, .challenge _ _ _ _ rest, env, ℓ => pure fun c => (rest c).prove w ans env ℓ
  | _, _, .check _ _ _ _ _ rest, env, ℓ => rest.prove w ans env ℓ
  | _, _, .compute _ _ _ _ φ args _ rest, env, ℓ =>
      (rest ((φ.inst args).eval (askId env))).prove w ans env ℓ
  | _, _, .input _ _ _ _ embed resp dflt rest, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).prove w ans
        (env.ext ℓ (inputEntry ans embed resp)) (ℓ + 1)
  | _, _, .branch _ _ _ _ honest _ rest, env, ℓ =>
      pure ⟨honest w, (rest (honest w)).prove w ans env ℓ⟩
  | _, _, .stageIn _ _ _ _ _ _ rest, env, ℓ => rest.prove w ans env ℓ
  | _, _, .stageOut _ _ _ rest, env, ℓ => rest.prove w ans env ℓ
  | _, _, .mark _ rest, env, ℓ => rest.prove w ans env ℓ

/-! ## Honest acceptance -/

/-- Every check holds when the prover is honest with witness `w` and the input oracles answer by
`ans`, for every choice of challenges. -/
def Complete (w : W) (ans : QueryImpl In.spec Id) :
    {t : OracleProtocol} → {ks : Skel} → Desc In W T t ks → Handlers Id → ℕ → Prop
  | _, _, .done _, _, _ => True
  | _, _, .message _ _ _ _ _ honest rest, env, ℓ => (rest (honest w)).Complete w ans env ℓ
  | _, _, .oracle _ _ I _ hA dflt _ _ _ honest rest, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).Complete w ans (env.ext ℓ (honestEntry I hA (honest w))) (ℓ + 1)
  | _, _, .challenge _ _ _ _ rest, env, ℓ => ∀ c, (rest c).Complete w ans env ℓ
  | _, _, .check _ _ φ args _ rest, env, ℓ =>
      (φ.inst args).eval (askId env) = true ∧ rest.Complete w ans env ℓ
  | _, _, .compute _ _ _ _ φ args _ rest, env, ℓ =>
      (rest ((φ.inst args).eval (askId env))).Complete w ans env ℓ
  | _, _, .input _ _ _ _ embed resp dflt rest, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).Complete w ans
        (env.ext ℓ (inputEntry ans embed resp)) (ℓ + 1)
  | _, _, .branch _ _ _ _ honest _ rest, env, ℓ => (rest (honest w)).Complete w ans env ℓ
  | _, _, .stageIn _ _ _ _ _ _ rest, env, ℓ => rest.Complete w ans env ℓ
  | _, _, .stageOut _ _ _ rest, env, ℓ => rest.Complete w ans env ℓ
  | _, _, .mark _ rest, env, ℓ => rest.Complete w ans env ℓ

/-- The transcript `tr` is a run of the honest prover with witness `w`: every message and
oracle message is the honest one. The challenges are arbitrary. -/
def Honest (w : W) (ans : QueryImpl In.spec Id) :
    {t : OracleProtocol} → {ks : Skel} → Desc In W T t ks → Transcript oracleSig t →
      Handlers Id → ℕ → Prop
  | _, _, .done _, _, _, _ => True
  | _, _, .message _ _ _ _ _ honest rest, ⟨x, tr⟩, env, ℓ =>
      x = honest w ∧ (rest x).Honest w ans tr env ℓ
  | _, _, .oracle _ _ I _ hA dflt _ _ _ honest rest, ⟨x, tr⟩, env, ℓ =>
      x = honest w ∧ (rest ⟨⟨ℓ, dflt⟩⟩).Honest w ans tr (env.ext ℓ (honestEntry I hA x))
        (ℓ + 1)
  | _, _, .challenge _ _ _ _ rest, ⟨c, tr⟩, env, ℓ => (rest c).Honest w ans tr env ℓ
  | _, _, .check _ _ _ _ _ rest, tr, env, ℓ => rest.Honest w ans tr env ℓ
  | _, _, .compute _ _ _ _ φ args _ rest, tr, env, ℓ =>
      (rest ((φ.inst args).eval (askId env))).Honest w ans tr env ℓ
  | _, _, .input _ _ _ _ embed resp dflt rest, tr, env, ℓ =>
      (rest ⟨⟨ℓ, dflt⟩⟩).Honest w ans tr
        (env.ext ℓ (inputEntry ans embed resp)) (ℓ + 1)
  | _, _, .branch _ _ _ _ honest _ rest, ⟨x, tr⟩, env, ℓ =>
      x = honest w ∧ (rest x).Honest w ans tr env ℓ
  | _, _, .stageIn _ _ _ _ _ _ rest, tr, env, ℓ => rest.Honest w ans tr env ℓ
  | _, _, .stageOut _ _ _ rest, tr, env, ℓ => rest.Honest w ans tr env ℓ
  | _, _, .mark _ rest, tr, env, ℓ => rest.Honest w ans tr env ℓ

/-- Honest acceptance: if every check holds on the honest values, the verdict accepts every
honest transcript. -/
theorem verdict_isSome (w : W) (ans : QueryImpl In.spec Id) :
    ∀ {t : OracleProtocol} {ks : Skel} (d : Desc In W T t ks) (tr : Transcript oracleSig t)
      (env : Handlers Id) (ℓ : ℕ), d.Complete w ans env ℓ → d.Honest w ans tr env ℓ →
        (d.verdict ans tr env ℓ).isSome
  | _, _, .done _, _, _, _, _, _ => rfl
  | _, _, .message _ _ _ _ _ _ rest, ⟨_, tr⟩, env, ℓ, hc, hh => by
      obtain ⟨rfl, hh⟩ := hh
      exact verdict_isSome w ans (rest _) tr env ℓ hc hh
  | _, _, .oracle _ _ _ _ _ _ _ _ _ _ rest, ⟨_, tr⟩, _, _, hc, hh => by
      obtain ⟨rfl, hh⟩ := hh
      exact verdict_isSome w ans (rest _) tr _ _ hc hh
  | _, _, .challenge _ _ _ _ rest, ⟨c, tr⟩, env, ℓ, hc, hh =>
      verdict_isSome w ans (rest c) tr env ℓ (hc c) hh
  | _, _, .check _ _ _ _ _ rest, tr, env, ℓ, hc, hh => by
      obtain ⟨h, hc⟩ := hc
      simp only [verdict, h, ite_true]
      exact verdict_isSome w ans rest tr env ℓ hc hh
  | _, _, .compute _ _ _ _ _ _ _ rest, tr, env, ℓ, hc, hh =>
      verdict_isSome w ans (rest _) tr env ℓ hc hh
  | _, _, .input _ _ _ _ _ _ _ rest, tr, _, _, hc, hh =>
      verdict_isSome w ans (rest _) tr _ _ hc hh
  | _, _, .branch _ _ _ _ _ _ rest, ⟨_, tr⟩, env, ℓ, hc, hh => by
      obtain ⟨rfl, hh⟩ := hh
      exact verdict_isSome w ans (rest _) tr env ℓ hc hh
  | _, _, .stageIn _ _ _ _ _ _ rest, tr, env, ℓ, hc, hh =>
      verdict_isSome w ans rest tr env ℓ hc hh
  | _, _, .stageOut _ _ _ rest, tr, env, ℓ, hc, hh => verdict_isSome w ans rest tr env ℓ hc hh
  | _, _, .mark _ rest, tr, env, ℓ, hc, hh => verdict_isSome w ans rest tr env ℓ hc hh

end Desc

/-! ## Monad morphisms and the decision -/

/-- `φ` preserves `pure` and `bind`. `simulateQ impl` is one, and so is `pure` out of `Id`. -/
structure IsHom {m m' : Type → Type} [Monad m] [Monad m'] (φ : ∀ {α : Type}, m α → m' α) :
    Prop where
  map_pure : ∀ {α : Type} (a : α), φ (pure a) = pure a
  map_bind : ∀ {α β : Type} (x : m α) (f : α → m β), φ (x >>= f) = φ x >>= fun a => φ (f a)

/-- `pure` out of `Id`. -/
abbrev pureHom {m : Type → Type} [Monad m] : ∀ {α : Type}, Id α → m α := fun x => pure x.run

theorem isHom_pureHom {m : Type → Type} [Monad m] [LawfulMonad m] :
    @IsHom Id m _ _ (fun {_} x => pureHom x) :=
  ⟨fun _ => rfl, fun x f => (LawfulMonad.pure_bind x (fun a => pure (f a).run)).symm⟩

theorem isHom_simulateQ {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) :
    @IsHom (OracleComp spec) m _ _ (fun {_} x => simulateQ impl x) :=
  ⟨fun a => simulateQ_pure impl a, fun x f => simulateQ_bind impl x f⟩

section Hom
variable {m m' : Type → Type} [Monad m] [Monad m'] {φ : ∀ {α : Type}, m α → m' α}

theorem IsHom.map_map [LawfulMonad m] [LawfulMonad m'] (hφ : IsHom @φ) {α β : Type}
    (f : α → β) (x : m α) : φ (f <$> x) = f <$> φ x := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, hφ.map_bind]
  simp only [Function.comp_def, hφ.map_pure]

theorem sumM_hom (hφ : IsHom @φ) {α β : Type} [AddCommMonoid β] (f : α → m β) :
    ∀ l : List α, φ (sumM f l) = sumM (fun a => φ (f a)) l
  | [] => hφ.map_pure 0
  | a :: l => by simp only [sumM, hφ.map_bind, hφ.map_pure, sumM_hom hφ f l]

/-- A monad morphism commutes with formula evaluation. -/
theorem Fml.evalM_hom (hφ : IsHom @φ) {o : Type → Type → Type}
    (ask : ∀ ⦃Q A : Type⦄, o Q A → Q → m A) :
    ∀ {β : Type} (f : Fml (fun α => α) o β),
      φ (f.evalM ask) = f.evalM (fun ⦃_ _⦄ h q => φ (ask h q))
  | _, .var x => hφ.map_pure x
  | _, .lit _ a => hφ.map_pure a
  | _, @Fml.add _ _ _ _ a b => by
    simp only [Fml.evalM, hφ.map_bind, hφ.map_pure, Fml.evalM_hom hφ ask a,
      Fml.evalM_hom hφ ask b]
  | _, @Fml.sub _ _ _ _ a b => by
    simp only [Fml.evalM, hφ.map_bind, hφ.map_pure, Fml.evalM_hom hφ ask a,
      Fml.evalM_hom hφ ask b]
  | _, @Fml.mul _ _ _ _ a b => by
    simp only [Fml.evalM, hφ.map_bind, hφ.map_pure, Fml.evalM_hom hφ ask a,
      Fml.evalM_hom hφ ask b]
  | _, @Fml.neg _ _ _ _ a => by
    simp only [Fml.evalM, hφ.map_bind, hφ.map_pure, Fml.evalM_hom hφ ask a]
  | _, @Fml.pow _ _ _ _ a k => by
    simp only [Fml.evalM, hφ.map_bind, hφ.map_pure, Fml.evalM_hom hφ ask a]
  | _, @Fml.eq _ _ _ _ a b => by
    simp only [Fml.evalM, hφ.map_bind, hφ.map_pure, Fml.evalM_hom hφ ask a,
      Fml.evalM_hom hφ ask b]
  | _, .and a b => by
    simp only [Fml.evalM, hφ.map_bind, hφ.map_pure, Fml.evalM_hom hφ ask a,
      Fml.evalM_hom hφ ask b]
  | _, @Fml.sum _ _ _ _ _ _ dom body => by
    simp only [Fml.evalM]
    rw [sumM_hom hφ]
    exact congrArg (fun g => sumM g dom.elems) (funext fun x => Fml.evalM_hom hφ ask (body x))
  | _, .query h q => by
    simp only [Fml.evalM, hφ.map_bind, Fml.evalM_hom hφ ask q]
  | _, .app _ f x => by
    simp only [Fml.evalM, hφ.map_bind, hφ.map_pure, Fml.evalM_hom hφ ask x]

/-- A monad morphism that sends every oracle answer to `pure` of a pure answer sends the
evaluation to `pure` of the pure evaluation. -/
theorem Fml.evalM_eval [LawfulMonad m'] (hφ : IsHom @φ) {o : Type → Type → Type}
    (ask : ∀ ⦃Q A : Type⦄, o Q A → Q → m A) (askV : ∀ ⦃Q A : Type⦄, o Q A → Q → A)
    (h : ∀ ⦃Q A : Type⦄ (r : o Q A) (q : Q), φ (ask r q) = pure (askV r q)) {β : Type}
    (f : Fml (fun α => α) o β) : φ (f.evalM ask) = pure (f.eval askV) := by
  rw [Fml.evalM_hom hφ]
  refine Eq.trans ?_ (Fml.evalM_hom (isHom_pureHom (m := m'))
    (fun ⦃Q A : Type⦄ (r : o Q A) (q : Q) => (pure (askV r q) : Id A)) f).symm
  exact congrArg (fun g => f.evalM g) (funext fun _ => funext fun _ => funext fun r =>
    funext fun q => h r q)

theorem askOf_hom (hφ : IsHom @φ) (env : Handlers m) (envV : Handlers Id)
    (he : env.map φ = envV.map pureHom) {Q A : Type} (r : Ref Q A) (q : Q) :
    φ (askOf env r q) = pure (askId envV r q) := by
  rw [askOf, Handlers.find_map φ hφ.map_pure, he,
    ← Handlers.find_map (m := Id) (m' := m') (fun {_} x => pureHom x) (fun _ => rfl)]

/-- Decision as evaluation: a monad morphism that answers the input queries by `ans` and the
oracle-message queries from the transcript sends the decision to `pure` of the verdict. -/
theorem Desc.run_hom [LawfulMonad m] [LawfulMonad m'] (hφ : IsHom @φ) (inp : QueryImpl In.spec m)
    (ans : QueryImpl In.spec Id) (hinp : ∀ q, φ (inp q) = pure (ans q)) :
    ∀ {t : OracleProtocol} {ks : Skel} (d : Desc In W T t ks) (tr : Transcript oracleSig t)
      (lift : QueryImpl (oracleMessageSpec t tr.path) m) (env : Handlers m)
      (envV : Handlers Id) (ℓ : ℕ),
      (∀ q, φ (lift q) = pure (oracleMessageImpl t tr q)) → env.map φ = envV.map pureHom →
      φ (d.run inp tr.path (toView t tr) lift env ℓ) = pure (d.verdict ans tr envV ℓ)
  | _, _, .done _, _, _, _, _, _, _, _ => hφ.map_pure _
  | _, _, .message _ _ _ _ _ _ rest, ⟨x, tr⟩, lift, env, envV, ℓ, hl, he =>
      Desc.run_hom hφ inp ans hinp (rest x) tr lift env envV ℓ hl he
  | _, _, .oracle _ _ I _ hA _ _ _ _ _ rest, ⟨x, tr⟩, lift, env, envV, ℓ, hl, he => by
      refine Desc.run_hom hφ inp ans hinp (rest _) tr (fun q => lift (.inr q)) _ _ (ℓ + 1)
        (fun q => hl (.inr q)) ?_
      rw [Handlers.map_ext, Handlers.map_ext, he]
      congr 1
      funext q
      rw [hφ.map_map]
      erw [hl (.inl q)]
      rw [LawfulApplicative.map_pure]
      rfl
  | _, _, .challenge _ _ _ _ rest, ⟨c, tr⟩, lift, env, envV, ℓ, hl, he =>
      Desc.run_hom hφ inp ans hinp (rest c) tr lift env envV ℓ hl he
  | _, _, .check _ _ ψ args _ rest, tr, lift, env, envV, ℓ, hl, he => by
      simp only [Desc.run, Desc.verdict, hφ.map_bind,
        Fml.evalM_eval hφ _ (askId envV)
          (fun ⦃_ _⦄ r q => askOf_hom hφ env envV he r q),
        LawfulMonad.pure_bind]
      cases (ψ.inst args).eval (askId envV)
      · exact hφ.map_pure none
      · exact Desc.run_hom hφ inp ans hinp rest tr lift env envV ℓ hl he
  | _, _, .compute _ _ _ _ ψ args _ rest, tr, lift, env, envV, ℓ, hl, he => by
      simp only [Desc.run, Desc.verdict, hφ.map_bind,
        Fml.evalM_eval hφ _ (askId envV)
          (fun ⦃_ _⦄ r q => askOf_hom hφ env envV he r q),
        LawfulMonad.pure_bind]
      exact Desc.run_hom hφ inp ans hinp (rest _) tr lift env envV ℓ hl he
  | _, _, .input _ _ _ _ embed resp _ rest, tr, lift, env, envV, ℓ, hl, he => by
      refine Desc.run_hom hφ inp ans hinp (rest _) tr lift _ _ (ℓ + 1) hl ?_
      rw [Handlers.map_ext, Handlers.map_ext, he]
      congr 1
      funext q
      rw [hφ.map_map, hinp, LawfulApplicative.map_pure]
      rfl
  | _, _, .branch _ _ _ _ _ _ rest, ⟨x, tr⟩, lift, env, envV, ℓ, hl, he =>
      Desc.run_hom hφ inp ans hinp (rest x) tr lift env envV ℓ hl he
  | _, _, .stageIn _ _ _ _ _ _ rest, tr, lift, env, envV, ℓ, hl, he =>
      Desc.run_hom hφ inp ans hinp rest tr lift env envV ℓ hl he
  | _, _, .stageOut _ _ _ rest, tr, lift, env, envV, ℓ, hl, he =>
      Desc.run_hom hφ inp ans hinp rest tr lift env envV ℓ hl he
  | _, _, .mark _ rest, tr, lift, env, envV, ℓ, hl, he =>
      Desc.run_hom hφ inp ans hinp rest tr lift env envV ℓ hl he

end Hom

/-! ## Specifications as ArkLib objects -/

namespace Spec
variable {S : Type} {t : OracleProtocol} {ks : Skel}

/-- The honest prover with witness `w` and input oracle data `data`. -/
noncomputable def prover {m : Type → Type} [Monad m] (s : Spec In S W T t ks) (stmt : S) (w : W)
    (data : In.Data) : Focal oracleSig m t (fun _ => T) :=
  (s.desc stmt).prove w (In.answer data) .empty 0

/-- The pure verdict on a full transcript with input oracle data `data`. -/
noncomputable def verdict (s : Spec In S W T t ks) (stmt : S) (data : In.Data)
    (tr : Transcript oracleSig t) : Option T :=
  (s.desc stmt).verdict (In.answer data) tr .empty 0

/-- The passive oracle verifier. Its decision sends input-oracle queries to `.inr (.inl _)` and
oracle-message queries to `.inr (.inr _)`, and it keeps the input oracles as its output. -/
noncomputable def verifier (s : Spec In S W T t ks) {ι : Type} (ambient : OracleSpec ι) :
    OracleVerifier ambient t S (fun _ => T) In (fun _ => In) where
  decide stmt p v := OptionT.mk ((s.desc stmt).run
    (m := OracleComp (ambient + (pathBundle In t p).spec))
    (fun q => liftM ((ambient + (pathBundle In t p).spec).query (.inr (.inl q)))) p v
    (fun q => liftM ((ambient + (pathBundle In t p).spec).query (.inr (.inr q)))) .empty 0)
  outputMap _ _ _ := OracleMap.fst _ _

/-- Decision as evaluation for ArkLib's verifier: answered from the input data and the
transcript's oracle messages, with any ambient handler, the decision is `pure` of the verdict. -/
theorem decide_eq_verdict (s : Spec In S W T t ks) {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type} [Monad m] [LawfulMonad m] (amb : QueryImpl ambient m) (stmt : S)
    (data : In.Data) (tr : Transcript oracleSig t) :
    simulateQ (QueryImpl.addLift (r := m) amb ((pathBundle In t tr.path).answer
        (data, oracleMessages t tr))) ((s.verifier ambient).decide stmt _ (toView t tr)).run =
      pure (s.verdict stmt data tr) :=
  Desc.run_hom (isHom_simulateQ _) _ (In.answer data)
    (fun q => by rw [simulateQ_spec_query]; rfl) (s.desc stmt) tr _ .empty .empty 0
    (fun q => by rw [simulateQ_spec_query]; rfl) rfl

/-- Honest acceptance for a specification. -/
theorem verdict_isSome (s : Spec In S W T t ks) (stmt : S) (w : W) (data : In.Data)
    (tr : Transcript oracleSig t)
    (hc : (s.desc stmt).Complete w (In.answer data) .empty 0)
    (hh : (s.desc stmt).Honest w (In.answer data) tr .empty 0) :
    (s.verdict stmt data tr).isSome :=
  Desc.verdict_isSome w _ _ tr _ _ hc hh

end Spec

/-! ## Accessors by hierarchical label -/

section Accessor
open Lean Elab Term Meta

/-- A component of a hierarchical label: a stage or block name, or a round number. -/
inductive LabelComp
  | name (s : String)
  | num (n : ℕ)
  deriving BEq, Inhabited

/-- A component of a hierarchical label. -/
declare_syntax_cat specLabel
syntax ident : specLabel
syntax num : specLabel
syntax str : specLabel

/-- `tr⟦a, …, x⟧` is the move with name base `x` inside the enclosing stages, blocks and rounds
`a, …`, in a transcript of type `Spec.Tr s` or a view of type `Spec.Vw s p`. It elaborates to a
chain of projections. -/
syntax:max term noWs "⟦" specLabel,+ "⟧" : term

private def labelComp : TSyntax `specLabel → TermElabM LabelComp
  | `(specLabel| $x:ident) => pure (.name x.getId.toString)
  | `(specLabel| $n:num) => pure (.num n.getNat)
  | `(specLabel| $s:str) => pure (.name s.getString)
  | _ => throwUnsupportedSyntax

private def readString (e : Expr) : MetaM String := do
  match ← whnfD e with
  | .lit (.strVal s) => pure s
  | e' => throwError "the skeleton has a name that is not a literal: {e'}"

private def readNat (e : Expr) : MetaM (Option ℕ) := do
  let e ← instantiateMVars e
  if let some n ← evalNat e then return some n
  match ← whnfD e with
  | .lit (.natVal n) => pure (some n)
  | _ => pure none

/-- `l` is a subsequence of `ctx`. -/
private def isSubseq : List LabelComp → List LabelComp → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: ctx => if a == b then isSubseq l ctx else isSubseq (a :: l) ctx

private def nameBase (nm : Expr) : MetaM String := do
  let nm ← whnfD nm
  readString nm.getAppArgs[0]!

/-- The position among the moves of the first move that matches the label. -/
private partial def findMove (label : List LabelComp) (base : String) (ks : Expr)
    (ctx : Array LabelComp) (pos : ℕ) : MetaM ℕ := do
  let ks ← whnfD ks
  let args := ks.getAppArgs
  let hit (nm : Expr) : MetaM Bool := do
    pure ((← nameBase nm) == base && isSubseq label ctx.toList)
  match ks.getAppFn.constName? with
  | some ``Skel.cons =>
    let it ← whnfD args[0]!
    let iargs := it.getAppArgs
    let rest := args[1]!
    match it.getAppFn.constName? with
    | some ``Item.move =>
      if ← hit iargs[1]! then return pos else findMove label base rest ctx (pos + 1)
    | some ``Item.beginRound =>
      let block ← readString iargs[0]!
      let i ← readNat iargs[1]!
      let ctx := ctx.push (.name block)
      let ctx := match i with
        | some i => ctx.push (.num i)
        | none => ctx.push (.name "?")
      findMove label base rest ctx pos
    | some ``Item.endRound => findMove label base rest ctx.pop.pop pos
    | some ``Item.beginStage =>
      findMove label base rest (ctx.push (.name (← readString iargs[0]!))) pos
    | some ``Item.endStage => findMove label base rest ctx.pop pos
    | _ => findMove label base rest ctx pos
  | some ``Skel.branch | some ``Skel.opaque =>
    if ← hit args[0]! then return pos
    throwError "the label is not found before a branch; a label inside a branch is not supported"
  | _ => throwError "no move matches the label (the skeleton ends at {ks})"

/-- The skeleton of the specification in the type of a transcript or a view, and whether it is a
view. -/
private def skelOf (ty : Expr) : MetaM (Expr × Bool) := do
  let ty ← instantiateMVars ty
  let (s, isView) ← match ty.getAppFn.constName? with
    | some ``Spec.Tr => pure (ty.appArg!, false)
    | some ``Spec.Vw => pure (ty.appFn!.appArg!, true)
    | _ => throwError "a label accessor needs a transcript of type `Spec.Tr s` or a view of \
        type `Spec.Vw s p`, got {ty}"
  let sty ← whnfD (← inferType s)
  unless sty.isAppOf ``Spec do throwError "not a specification: {sty}"
  pure (sty.getAppArgs[5]!, isView)

elab_rules : term
  | `($tr⟦$cs,*⟧) => do
    let comps ← cs.getElems.toList.mapM labelComp
    let some (.name base) := comps.getLast? | throwError "a label ends with a name"
    let trE ← elabTerm tr none
    let (ks, isView) ← skelOf (← inferType trE)
    let pos ← findMove comps.dropLast base ks #[] 0
    let mut stx ← exprToSyntax trE
    if isView then stx ← `(($stx).1)
    for _ in [0:pos] do
      stx ← `(($stx).2)
    stx ← `(($stx).1)
    elabTerm stx none

end Accessor

#print axioms Handlers.find_map
#print axioms Desc.verdict_isSome
#print axioms Desc.run_hom
#print axioms Spec.decide_eq_verdict
#print axioms Spec.verdict_isSome

end Specs
