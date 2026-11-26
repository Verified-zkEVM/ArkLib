/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Legacy.Verifier
public import ArkLib.Interaction.LiftContext
public import ArkLib.OracleReduction.LiftContext.Reduction

/-!
# Context lifting and the legacy embedding

A legacy statement lens gives a core statement lens with constant output families, and a legacy
context lens gives a core context lens whose prover output is the pair of output statement and
witness. Embedding commutes with lifting along these lenses:

* `Legacy.embedVerifier_liftContext`: the embedded lifted legacy verifier is the core lift of the
  embedded verifier;
* `Legacy.embedProver_liftContext`: the embedded lifted legacy prover is the core lift of the
  embedded prover;
* `Legacy.embedReduction_liftContext`: the same for reductions.

These are equalities of the embedded objects, so lifting then embedding agrees with embedding
then lifting on every run.
-/

@[expose] public section

namespace Interaction
open PFunctor TwoParty.Lens OracleComp OracleSpec ProtocolSpec Legacy

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}

/-- A legacy statement lens as a core statement lens with constant output families. -/
def StatementLens.ofLegacy
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) :
    StatementLens (protocol pSpec) OuterStmtIn InnerStmtIn (fun _ => OuterStmtOut)
      (fun _ => InnerStmtOut) where
  proj := lens.proj
  lift x _ t := lens.lift x t

/-- A legacy context lens as a core context lens. The prover output is the legacy pair of output
statement and witness, lifted by the legacy context lift. -/
def ContextLens.ofLegacy
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut OuterWitIn OuterWitOut
      InnerWitIn InnerWitOut) :
    ContextLens plainSig (protocol pSpec) OuterStmtIn InnerStmtIn OuterWitIn InnerWitIn
      (fun _ => OuterStmtOut) (fun _ => InnerStmtOut) (fun _ => OuterStmtOut × OuterWitOut)
      (fun _ => InnerStmtOut × InnerWitOut) where
  stmt := StatementLens.ofLegacy lens.stmt
  wit :=
    { proj x w := lens.wit.proj (x, w)
      lift x w _ o := lens.lift (x, w) o }

namespace Legacy

/-- Embedding commutes with lifting a verifier. -/
theorem embedVerifier_liftContext
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : _root_.Verifier oSpec InnerStmtIn InnerStmtOut pSpec) :
    embedVerifier (V.liftContext lens) =
      (embedVerifier V).liftContext (StatementLens.ofLegacy lens) := by
  simp only [embedVerifier, Interaction.Verifier.liftContext, _root_.Verifier.liftContext,
    StatementLens.ofLegacy, LawfulMonad.bind_pure_comp]

/-- A lifted legacy prover's round slot is the inner slot with the outer input kept beside the
next state. -/
theorem roundSlot_liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut OuterWitIn OuterWitOut
      InnerWitIn InnerWitOut)
    (P : _root_.Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) (j : Fin n)
    (d : Direction) (hd : pSpec.dir j = d) (st : P.PrvState j.castSucc) (x : OuterStmtIn)
    (w : OuterWitIn) :
    roundSlot (P.liftContext lens) j d hd (st, x, w) =
      Choice.map .focal _ (fun _ st' => (st', x, w)) <$> roundSlot P j d hd st := by
  cases d with
  | P_to_V =>
    simp only [roundSlot, _root_.Prover.liftContext]
    refine (map_bind _ _ _).trans ?_
    refine Eq.trans ?_ (Functor.map_map _ _ _).symm
    refine (bind_congr fun _ => map_pure _ _).trans ?_
    exact LawfulMonad.bind_pure_comp _ _
  | V_to_P =>
    simp only [roundSlot, _root_.Prover.liftContext, LawfulMonad.bind_pure_comp]
    rfl

/-- The embedded lifted legacy prover from round `k` is the embedded inner prover from round
`k`, with its output lifted. -/
theorem embedFrom_liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut OuterWitIn OuterWitOut
      InnerWitIn InnerWitOut)
    (P : _root_.Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec)
    (x : OuterStmtIn) (w : OuterWitIn) :
    (m k : ℕ) → (h : k + m = n) → (st : P.PrvState ⟨k, by omega⟩) →
    embedFrom (P.liftContext lens) k m h (st, x, w) =
      Strategy.mapOutput (fun _ o => lens.lift (x, w) o) (embedFrom P k m h st)
  | 0, k, h, st => by
    subst h
    change (P.liftContext lens).output (st, x, w) = (fun o => lens.lift (x, w) o) <$> P.output st
    simp only [_root_.Prover.liftContext, LawfulMonad.bind_pure_comp]
  | m + 1, k, h, st => by
    simp only [embedFrom]
    rw [roundSlot_liftContext]
    refine (Functor.map_map _ _ _).trans
      ((congrArg (fun g => g <$> _) (funext fun c => ?_)).trans (Functor.map_map _ _ _).symm)
    refine (congrFun (Choice.map_comp _ _ _ _) c).trans ?_
    refine Eq.trans ?_ (congrFun (Choice.map_comp _ _ _ _) c).symm
    exact congrArg (fun g => Choice.map .focal _ g c)
      (funext fun _ => funext fun st' => embedFrom_liftContext lens P x w m (k + 1) _ st')

/-- Embedding commutes with lifting a prover. -/
theorem embedProver_liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut OuterWitIn OuterWitOut
      InnerWitIn InnerWitOut)
    (P : _root_.Prover oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
    embedProver (P.liftContext lens) =
      Interaction.Prover.liftContext (ContextLens.ofLegacy (pSpec := pSpec) lens).stmt.proj
        (ContextLens.ofLegacy lens).wit (embedProver P) := by
  funext x w
  exact embedFrom_liftContext lens P x w n 0 (Nat.zero_add n) _

/-- Embedding commutes with lifting a reduction. -/
theorem embedReduction_liftContext
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut OuterWitIn OuterWitOut
      InnerWitIn InnerWitOut)
    (R : _root_.Reduction oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut pSpec) :
    embedReduction (R.liftContext lens) =
      (embedReduction R).liftContext (ContextLens.ofLegacy lens) := by
  simp only [embedReduction, _root_.Reduction.liftContext, Interaction.Reduction.liftContext,
    embedProver_liftContext, embedVerifier_liftContext]
  rfl

end Legacy

end Interaction
