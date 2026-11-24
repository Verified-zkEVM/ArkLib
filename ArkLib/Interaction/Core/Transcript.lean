/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Signature

/-!
# Transcripts

The transcript of a run lists every move in order: prover messages, verifier challenges and,
for oracle protocols, oracle messages. The signature lens decides how each move is presented.
With `plainSig` the transcript has every message and challenge. With `oracleSig` it also has
every oracle message. With `viewSig` it is the verifier's view, which keeps a marker in place of
each oracle message.

A `PartialTranscript` records a run that has not reached the leaf: the moves made so far, in
order, presented by the same signature lens.

A transcript determines the *path* of the protocol tree that the run followed: the branch
choices made by messages that select the next subprotocol. Challenges and oracle messages never
select a branch, so the path omits them.

`Transcript l s` is PolyFun's `PathAlong l s`, kept reducible as VCVio does for `OracleComp` over
`FreeM`. Statements in the core use the names in this file. `ofPathAlong` and `toPathAlong` are
the boundary for generic PolyFun constructions, which should use them instead of unfolding.
-/

@[expose] public section

universe u v w uA

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens

variable {P : PFunctor.{uA, u}} {α : Type v} {β : Type w}

/-- The transcript of a run of the protocol `s`: every move in order, presented by the
signature lens `l`. -/
@[reducible]
def Transcript (l : PFunctor.Lens P rolePoly.{u}) (s : FreeM P α) : Type u :=
  PathAlong l s

namespace Transcript

variable {l : PFunctor.Lens P rolePoly.{u}}

/-- View a PolyFun runtime path as a transcript. -/
@[reducible]
def ofPathAlong {s : FreeM P α} (tr : PathAlong l s) : Transcript l s := tr

/-- The PolyFun runtime path underlying a transcript. -/
@[reducible]
def toPathAlong {s : FreeM P α} (tr : Transcript l s) : PathAlong l s := tr

/-- The path of the protocol tree that the transcript follows. It keeps the branch choices and
drops challenges and oracle messages. -/
@[reducible]
def path {s : FreeM P α} (tr : Transcript l s) : Path s :=
  projectPathAlong l s tr

/-- Join a transcript of `s₁` with a transcript of the continuation that its path selects. -/
@[reducible]
def append (s₁ : FreeM P α) (s₂ : Path s₁ → FreeM P β) (tr₁ : Transcript l s₁)
    (tr₂ : Transcript l (s₂ tr₁.path)) : Transcript l (s₁.append s₂) :=
  PathAlong.append l s₁ s₂ tr₁ tr₂

/-- Split a transcript of an appended protocol into the prefix transcript and the transcript of
the continuation that the prefix path selects. -/
@[reducible]
def split (s₁ : FreeM P α) (s₂ : Path s₁ → FreeM P β) (tr : Transcript l (s₁.append s₂)) :
    (tr₁ : Transcript l s₁) × Transcript l (s₂ tr₁.path) :=
  PathAlong.split l s₁ s₂ tr

/-- Present every move of a transcript through a move map into another signature lens. The
path is unchanged, by `path_mapMoves`. -/
@[reducible]
def mapMoves {l' : PFunctor.Lens P rolePoly.{u}} (g : PathAlong.MoveMap l l') {s : FreeM P α}
    (tr : Transcript l s) : Transcript l' s :=
  PathAlong.mapMoves g s tr

@[simp]
theorem path_append (s₁ : FreeM P α) (s₂ : Path s₁ → FreeM P β) (tr₁ : Transcript l s₁)
    (tr₂ : Transcript l (s₂ tr₁.path)) :
    (append s₁ s₂ tr₁ tr₂).path = Path.append s₁ s₂ tr₁.path tr₂.path :=
  PathAlong.projectPathAlong_append l s₁ s₂ tr₁ tr₂

@[simp]
theorem split_append (s₁ : FreeM P α) (s₂ : Path s₁ → FreeM P β) (tr₁ : Transcript l s₁)
    (tr₂ : Transcript l (s₂ tr₁.path)) :
    split s₁ s₂ (append s₁ s₂ tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  PathAlong.split_append l s₁ s₂ tr₁ tr₂

@[simp]
theorem append_split (s₁ : FreeM P α) (s₂ : Path s₁ → FreeM P β)
    (tr : Transcript l (s₁.append s₂)) :
    append s₁ s₂ (split s₁ s₂ tr).1 (split s₁ s₂ tr).2 = tr :=
  PathAlong.append_split l s₁ s₂ tr

@[simp]
theorem path_mapMoves {l' : PFunctor.Lens P rolePoly.{u}} (g : PathAlong.MoveMap l l')
    {s : FreeM P α} (tr : Transcript l s) : (tr.mapMoves g).path = tr.path :=
  projectPathAlong_mapMoves g s tr

end Transcript

/-- The transcripts of `s` that follow the path `p`. -/
abbrev TranscriptAt (l : PFunctor.Lens P rolePoly.{u}) (s : FreeM P α) (p : Path s) :=
  {tr : Transcript l s // tr.path = p}

/-- A transcript that may stop before the leaf: the moves already made along the protocol `s`,
presented by the signature lens `l`. -/
def PartialTranscript (l : PFunctor.Lens P rolePoly.{u}) : (s : FreeM P α) → Type u
  | .pure _ => Option PEmpty
  | .liftBind a next => Option ((x : Move l a) × PartialTranscript l (next (l.toFunB a x)))

namespace PartialTranscript

variable {l : PFunctor.Lens P rolePoly.{u}}

/-- The empty partial transcript, with no moves made yet. -/
def empty {s : FreeM P α} : PartialTranscript l s := by cases s <;> exact none

/-- The partial transcript that starts with move `x` and continues with the partial transcript
`tail` of the rest of the protocol. -/
def cons {a : P.A} {next : P.B a → FreeM P α} (x : Move l a)
    (tail : PartialTranscript l (next (l.toFunB a x))) :
    PartialTranscript l (.liftBind a next) := some ⟨x, tail⟩

/-- The number of moves already made. -/
def length : {s : FreeM P α} → PartialTranscript l s → Nat
  | .pure _, _ => 0
  | .liftBind _ _, none => 0
  | .liftBind _ _, some ⟨_, tail⟩ => tail.length + 1

/-- A completed transcript as a partial transcript. It keeps every move. -/
def ofTranscript : (s : FreeM P α) → Transcript l s → PartialTranscript l s
  | .pure _, _ => none
  | .liftBind _ next, ⟨x, tr⟩ => .cons x (ofTranscript (next (l.toFunB _ x)) tr)

end PartialTranscript

end Interaction.Core
