/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.Knowledge

/-!
# Backward extraction through dependent native append

The suffix tree is selected by the native structural branch. Its witness maps and challenge
schedule may also depend on the actual concrete first path. Native prefix and complete-path
correspondences identify the exact knowledge states; named backward extraction composes in
reverse execution order. Every component prover law and fixed-prefix bad-challenge bound is
preserved with the same sampler and error. Actual verifier freshness and closed-claim relation
seams are supplied by `KnowledgeComposition`.
-/

@[expose] public section

universe u w

namespace Interaction.Oracle.Security

open Interaction.Oracle.TypeTree PFunctor.FreeM

namespace RoundExtractor

/-- Join two extractors along the actual first path, keeping its terminal knowledge state as
the suffix input state. Suffix tree choice uses exactly the native structural path. -/
def append : {tree : Oracle.TypeTree.{u}} → {state : KnowledgeState.{w}} →
    (first : RoundExtractor tree state) → (suffix : tree.BranchPath → Oracle.TypeTree.{u}) →
    ((path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (terminalState first path)) → RoundExtractor (PFunctor.FreeM.append tree suffix) state
  | .done, _, _, _, second => second PUnit.unit
  | .public _ _, _, first, suffix, second => fun move =>
      ⟨(first move).1, (first move).2.1,
        append (first move).2.2 (fun path => suffix ⟨move, path⟩)
          (fun path => second ⟨move, path⟩)⟩
  | .oracle _ _, _, first, suffix, second => fun message =>
      ⟨(first message).1, (first message).2.1,
        append (first message).2.2 (fun path => suffix ⟨PUnit.unit, path⟩)
          (fun path => second ⟨message, path⟩)⟩

/-- The terminal state of native append is exactly the selected suffix terminal state. -/
theorem terminalState_append : {tree : Oracle.TypeTree.{u}} →
    {state : KnowledgeState.{w}} → (first : RoundExtractor tree state) →
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) →
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (terminalState first path)) →
    (path : tree.ExecutionPath) → (rest : (suffix path.toBranchPath).ExecutionPath) →
    terminalState (append first suffix second)
      (PathAlong.append TypeTree.runtimeLens tree suffix path rest) =
        terminalState (second path) rest
  | .done, _, _, _, _, path, _ => by cases path; rfl
  | .public _ _, _, first, suffix, second, path, rest =>
      terminalState_append (first path.1).2.2 (fun p => suffix ⟨path.1, p⟩)
        (fun p => second ⟨path.1, p⟩) path.2 rest
  | .oracle _ _, _, first, suffix, second, path, rest =>
      terminalState_append (first path.1).2.2 (fun p => suffix ⟨PUnit.unit, p⟩)
        (fun p => second ⟨path.1, p⟩) path.2 rest

/-- Backward extraction on the actual appended path composes the two named extractors. -/
theorem extractWitness_append : {tree : Oracle.TypeTree.{u}} →
    {state : KnowledgeState.{w}} → (first : RoundExtractor tree state) →
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) →
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (terminalState first path)) →
    (path : tree.ExecutionPath) → (rest : (suffix path.toBranchPath).ExecutionPath) →
    (witness : (terminalState (second path) rest).Witness) →
    extractWitness (append first suffix second)
      (PathAlong.append TypeTree.runtimeLens tree suffix path rest)
      ((terminalState_append first suffix second path rest).symm ▸ witness) =
    extractWitness first path (extractWitness (second path) rest witness)
  | .done, _, _, _, _, path, _, _ => by cases path; rfl
  | .public _ _, _, first, suffix, second, path, rest, witness =>
      congrArg (first path.1).2.1
        (extractWitness_append (first path.1).2.2 (fun p => suffix ⟨path.1, p⟩)
          (fun p => second ⟨path.1, p⟩) path.2 rest witness)
  | .oracle _ _, _, first, suffix, second, path, rest, witness =>
      congrArg (first path.1).2.1
        (extractWitness_append (first path.1).2.2 (fun p => suffix ⟨PUnit.unit, p⟩)
          (fun p => second ⟨path.1, p⟩) path.2 rest witness)

/-- Prover-message preservation holds through the dependent native composition. -/
theorem isProverPreserving_append : {tree : Oracle.TypeTree.{u}} →
    {state : KnowledgeState.{w}} → (first : RoundExtractor tree state) →
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) →
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (terminalState first path)) →
    (firstRoles : tree.RoleDecoration) →
    (secondRoles : (path : tree.BranchPath) → (suffix path).RoleDecoration) →
    IsProverPreserving first firstRoles →
    (∀ path, IsProverPreserving (second path) (secondRoles path.toBranchPath)) →
    IsProverPreserving (append first suffix second)
      (Displayed.Decoration.append firstRoles secondRoles)
  | .done, _, _, _, _, _, _, _, after => after PUnit.unit
  | .public _ _, _, first, suffix, second, firstRoles, secondRoles, before, after =>
      ⟨before.1, fun move => isProverPreserving_append (first move).2.2
        (fun p => suffix ⟨move, p⟩) (fun p => second ⟨move, p⟩) (firstRoles.2 move)
        (fun p => secondRoles ⟨move, p⟩) (before.2 move) (fun p => after ⟨move, p⟩)⟩
  | .oracle _ _, _, first, suffix, second, firstRoles, secondRoles, before, after =>
      ⟨before.1, fun message => isProverPreserving_append (first message).2.2
        (fun p => suffix ⟨PUnit.unit, p⟩) (fun p => second ⟨message, p⟩)
        (firstRoles.2 PUnit.unit) (fun p => secondRoles ⟨PUnit.unit, p⟩)
        (before.2 message) (fun p => after ⟨message, p⟩)⟩

/-- Join fresh-challenge/error metadata without resampling or adding errors at prover steps. -/
def appendSchedule : {tree : Oracle.TypeTree.{0}} →
    (suffix : tree.BranchPath → Oracle.TypeTree.{0}) →
    (firstRoles : tree.RoleDecoration) →
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration) →
    ChallengeSchedule tree firstRoles →
    ((path : tree.ExecutionPath) → ChallengeSchedule (suffix path.toBranchPath)
      (secondRoles path.toBranchPath)) →
    ChallengeSchedule (PFunctor.FreeM.append tree suffix)
      (Displayed.Decoration.append firstRoles secondRoles)
  | .done, _, _, _, _, second => second PUnit.unit
  | .public _ _, suffix, firstRoles, secondRoles, first, second =>
      ⟨first.1, fun move => appendSchedule (fun p => suffix ⟨move, p⟩) (firstRoles.2 move)
        (fun p => secondRoles ⟨move, p⟩) (first.2 move) (fun p => second ⟨move, p⟩)⟩
  | .oracle _ _, suffix, firstRoles, secondRoles, first, second =>
      fun message => appendSchedule (fun p => suffix ⟨PUnit.unit, p⟩)
        (firstRoles.2 PUnit.unit) (fun p => secondRoles ⟨PUnit.unit, p⟩)
        (first message) (fun p => second ⟨message, p⟩)

/-- Both stages retain every fixed-prefix bad-challenge bound and its stated error. -/
theorem isLocallyBounded_append : {tree : Oracle.TypeTree.{0}} →
    {state : KnowledgeState.{w}} → (first : RoundExtractor tree state) →
    (suffix : tree.BranchPath → Oracle.TypeTree.{0}) →
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (terminalState first path)) →
    (firstRoles : tree.RoleDecoration) →
    (secondRoles : (path : tree.BranchPath) → (suffix path).RoleDecoration) →
    (firstSchedule : ChallengeSchedule tree firstRoles) →
    (secondSchedule : (path : tree.ExecutionPath) →
      ChallengeSchedule (suffix path.toBranchPath) (secondRoles path.toBranchPath)) →
    IsLocallyBounded first firstRoles firstSchedule →
    (∀ path, IsLocallyBounded (second path) (secondRoles path.toBranchPath)
      (secondSchedule path)) →
    IsLocallyBounded (append first suffix second)
      (Displayed.Decoration.append firstRoles secondRoles)
      (appendSchedule suffix firstRoles secondRoles firstSchedule secondSchedule)
  | .done, _, _, _, _, _, _, _, _, _, after => after PUnit.unit
  | .public _ _, _, first, suffix, second, ⟨.sender, roles⟩, secondRoles,
      firstSchedule, secondSchedule, before, after =>
      fun move => isLocallyBounded_append (first move).2.2 (fun p => suffix ⟨move, p⟩)
        (fun p => second ⟨move, p⟩) (roles move) (fun p => secondRoles ⟨move, p⟩)
        (firstSchedule.2 move) (fun p => secondSchedule ⟨move, p⟩) (before move)
        (fun p => after ⟨move, p⟩)
  | .public _ _, _, first, suffix, second, ⟨.receiver, roles⟩, secondRoles,
      firstSchedule, secondSchedule, before, after =>
      ⟨before.1, fun move => isLocallyBounded_append (first move).2.2
        (fun p => suffix ⟨move, p⟩) (fun p => second ⟨move, p⟩) (roles move)
        (fun p => secondRoles ⟨move, p⟩) (firstSchedule.2 move)
        (fun p => secondSchedule ⟨move, p⟩) (before.2 move) (fun p => after ⟨move, p⟩)⟩
  | .oracle _ _, _, first, suffix, second, firstRoles, secondRoles,
      firstSchedule, secondSchedule, before, after =>
      fun message => isLocallyBounded_append (first message).2.2
        (fun p => suffix ⟨PUnit.unit, p⟩) (fun p => second ⟨message, p⟩)
        (firstRoles.2 PUnit.unit) (fun p => secondRoles ⟨PUnit.unit, p⟩)
        (firstSchedule message) (fun p => secondSchedule ⟨message, p⟩) (before message)
        (fun p => after ⟨message, p⟩)

/-- Transport exactly the concrete messages retained by a native left-prefix embedding. -/
def liftPrefixMessages : {tree residual : Oracle.TypeTree.{u}} →
    (spine : Cursor.Spine tree residual) → (suffix : tree.BranchPath → Oracle.TypeTree.{u}) →
    PrefixMessages.Along spine → PrefixMessages.Along (spine.liftAppend suffix)
  | _, _, .root _, _, messages => messages
  | .public _ _, _, .down move tail, suffix, messages =>
      liftPrefixMessages tail (fun p => suffix ⟨move, p⟩) messages
  | .oracle _ _, _, .down answer tail, suffix, messages =>
      ⟨messages.1, liftPrefixMessages tail (fun p => suffix ⟨answer, p⟩) messages.2⟩

/-- Embed a concrete first-stage prefix through native dependent append. -/
def appendPrefix {tree : Oracle.TypeTree.{u}} (pfx : ExecutionPrefix tree)
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) :
    ExecutionPrefix (PFunctor.FreeM.append tree suffix) :=
  ⟨pfx.cursor.liftAppend suffix, liftPrefixMessages pfx.cursor.spine suffix pfx.messages⟩

/-- A first-stage prefix keeps exactly its witness carrier and knowledge predicate after append. -/
theorem knowledgeState_appendPrefix {tree residual : Oracle.TypeTree.{u}}
    {state : KnowledgeState.{w}} (first : RoundExtractor tree state)
    (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (terminalState first path))
    (spine : Cursor.Spine tree residual) (messages : PrefixMessages.Along spine) :
    knowledgeState (append first suffix second)
      (appendPrefix ⟨⟨residual, spine⟩, messages⟩ suffix) =
      stateAt first spine messages := by
  induction spine generalizing state with
  | root => rfl
  | @down position next residual answer tail ih =>
      cases position with
      | «public» =>
          exact ih (first answer).2.2 (fun p => suffix ⟨answer, p⟩)
            (fun p => second ⟨answer, p⟩) messages
      | «oracle» =>
          cases answer
          exact ih (first messages.1).2.2 (fun p => suffix ⟨PUnit.unit, p⟩)
            (fun p => second ⟨messages.1, p⟩) messages.2

/-- Follow an actual first-stage execution path, then a concrete suffix prefix. -/
def appendSuffixPrefix : (tree : Oracle.TypeTree.{u}) →
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) → (path : tree.ExecutionPath) →
    ExecutionPrefix (suffix path.toBranchPath) → ExecutionPrefix (PFunctor.FreeM.append tree suffix)
  | .done, _, _, pfx => pfx
  | .public _ _, suffix, path, pfx =>
      let tail := appendSuffixPrefix _ (fun p => suffix ⟨path.1, p⟩) path.2 pfx
      ⟨Cursor.down path.1 tail.cursor, tail.messages⟩
  | .oracle _ _, suffix, path, pfx =>
      let tail := appendSuffixPrefix _ (fun p => suffix ⟨PUnit.unit, p⟩) path.2 pfx
      ⟨Cursor.down PUnit.unit tail.cursor, ⟨path.1, tail.messages⟩⟩

/-- The concrete suffix embedding has the canonical native joined cursor. -/
theorem cursor_appendSuffixPrefix : (tree : Oracle.TypeTree.{u}) →
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) → (path : tree.ExecutionPath) →
    (pfx : ExecutionPrefix (suffix path.toBranchPath)) →
    (appendSuffixPrefix tree suffix path pfx).cursor =
      Cursor.joinRight tree suffix path.toBranchPath pfx.cursor
  | .done, _, path, _ => by cases path; rfl
  | .public Moves next, suffix, path, pfx => by
      change Cursor.down (P := TypeTree.basePFunctor) (a := Position.public Moves)
        (next := fun move => PFunctor.FreeM.append (next move) (fun p => suffix ⟨move, p⟩))
        path.1 (appendSuffixPrefix _ (fun p => suffix ⟨path.1, p⟩) path.2 pfx).cursor =
        Cursor.down (P := TypeTree.basePFunctor) (a := Position.public Moves)
          (next := fun move => PFunctor.FreeM.append (next move) (fun p => suffix ⟨move, p⟩))
          path.1 (Cursor.joinRight _ (fun p => suffix ⟨path.1, p⟩)
            (ExecutionPath.toBranchPath path.2) pfx.cursor)
      exact congrArg (Cursor.down (P := TypeTree.basePFunctor) (a := Position.public Moves)
        (next := fun move => PFunctor.FreeM.append (next move) (fun p => suffix ⟨move, p⟩)) path.1)
        (cursor_appendSuffixPrefix _ (fun p => suffix ⟨path.1, p⟩) path.2 pfx)
  | .oracle Messages next, suffix, path, pfx => by
      change Cursor.down (P := TypeTree.basePFunctor) (a := Position.oracle Messages)
        (next := fun marker => PFunctor.FreeM.append (next marker) (fun p => suffix ⟨marker, p⟩))
        PUnit.unit (appendSuffixPrefix _ (fun p => suffix ⟨PUnit.unit, p⟩) path.2 pfx).cursor =
        Cursor.down (P := TypeTree.basePFunctor) (a := Position.oracle Messages)
          (next := fun marker => PFunctor.FreeM.append (next marker) (fun p => suffix ⟨marker, p⟩))
          PUnit.unit (Cursor.joinRight _ (fun p => suffix ⟨PUnit.unit, p⟩)
            (ExecutionPath.toBranchPath path.2) pfx.cursor)
      exact congrArg (Cursor.down (P := TypeTree.basePFunctor) (a := Position.oracle Messages)
        (next := fun marker => PFunctor.FreeM.append (next marker) (fun p => suffix ⟨marker, p⟩))
        PUnit.unit)
        (cursor_appendSuffixPrefix _ (fun p => suffix ⟨PUnit.unit, p⟩) path.2 pfx)

/-- A native suffix prefix has exactly the selected suffix knowledge state. -/
theorem knowledgeState_appendSuffixPrefix : {tree : Oracle.TypeTree.{u}} →
    {state : KnowledgeState.{w}} → (first : RoundExtractor tree state) →
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) →
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (terminalState first path)) → (path : tree.ExecutionPath) →
    (pfx : ExecutionPrefix (suffix path.toBranchPath)) →
    knowledgeState (append first suffix second) (appendSuffixPrefix tree suffix path pfx) =
      knowledgeState (second path) pfx
  | .done, _, _, _, _, path, _ => by cases path; rfl
  | .public _ _, _, first, suffix, second, path, pfx =>
      knowledgeState_appendSuffixPrefix (first path.1).2.2 (fun p => suffix ⟨path.1, p⟩)
        (fun p => second ⟨path.1, p⟩) path.2 pfx
  | .oracle _ _, _, first, suffix, second, path, pfx =>
      knowledgeState_appendSuffixPrefix (first path.1).2.2 (fun p => suffix ⟨PUnit.unit, p⟩)
        (fun p => second ⟨path.1, p⟩) path.2 pfx

/-- The remaining maps at a native suffix prefix are exactly the selected suffix extractor. -/
theorem remainingExtractor_appendSuffixPrefix : {tree : Oracle.TypeTree.{u}} →
    {state : KnowledgeState.{w}} → (first : RoundExtractor tree state) →
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) →
    (second : (path : tree.ExecutionPath) → RoundExtractor (suffix path.toBranchPath)
      (terminalState first path)) → (path : tree.ExecutionPath) →
    (pfx : ExecutionPrefix (suffix path.toBranchPath)) →
    HEq (remainingExtractor (append first suffix second) (appendSuffixPrefix tree suffix path pfx))
      (remainingExtractor (second path) pfx)
  | .done, _, _, _, _, path, _ => by cases path; rfl
  | .public _ _, _, first, suffix, second, path, pfx =>
      remainingExtractor_appendSuffixPrefix (first path.1).2.2 (fun p => suffix ⟨path.1, p⟩)
        (fun p => second ⟨path.1, p⟩) path.2 pfx
  | .oracle _ _, _, first, suffix, second, path, pfx =>
      remainingExtractor_appendSuffixPrefix (first path.1).2.2 (fun p => suffix ⟨PUnit.unit, p⟩)
        (fun p => second ⟨path.1, p⟩) path.2 pfx

end RoundExtractor

end Interaction.Oracle.Security
