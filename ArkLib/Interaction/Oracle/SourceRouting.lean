/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Sequential
public import ArkLib.Interaction.Oracle.Claim

/-!
# Routing restricted verifiers through exported interfaces

A symbolic source route replaces queries by existing oracle programs. Ambient queries and newly
sent oracle slots retain their identity. The route is authoring data, never a concrete handler or
message payload. Interpretation uses the actual execution's accumulated handler.
-/

@[expose] public section

universe u

namespace Interaction.Oracle

open OracleComp OracleSpec TwoParty
open PFunctor.FreeM.Displayed (Decoration)

namespace Access

/-- Preserve the newly received slot while substituting programs for prior source queries. -/
def extendRoute {Messages : Type u} (source target : PFunctor.{u, u})
    (interface : OracleInterface.{u, u} Messages)
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target))) :
    QueryImpl (ofPFunctor (extend source interface))
      (OracleComp (ofPFunctor (extend target interface))) :=
  QueryImpl.add (QueryImpl.compose (queryPrior target interface) route)
    (queryLatest target interface)

/-- Extending a route reads the same concrete new message on both sides. -/
theorem compose_extendRoute {Messages : Type u} (source target : PFunctor.{u, u})
    (interface : OracleInterface.{u, u} Messages)
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (impl : QueryImpl (ofPFunctor target) Id) (message : Messages) :
    QueryImpl.compose (extendImpl target interface impl message)
      (extendRoute source target interface route) =
    extendImpl source interface (QueryImpl.compose impl route) message := by
  funext q
  cases q with
  | inl q =>
    change simulateQ (extendImpl target interface impl message)
      (simulateQ (queryPrior target interface) (route q)) = _
    rw [← QueryImpl.simulateQ_compose]
    congr 1
  | inr q => exact eval_queryLatest target interface impl message q

end Access

namespace TypeTree

/-- Extend a symbolic initial route along a public branch, preserving each fresh oracle slot. -/
def routeAfter : (tree : Oracle.TypeTree.{u}) → (oracles : tree.OracleDecoration) →
    (source target : PFunctor.{u, u}) →
    QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)) →
    (path : tree.BranchPath) →
    QueryImpl (ofPFunctor (accessAfter tree oracles source path))
      (OracleComp (ofPFunctor (accessAfter tree oracles target path)))
  | .done, _, _, _, route, _ => route
  | .public _ rest, oracles, source, target, route, path =>
    routeAfter (rest path.1) (oracles.2 path.1) source target route path.2
  | .oracle _ rest, oracles, source, target, route, path =>
    routeAfter (rest path.1) (oracles.2 path.1) (Access.extend source oracles.1)
      (Access.extend target oracles.1) (Access.extendRoute source target oracles.1 route) path.2

/-- A routed final handler uses the actual messages and input resources of the raw execution. -/
theorem ExecutionPath.compose_closingImpl_routeAfter :
    (tree : Oracle.TypeTree.{u}) → (oracles : tree.OracleDecoration) →
    (source target : PFunctor.{u, u}) →
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target))) →
    (path : tree.ExecutionPath) → (impl : QueryImpl (ofPFunctor target) Id) →
    QueryImpl.compose (path.closingImpl oracles target impl)
      (routeAfter tree oracles source target route path.toBranchPath) =
    path.closingImpl oracles source (QueryImpl.compose impl route)
  | .done, _, _, _, _, _, _ => rfl
  | .public _ rest, oracles, source, target, route, path, impl =>
    ExecutionPath.compose_closingImpl_routeAfter (rest path.1) (oracles.2 path.1)
      source target route path.2 impl
  | .oracle Messages rest, oracles, source, target, route, path, impl => by
    rcases path with ⟨message, tail⟩
    change Messages at message
    simp only [ExecutionPath.closingImpl_oracle]
    change QueryImpl.compose _
      (routeAfter (rest PUnit.unit) (oracles.2 PUnit.unit) (Access.extend source oracles.1)
        (Access.extend target oracles.1) (Access.extendRoute source target oracles.1 route)
        (ExecutionPath.toBranchPath tail)) = _
    rw [ExecutionPath.compose_closingImpl_routeAfter, Access.compose_extendRoute]

end TypeTree

namespace OpenClaim

/-- Substitute source programs in a claim, retaining its statement and output family. -/
def substSource {I J K : Type u} {source : OracleSpec.{u, u} I}
    {target : OracleSpec.{u, u} J} {Data : K → Type u}
    {Out : OracleFamily.{u, u, u} K Data} {Stmt : Type u}
    (claim : OpenClaim source Stmt Out) (route : QueryImpl source (OracleComp target)) :
    OpenClaim target Stmt Out := ⟨claim.stmt, claim.oracles.substSource route⟩

/-- Closing a substituted claim uses the same handler composed with its source programs. -/
theorem closeWith_substSource {I J K : Type u} {source : OracleSpec.{u, u} I}
    {target : OracleSpec.{u, u} J} {Data : K → Type u}
    {Out : OracleFamily.{u, u, u} K Data} {Stmt : Type u}
    (claim : OpenClaim source Stmt Out) (route : QueryImpl source (OracleComp target))
    (impl : QueryImpl target Id) :
    (claim.substSource route).closeWith impl = claim.closeWith (QueryImpl.compose impl route) := by
  simp [substSource, closeWith, VirtualOracle.eval_substSource]

/-- A source signature cast preserves claim closure under the same transported handler. -/
theorem closeWith_cast_access {I : Type u} {Stmt : Type u} {Data : I → Type u}
    {Out : OracleFamily.{u, u, u} I Data} {source target : PFunctor.{u, u}}
    (h : source = target) (claim : OpenClaim (ofPFunctor source) Stmt Out)
    (impl : QueryImpl (ofPFunctor target) Id) :
    (cast (congrArg (fun access => OpenClaim (ofPFunctor access) Stmt Out) h) claim).closeWith
      impl =
      claim.closeWith
        (cast (congrArg (fun access => QueryImpl (ofPFunctor access) Id) h.symm) impl) := by
  cases h
  rfl

/-- Close an appended claim using the resources of the same concrete prefix and suffix paths. -/
theorem closeWith_append {I : Type u}
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (first : tree.OracleDecoration)
    (second : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (path : tree.ExecutionPath)
    (rest : (suffix path.toBranchPath).ExecutionPath)
    (impl : QueryImpl (ofPFunctor initial) Id)
    {Stmt : Type u} {Data : I → Type u} {Out : OracleFamily.{u, u, u} I Data}
    (claim : OpenClaim (ofPFunctor (TypeTree.accessAfter (suffix path.toBranchPath)
      (second path.toBranchPath) (TypeTree.accessAfter tree first initial path.toBranchPath)
      rest.toBranchPath)) Stmt Out) :
    (cast (congrArg (fun access => OpenClaim (ofPFunctor access) Stmt Out)
      (TypeTree.accessAfter_append_execution tree suffix first second initial path rest).symm)
      claim).closeWith
        (TypeTree.ExecutionPath.closingImpl
          (PFunctor.FreeM.PathAlong.append TypeTree.runtimeLens tree suffix path rest)
          (Decoration.append first second) initial impl) =
    claim.closeWith (rest.closingImpl (second path.toBranchPath)
      (TypeTree.accessAfter tree first initial path.toBranchPath)
      (path.closingImpl first initial impl)) := by
  rw [OpenClaim.closeWith_cast_access
    (TypeTree.accessAfter_append_execution tree suffix first second initial path rest).symm,
    TypeTree.ExecutionPath.closingImpl_append]


end OpenClaim

namespace Verifier

/-- Substitute source programs in a local computation, preserving every ambient query. -/
def routeProgram {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (source target : PFunctor.{u, u})
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    {A : Type u} (program : OracleComp (ambient + ofPFunctor source) A) :
    OracleComp (ambient + ofPFunctor target) A :=
  simulateQ (QueryImpl.add
    (fun q => liftM ((ambient + ofPFunctor target).query (.inl q)))
    (QueryImpl.compose (fun q => liftM ((ambient + ofPFunctor target).query (.inr q))) route))
    program

/-- A routed computation is interpreted with the composed source handler, in the same order. -/
theorem simulateQ_routeProgram {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (source target : PFunctor.{u, u})
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (impl : QueryImpl (ofPFunctor target) Id) {A : Type u}
    (program : OracleComp (ambient + ofPFunctor source) A) :
    simulateQ (liftAccessImpl ambient target impl)
      (routeProgram ambient source target route program) =
    simulateQ (liftAccessImpl ambient source (QueryImpl.compose impl route)) program := by
  unfold routeProgram
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext q
  cases q with
  | inl q => rfl
  | inr q =>
    change simulateQ (liftAccessImpl ambient target impl)
      (simulateQ (show QueryImpl (ofPFunctor target)
        (OracleComp (ambient + ofPFunctor target)) from
        fun q => liftM ((ambient + ofPFunctor target).query (.inr q))) (route q)) =
      pure (simulateQ impl (route q))
    rw [← QueryImpl.simulateQ_compose]
    change simulateQ (fun q => pure (impl q)) (route q) = _
    exact simulateQ_liftTarget (n := OracleComp ambient) impl (route q)

/-- Route a restricted fragment's node programs. Ordinary leaves remain ordinary values; fresh
oracle slots remain available under their own interfaces, with no access to concrete payloads. -/
def routeFragment {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    (tree : Oracle.TypeTree.{u}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (source target : PFunctor.{u, u}) →
    QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)) →
    (Leaf : tree.BranchPath → Type u) → Fragment ambient tree roles oracles source Leaf →
    Fragment ambient tree roles oracles target Leaf
  | .done, _, _, _, _, _, _, fragment => fragment
  | .public _ rest, ⟨.sender, roles⟩, oracles, source, target, route, Leaf, fragment =>
    fun move => do
      let next ← routeProgram ambient source target route (fragment move)
      return routeFragment ambient (rest move) (roles move) (oracles.2 move) source target route
        (fun p => Leaf ⟨move, p⟩) next
  | .public _ rest, ⟨.receiver, roles⟩, oracles, source, target, route, Leaf, fragment => do
    let ⟨move, next⟩ ← routeProgram ambient source target route fragment
    return ⟨move, routeFragment ambient (rest move) (roles move) (oracles.2 move) source target
      route (fun p => Leaf ⟨move, p⟩) next⟩
  | .oracle _ rest, roles, oracles, source, target, route, Leaf, fragment => do
    let next ← routeProgram ambient (Access.extend source oracles.1)
      (Access.extend target oracles.1) (Access.extendRoute source target oracles.1 route) fragment
    return routeFragment ambient (rest PUnit.unit) (roles.2 PUnit.unit) (oracles.2 PUnit.unit)
      (Access.extend source oracles.1) (Access.extend target oracles.1)
      (Access.extendRoute source target oracles.1 route) (fun p => Leaf ⟨PUnit.unit, p⟩) next

/-- Route the final action as well as node computations, retaining its ordinary output type. -/
def routeStrategy {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (source target : PFunctor.{u, u})
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (Out : tree.BranchPath → Type u) (verifier : Strategy ambient tree roles oracles source Out) :
    Strategy ambient tree roles oracles target Out :=
  Fragment.mapOutput ambient (fun path action =>
    routeProgram ambient (TypeTree.accessAfter tree oracles source path)
      (TypeTree.accessAfter tree oracles target path)
      (TypeTree.routeAfter tree oracles source target route path) action)
    (routeFragment ambient tree roles oracles source target route _ verifier)

set_option backward.isDefEq.respectTransparency false in
/-- Routing preserves the value interpreter, using the derived source handler at the input. -/
theorem toCounterpartValue_routeFragment {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    (tree : Oracle.TypeTree.{u}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (source target : PFunctor.{u, u}) →
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target))) →
    (impl : QueryImpl (ofPFunctor target) Id) → (Leaf : tree.BranchPath → Type u) →
    (fragment : Fragment ambient tree roles oracles source Leaf) →
    toCounterpartValue ambient tree roles oracles target impl Leaf
      (routeFragment ambient tree roles oracles source target route Leaf fragment) =
    toCounterpartValue ambient tree roles oracles source (QueryImpl.compose impl route)
      Leaf fragment
  | .done, _, _, _, _, _, _, _, _ => rfl
  | .public Moves rest, ⟨.sender, roles⟩, oracles, source, target, route, impl, Leaf,
      fragment => by
    funext move
    change Moves at move
    simp only [routeFragment, toCounterpartValue, toCounterpartWith, simulateQ_bind,
      simulateQ_pure, bind_assoc, pure_bind, simulateQ_routeProgram]
    apply bind_congr
    intro next
    apply congrArg pure
    exact toCounterpartValue_routeFragment ambient (rest move) (roles move) (oracles.2 move)
      source target route impl (fun p => Leaf ⟨move, p⟩) next
  | .public Moves rest, ⟨.receiver, roles⟩, oracles, source, target, route, impl, Leaf,
      fragment => by
    let resultType := (move : Moves) ×
      StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient))
        Participant.counterpart (rest move).toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles (rest move) (roles move))
        (fun path => Leaf ⟨move, (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath⟩)
    change (simulateQ (liftAccessImpl ambient target impl)
      (routeProgram ambient source target route fragment >>= fun next => pure
        (⟨next.1, routeFragment ambient (rest next.1) (roles next.1) (oracles.2 next.1)
          source target route (fun p => Leaf ⟨next.1, p⟩) next.2⟩ :
          (move : Moves) × Fragment ambient (rest move) (roles move) (oracles.2 move)
            target (fun p => Leaf ⟨move, p⟩))) >>= fun next =>
      pure (⟨next.1, toCounterpartValue ambient (rest next.1) (roles next.1) (oracles.2 next.1)
        target impl (fun p => Leaf ⟨next.1, p⟩) next.2⟩ : resultType)) = _
    rw [simulateQ_bind, simulateQ_routeProgram]
    simp only [simulateQ_pure, bind_assoc, pure_bind]
    apply bind_congr
    intro ⟨move, next⟩
    apply congrArg pure
    apply congrArg (Sigma.mk move)
    exact toCounterpartValue_routeFragment ambient (rest move) (roles move) (oracles.2 move)
      source target route impl (fun p => Leaf ⟨move, p⟩) next
  | .oracle Messages rest, roles, oracles, source, target, route, impl, Leaf, fragment => by
    funext message
    change Messages at message
    change (simulateQ (liftAccessImpl ambient (Access.extend target oracles.1)
      (Access.extendImpl target oracles.1 impl message))
      (routeProgram ambient (Access.extend source oracles.1) (Access.extend target oracles.1)
        (Access.extendRoute source target oracles.1 route) fragment >>= fun next => pure
        (routeFragment ambient (rest PUnit.unit) (roles.2 PUnit.unit) (oracles.2 PUnit.unit)
          (Access.extend source oracles.1) (Access.extend target oracles.1)
          (Access.extendRoute source target oracles.1 route) (fun p => Leaf ⟨PUnit.unit, p⟩)
          next)) >>= fun next => pure (toCounterpartValue ambient (rest PUnit.unit)
      (roles.2 PUnit.unit) (oracles.2 PUnit.unit) (Access.extend target oracles.1)
      (Access.extendImpl target oracles.1 impl message) (fun p => Leaf ⟨PUnit.unit, p⟩) next)) = _
    rw [simulateQ_bind, simulateQ_routeProgram, Access.compose_extendRoute]
    simp only [simulateQ_pure, bind_assoc, pure_bind]
    apply bind_congr
    intro next
    apply congrArg pure
    convert (toCounterpartValue_routeFragment ambient (rest PUnit.unit) (roles.2 PUnit.unit)
      (oracles.2 PUnit.unit) (Access.extend source oracles.1) (Access.extend target oracles.1)
      (Access.extendRoute source target oracles.1 route)
      (Access.extendImpl target oracles.1 impl message) (fun p => Leaf ⟨PUnit.unit, p⟩) next)
      using 1
    rw [Access.compose_extendRoute]
    rfl

/-- Source routing commutes with the shared interpreter's finish handler. The raw finish handler
composes its actual accumulated source behavior with the symbolic accumulated route. -/
theorem toCounterpartWith_routeFragment {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (source target : PFunctor.{u, u})
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (impl : QueryImpl (ofPFunctor target) Id) (Leaf Out : tree.BranchPath → Type u)
    (finish : (p : tree.BranchPath) →
      QueryImpl (ofPFunctor (TypeTree.accessAfter tree oracles source p)) Id → Leaf p → Out p)
    (fragment : Fragment ambient tree roles oracles source Leaf) :
    toCounterpartWith ambient tree roles oracles target impl Leaf Out
      (fun p raw leaf => finish p (QueryImpl.compose raw
        (TypeTree.routeAfter tree oracles source target route p)) leaf)
      (routeFragment ambient tree roles oracles source target route Leaf fragment) =
    toCounterpartWith ambient tree roles oracles source (QueryImpl.compose impl route)
      Leaf Out finish fragment := by
  rw [toCounterpartWith_finish_eq_mapOutput, toCounterpartWith_finish_eq_mapOutput,
    toCounterpartValue_routeFragment]
  congr 1
  funext path leaf
  rw [TypeTree.ExecutionPath.compose_closingImpl_routeAfter]

/-- Both node effects and the final action use the composed exported-interface behavior.
This is an equality of open ambient programs, so expanded source queries keep their order. -/
theorem toCounterpart_routeStrategy {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (source target : PFunctor.{u, u})
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (impl : QueryImpl (ofPFunctor target) Id) (Out : tree.BranchPath → Type u)
    (verifier : Strategy ambient tree roles oracles source Out) :
    toCounterpart ambient tree roles oracles target impl Out
      (routeStrategy ambient tree roles oracles source target route Out verifier) =
    toCounterpart ambient tree roles oracles source
      (QueryImpl.compose impl route) Out verifier := by
  simp only [routeStrategy, toCounterpart]
  rw [toCounterpartWith_mapOutput, toCounterpartWith_finish_eq_mapOutput,
    toCounterpartWith_finish_eq_mapOutput, toCounterpartValue_routeFragment]
  congr 1
  funext path action
  rw [simulateQ_routeProgram, TypeTree.ExecutionPath.compose_closingImpl_routeAfter]

/-- Route a verifier's returned claim programs into the actual raw accumulated signature.
Rejection remains an ordinary terminal result and never skips a nonempty suffix. -/
def routeClaimStrategy {ι I : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (source target : PFunctor.{u, u})
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (Stmt : tree.BranchPath → Type u) (Data : tree.BranchPath → I → Type u)
    (Out : (p : tree.BranchPath) → OracleFamily.{u, u, u} I (Data p))
    (verifier : Strategy ambient tree roles oracles source (fun p => Option
      (OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles source p)) (Stmt p) (Out p)))) :
    Strategy ambient tree roles oracles target (fun p => Option
      (OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles target p)) (Stmt p) (Out p))) :=
  Fragment.mapOutput ambient (fun p action =>
    (fun result => result.map (fun claim => claim.substSource
      (TypeTree.routeAfter tree oracles source target route p))) <$> action)
    (routeStrategy ambient tree roles oracles source target route _ verifier)

/-- The final claim's closure uses the same concrete path on both sides of source routing. -/
theorem closeWith_routeAfter {I : Type u}
    (tree : Oracle.TypeTree.{u}) (oracles : tree.OracleDecoration)
    (source target : PFunctor.{u, u})
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (path : tree.ExecutionPath) (impl : QueryImpl (ofPFunctor target) Id)
    {Stmt : Type u} {Data : I → Type u} {Out : OracleFamily.{u, u, u} I Data}
    (claim : OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles source path.toBranchPath))
      Stmt Out) :
    (claim.substSource
      (TypeTree.routeAfter tree oracles source target route path.toBranchPath)).closeWith
      (path.closingImpl oracles target impl) =
    claim.closeWith (path.closingImpl oracles source (QueryImpl.compose impl route)) := by
  rw [OpenClaim.closeWith_substSource, TypeTree.ExecutionPath.compose_closingImpl_routeAfter]

/-- Routing and then closing a returned claim agrees with interpreting the original verifier
through the exported behavior. The shared interpreter supplies each finish handler from the actual
path; there is no replacement source handler or additional execution mechanism. -/
theorem toCounterpartWith_routeClaimStrategy {ι I : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (source target : PFunctor.{u, u})
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (impl : QueryImpl (ofPFunctor target) Id)
    (Stmt : tree.BranchPath → Type u) (Data : tree.BranchPath → I → Type u)
    (Out : (p : tree.BranchPath) → OracleFamily.{u, u, u} I (Data p))
    (verifier : Strategy ambient tree roles oracles source (fun p => Option
      (OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles source p)) (Stmt p) (Out p)))) :
    toCounterpartWith ambient tree roles oracles target impl _
      (fun p => OracleComp ambient (Option (ClosedClaim (Stmt p) (Out p))))
      (fun p actual action => (fun result => result.map (fun claim => claim.closeWith actual)) <$>
        simulateQ (liftAccessImpl ambient (TypeTree.accessAfter tree oracles target p) actual)
          action)
      (routeClaimStrategy ambient tree roles oracles source target route Stmt Data Out verifier) =
    toCounterpartWith ambient tree roles oracles source (QueryImpl.compose impl route) _
      (fun p => OracleComp ambient (Option (ClosedClaim (Stmt p) (Out p))))
      (fun p actual action => (fun result => result.map (fun claim => claim.closeWith actual)) <$>
        simulateQ (liftAccessImpl ambient (TypeTree.accessAfter tree oracles source p) actual)
          action) verifier := by
  simp only [routeClaimStrategy, routeStrategy]
  rw [toCounterpartWith_mapOutput, toCounterpartWith_mapOutput]
  have finish :
      (fun (p : tree.BranchPath)
        (actual : QueryImpl (ofPFunctor (TypeTree.accessAfter tree oracles target p)) Id)
        (action : OracleComp (ambient + ofPFunctor (TypeTree.accessAfter tree oracles source p))
          (Option (OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles source p))
            (Stmt p) (Out p)))) =>
        (fun result => result.map (fun claim => claim.closeWith actual)) <$>
          simulateQ (liftAccessImpl ambient (TypeTree.accessAfter tree oracles target p) actual)
            ((fun result => result.map (fun claim => claim.substSource
              (TypeTree.routeAfter tree oracles source target route p))) <$>
              routeProgram ambient (TypeTree.accessAfter tree oracles source p)
                (TypeTree.accessAfter tree oracles target p)
                (TypeTree.routeAfter tree oracles source target route p) action)) =
      (fun p actual action =>
        (fun result => result.map (fun claim => claim.closeWith (QueryImpl.compose actual
          (TypeTree.routeAfter tree oracles source target route p)))) <$>
          simulateQ (liftAccessImpl ambient (TypeTree.accessAfter tree oracles source p)
            (QueryImpl.compose actual (TypeTree.routeAfter tree oracles source target route p)))
            action) := by
    funext p actual action
    rw [simulateQ_map, simulateQ_routeProgram, Functor.map_map]
    congr 1
    funext result
    cases result with
    | none => rfl
    | some claim => exact congrArg some (OpenClaim.closeWith_substSource claim _ actual)
  rw [finish]
  exact toCounterpartWith_routeFragment ambient tree roles oracles source target route impl _
    (fun p => OracleComp ambient (Option (ClosedClaim (Stmt p) (Out p))))
    (fun p actual action => (fun result => result.map (fun claim => claim.closeWith actual)) <$>
      simulateQ (liftAccessImpl ambient (TypeTree.accessAfter tree oracles source p) actual) action)
    verifier

/-- Compose a prefix's exported interface with a suffix authored only over that interface.
The suffix receives the statement, not raw programs or a handler. Returned claims are routed into
actual accumulated access. A public abort branch can select an empty suffix; terminal rejection
alone does not skip a nonempty suffix. -/
def appendExported {ι I J : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (Stmt : tree.BranchPath → Type u)
    (Data : tree.BranchPath → I → Type u)
    (Export : (p : tree.BranchPath) → OracleFamily.{u, u, u} I (Data p))
    (FinalStmt : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (FinalData : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → J → Type u)
    (Final : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      OracleFamily.{u, u, u} J (FinalData p))
    (first : Fragment ambient tree firstRoles firstOracles initial (fun p =>
      OpenClaim (ofPFunctor (TypeTree.accessAfter tree firstOracles initial p))
        (Stmt p) (Export p)))
    (second : (p : tree.BranchPath) → Stmt p → Strategy ambient (suffix p)
      (secondRoles p) (secondOracles p) (Export p).spec.toPFunctor (fun q => Option
        (OpenClaim (ofPFunctor (TypeTree.accessAfter (suffix p) (secondOracles p)
          (Export p).spec.toPFunctor q))
          (FinalStmt (PFunctor.FreeM.Path.append tree suffix p q))
          (Final (PFunctor.FreeM.Path.append tree suffix p q))))) :
    Strategy ambient (PFunctor.FreeM.append tree suffix)
      (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles)
      (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial
      (fun p => Option (OpenClaim (ofPFunctor (TypeTree.accessAfter
        (PFunctor.FreeM.append tree suffix)
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial p))
        (FinalStmt p) (Final p))) :=
  append ambient tree suffix firstRoles secondRoles firstOracles secondOracles initial _ _ first
    (fun p claim => Fragment.mapOutput ambient (fun q action =>
      (fun result => cast (congrArg (fun access => Option (OpenClaim (ofPFunctor access)
        (FinalStmt (PFunctor.FreeM.Path.append tree suffix p q))
        (Final (PFunctor.FreeM.Path.append tree suffix p q))))
        (TypeTree.accessAfter_append tree suffix firstOracles secondOracles initial p q).symm)
        result) <$> action)
      (routeClaimStrategy ambient (suffix p) (secondRoles p) (secondOracles p)
        (Export p).spec.toPFunctor (TypeTree.accessAfter tree firstOracles initial p)
        claim.oracles.query
        (fun q => FinalStmt (PFunctor.FreeM.Path.append tree suffix p q))
        (fun q => FinalData (PFunctor.FreeM.Path.append tree suffix p q))
        (fun q => Final (PFunctor.FreeM.Path.append tree suffix p q)) (second p claim.stmt)))

end Verifier

open Interaction.Oracle.Verifier

private theorem cast_option {A B : Type u} (h : A = B) (result : Option A) :
    cast (congrArg Option h) result = result.map (cast h) := by
  cases h
  cases result <;> rfl

private theorem map_close_cast_branch {ι I : Type u} (ambient : OracleSpec.{u, u} ι)
    {Branch : Type u} (access : Branch → PFunctor.{u, u}) (Stmt : Branch → Type u)
    (Data : Branch → I → Type u) (Out : (p : Branch) → OracleFamily.{u, u, u} I (Data p))
    {p q : Branch} (h : p = q)
    (impl : QueryImpl (ofPFunctor (access q)) Id)
    (program : OracleComp ambient (Option (OpenClaim (ofPFunctor (access p)) (Stmt p) (Out p)))) :
    (fun result => result.map (fun claim => claim.closeWith impl)) <$>
      cast (congrArg (fun b => OracleComp ambient
        (Option (OpenClaim (ofPFunctor (access b)) (Stmt b) (Out b)))) h) program =
    cast (congrArg (fun b => OracleComp ambient (Option (ClosedClaim (Stmt b) (Out b)))) h)
      ((fun result => result.map (fun claim => claim.closeWith
        (cast (congrArg (fun b => QueryImpl (ofPFunctor (access b)) Id) h.symm) impl))) <$>
        program) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Execute an exported-interface composition using the actual native prefix and returned prover
continuation. The suffix queries the prefix export; its final claim closes against the source
resources of these same paths. Ambient effects retain their order and the final action runs once. -/
theorem executeStrategies_appendExported_close {ι I J : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (ofPFunctor initial) Id)
    (Stmt : tree.BranchPath → Type u)
    (Data : tree.BranchPath → I → Type u)
    (Export : (p : tree.BranchPath) → OracleFamily.{u, u, u} I (Data p))
    (FinalStmt : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (FinalData : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → J → Type u)
    (Final : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      OracleFamily.{u, u, u} J (FinalData p))
    (OutP : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix) → Type u)
    (prover : Prover.Strategy ambient (PFunctor.FreeM.append tree suffix)
      (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles) OutP)
    (first : Fragment ambient tree firstRoles firstOracles initial (fun p =>
      OpenClaim (ofPFunctor (TypeTree.accessAfter tree firstOracles initial p))
        (Stmt p) (Export p)))
    (second : (p : tree.BranchPath) → Stmt p → Strategy ambient (suffix p)
      (secondRoles p) (secondOracles p) (Export p).spec.toPFunctor (fun q => Option
        (OpenClaim (ofPFunctor (TypeTree.accessAfter (suffix p) (secondOracles p)
          (Export p).spec.toPFunctor q))
          (FinalStmt (PFunctor.FreeM.Path.append tree suffix p q))
          (Final (PFunctor.FreeM.Path.append tree suffix p q))))) :
    (fun result => (⟨result.1, result.2.1,
      result.2.2.map (fun claim => claim.closeWith (result.1.closingImpl
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl))⟩ :
      (path : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) × OutP path ×
        Option (ClosedClaim (FinalStmt path.toBranchPath) (Final path.toBranchPath)))) <$>
      executeStrategies ambient (PFunctor.FreeM.append tree suffix)
        (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles)
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl prover
        (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
          initial Stmt Data Export FinalStmt FinalData Final first second) = (do
      let ⟨path₁, continuation, mid⟩ ← TwoParty.run tree.toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles tree firstRoles)
        (StrategyOver.TwoParty.Focal.splitPrefix
          (onAppendedRuntime ambient Participant.focal tree suffix firstRoles secondRoles OutP
            prover))
        (toCounterpartValue ambient tree firstRoles firstOracles initial impl _ first)
      let ⟨rest, outP, action⟩ ← TwoParty.run
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath).toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles
          (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
          (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath))
        continuation
        (StrategyOver.TwoParty.Counterpart.mapOutput (fun rest action =>
          cast (congrArg (fun branch => OracleComp ambient
            (Option (ClosedClaim (FinalStmt branch) (Final branch))))
            (runtimeBranch_append tree suffix path₁ rest).symm) action)
          (toCounterpartWith ambient
            (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (Export (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath).spec.toPFunctor
            (mid.oracles.eval
              ((TypeTree.ExecutionPath.ofTypeTreePath path₁).closingImpl firstOracles initial impl))
            _ (fun q => OracleComp ambient (Option (ClosedClaim
              (FinalStmt (PFunctor.FreeM.Path.append tree suffix
                (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath q))
              (Final (PFunctor.FreeM.Path.append tree suffix
                (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath q)))))
            (fun q actual action => (fun result => result.map (fun claim =>
              claim.closeWith actual)) <$> simulateQ (liftAccessImpl ambient
                (TypeTree.accessAfter
                  (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
                  (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
                  (OracleFamily.spec
                    (Export (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)).toPFunctor
                  q) actual) action)
            (second (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath mid.stmt)))
      let outV ← action
      return ⟨TypeTree.ExecutionPath.ofTypeTreePath
        (cast (congrArg Interaction.TypeTree.Path
          (TypeTree.toTypeTree_append tree suffix).symm)
          (PFunctor.FreeM.Path.append tree.toTypeTree
            (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
            path₁ rest)), outP, outV⟩) := by
  simp only [executeStrategies]
  rw [toCounterpart, toCounterpartWith_finish_eq_mapOutput, run_counterpart_mapOutput]
  simp only [bind_map_left, map_bind, map_pure]
  let Leaf := fun branch => OracleComp (ambient + ofPFunctor
    (TypeTree.accessAfter (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstOracles secondOracles) initial branch))
      (Option (OpenClaim (ofPFunctor (TypeTree.accessAfter (PFunctor.FreeM.append tree suffix)
        (Decoration.append firstOracles secondOracles) initial branch))
        (FinalStmt branch) (Final branch)))
  have transport := run_onAppendedRuntime ambient tree suffix firstRoles secondRoles OutP
    (fun path => Leaf path.toBranchPath) prover
    (toCounterpartValue ambient (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstRoles secondRoles) (Decoration.append firstOracles secondOracles)
      initial impl Leaf (appendExported ambient tree suffix firstRoles secondRoles
        firstOracles secondOracles initial Stmt Data Export FinalStmt FinalData Final first second))
  rw [← transport]
  simp only [bind_map_left, appendExported, Verifier.append]
  rw [toCounterpartValue_appendFragment]
  unfold Verifier.appendValueCounterpart
  rw [TwoParty.run_appendFlat_splitPrefix]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro ⟨path₁, continuation, mid⟩
  dsimp only
  have routed := toCounterpartWith_routeClaimStrategy ambient
    (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
    (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
    (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
    (Export (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath).spec.toPFunctor
    (TypeTree.accessAfter tree firstOracles initial
      (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
    mid.oracles.query
    ((TypeTree.ExecutionPath.ofTypeTreePath path₁).closingImpl firstOracles initial impl)
    (fun q => FinalStmt (PFunctor.FreeM.Path.append tree suffix
      (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath q))
    (fun q => FinalData (PFunctor.FreeM.Path.append tree suffix
      (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath q))
    (fun q => Final (PFunctor.FreeM.Path.append tree suffix
      (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath q))
    (second (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath mid.stmt)
  simp only [VirtualOracle.eval]
  rw [← routed]
  conv_lhs =>
    rw [toCounterpartValue, toCounterpartWith_mapOutput, toCounterpartWith_mapOutput,
      toCounterpartWith_finish_eq_mapOutput]
  conv_rhs => rw [toCounterpartWith_finish_eq_mapOutput]
  simp only [run_counterpart_mapOutput, bind_map_left]
  apply bind_congr
  intro ⟨rest, outP, action⟩
  dsimp only [Leaf]
  rw [finish_append_action ambient tree suffix firstOracles secondOracles initial impl
    (fun branch => Option (OpenClaim (ofPFunctor (TypeTree.accessAfter
      (PFunctor.FreeM.append tree suffix) (Decoration.append firstOracles secondOracles)
      initial branch)) (FinalStmt branch) (Final branch))) path₁ rest]
  let firstPath := TypeTree.ExecutionPath.ofTypeTreePath path₁
  let secondPath := TypeTree.ExecutionPath.ofTypeTreePath rest
  let fullPath := TypeTree.ExecutionPath.ofTypeTreePath
    (cast (congrArg Interaction.TypeTree.Path (TypeTree.toTypeTree_append tree suffix).symm)
      (PFunctor.FreeM.Path.append tree.toTypeTree
        (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
        path₁ rest))
  let fullImpl := fullPath.closingImpl (Decoration.append firstOracles secondOracles) initial impl
  let suffixImpl := secondPath.closingImpl (secondOracles firstPath.toBranchPath)
    (TypeTree.accessAfter tree firstOracles initial firstPath.toBranchPath)
    (firstPath.closingImpl firstOracles initial impl)
  let access := TypeTree.accessAfter (PFunctor.FreeM.append tree suffix)
    (Decoration.append firstOracles secondOracles) initial
  have program := map_close_cast_branch ambient access FinalStmt FinalData Final
    (runtimeBranch_append tree suffix path₁ rest).symm fullImpl
    (simulateQ (liftAccessImpl ambient
      (TypeTree.accessAfter (suffix firstPath.toBranchPath) (secondOracles firstPath.toBranchPath)
        (TypeTree.accessAfter tree firstOracles initial firstPath.toBranchPath)
        secondPath.toBranchPath) suffixImpl)
      ((fun result => cast (congrArg (fun a => Option (OpenClaim (ofPFunctor a)
        (FinalStmt (PFunctor.FreeM.Path.append tree suffix firstPath.toBranchPath
          secondPath.toBranchPath))
        (Final (PFunctor.FreeM.Path.append tree suffix firstPath.toBranchPath
          secondPath.toBranchPath))))
        (TypeTree.accessAfter_append tree suffix firstOracles secondOracles initial
          firstPath.toBranchPath secondPath.toBranchPath).symm) result) <$> action))
  rw [simulateQ_map, Functor.map_map] at program
  have joined := TypeTree.ExecutionPath.ofTypeTreePath_append tree suffix path₁ rest
  have handler := congr_arg_heq (fun p : TypeTree.ExecutionPath
    (PFunctor.FreeM.append tree suffix) =>
    p.closingImpl (Decoration.append firstOracles secondOracles) initial impl) joined
  have closing := TypeTree.ExecutionPath.closingImpl_append tree suffix firstOracles secondOracles
    initial firstPath secondPath impl
  have sameHandler := handler.trans ((cast_heq _ _).symm.trans (heq_of_eq closing))
  have handlers : cast (congrArg (fun a => QueryImpl (ofPFunctor a) Id)
      (TypeTree.accessAfter_append tree suffix firstOracles secondOracles initial
        firstPath.toBranchPath secondPath.toBranchPath))
      (cast (congrArg (fun p => QueryImpl (ofPFunctor (access p)) Id)
        (runtimeBranch_append tree suffix path₁ rest)) fullImpl) = suffixImpl := by
    exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans sameHandler))
  have close :
      (fun result => result.map (fun claim => claim.closeWith
        (cast (congrArg (fun p => QueryImpl (ofPFunctor (access p)) Id)
          (runtimeBranch_append tree suffix path₁ rest)) fullImpl))) ∘
      (fun result => cast (congrArg (fun a => Option (OpenClaim (ofPFunctor a)
        (FinalStmt (PFunctor.FreeM.Path.append tree suffix firstPath.toBranchPath
          secondPath.toBranchPath))
        (Final (PFunctor.FreeM.Path.append tree suffix firstPath.toBranchPath
          secondPath.toBranchPath))))
        (TypeTree.accessAfter_append tree suffix firstOracles secondOracles initial
          firstPath.toBranchPath secondPath.toBranchPath).symm) result) =
      (fun result => result.map (fun claim => claim.closeWith suffixImpl)) := by
    funext result
    dsimp only [Function.comp_apply]
    rw [cast_option (congrArg (fun a => OpenClaim (ofPFunctor a)
      (FinalStmt (PFunctor.FreeM.Path.append tree suffix firstPath.toBranchPath
        secondPath.toBranchPath))
      (Final (PFunctor.FreeM.Path.append tree suffix firstPath.toBranchPath
        secondPath.toBranchPath)))
      (TypeTree.accessAfter_append tree suffix firstOracles secondOracles initial
        firstPath.toBranchPath secondPath.toBranchPath).symm), Option.map_map]
    congr 1
    funext claim
    dsimp only [Function.comp_apply]
    rw [OpenClaim.closeWith_cast_access
      (TypeTree.accessAfter_append tree suffix firstOracles secondOracles initial
        firstPath.toBranchPath secondPath.toBranchPath).symm, handlers]
  unfold Function.comp at close
  rw [close] at program
  have final := congrArg (fun action => action >>= fun outV =>
    pure (⟨fullPath, outP, outV⟩ :
      (path : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) × OutP path ×
        Option (ClosedClaim (FinalStmt path.toBranchPath) (Final path.toBranchPath)))) program
  simpa only [simulateQ_map, bind_map_left, Function.comp_apply] using final


end Interaction.Oracle
