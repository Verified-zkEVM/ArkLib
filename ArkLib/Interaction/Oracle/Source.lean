/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.OracleComp.OracleContext
public import PolyFun.PFunctor.Lens.Basic

/-!
# Extensional oracle sources

A `SourceCtx Query Env` is exactly a reader-valued `OracleContext`: a typed query signature and
its deterministic interpretation by backing data. It introduces no duplicate handler datatype.
The carriers are explicit parameters: query, response, and environment universes
stay independent.
The `handler` operation fixes an environment and exposes only its observable answers.

A `SourceHom S T` routes queries by an upstream polynomial lens, pulls environments back, and
proves that these two actions agree. This layer contains no identity, provenance, promise, cost,
probability, or execution history. Extensional equality is not trace equality.

`tensor` uses the common response universe required by `OracleSpec` addition. `liftResponse`
explicitly raises that universe when needed. The pure routing API has no such restriction;
only the program adapter uses `OracleComp`'s homogeneous result universe.
-/

@[expose] public section

universe u v w u' v' w' u'' v'' w'' u''' v''' w''' k k' k''

namespace Interaction.Oracle

/-- A pure source is the existing oracle-context abstraction with a reader interpretation.

The query and backing-data carriers are parameters, not a second existential package around the
signature. In particular, no phantom fields or universe equalities are needed. -/
abbrev SourceCtx (Query : Type u) (Env : Type w) :=
  OracleContext Query (fun α : Type v => Env → α)

namespace SourceCtx

variable {I : Type u} {E : Type w} {J : Type u'} {F : Type w'}

/-- Observe a reader source through one fixed environment. -/
def handler (S : SourceCtx.{u, v, w} I E) (env : E) : QueryImpl S.spec Id :=
  fun q => S.impl q env

/-- The source of arbitrary deterministic behavior for a signature. -/
def ofSpec (spec : OracleSpec.{u, v} I) : SourceCtx I (QueryImpl spec Id) where
  spec := spec
  impl := fun q env => env q

/-- A source with no queries and no backing data. -/
def empty : SourceCtx.{u, v, w} PEmpty PUnit where
  spec := fun q => PEmpty.elim q
  impl := fun q => PEmpty.elim q

/-- Restrict or rename the query interface; noninjective maps explicitly expose aliases. -/
def reindex (S : SourceCtx.{u, v, w} I E) (f : J → I) : SourceCtx J E where
  spec := fun q => S.spec (f q)
  impl := fun q => S.impl (f q)

/-- Change only the backing-data presentation. -/
def comapEnv (S : SourceCtx.{u, v, w} I E) (f : F → E) : SourceCtx I F where
  spec := S.spec
  impl := fun q env => S.impl q (f env)

/-- Disjoint query alternatives, realized by a pair of environments.

This is signature addition, not a resource-sharing operation. Resource-level disjointness is an
additional obligation of the resource-schema layer. -/
def tensor (S : SourceCtx.{u, v, w} I E) (T : SourceCtx.{u', v, w'} J F) :
    SourceCtx (I ⊕ J) (E × F) where
  spec := S.spec + T.spec
  impl := fun q env => QueryImpl.add (S.handler env.1) (T.handler env.2) q

/-- A pair of queries answered by a pair of responses, with all universes independent.

Unlike `tensor`, one primitive query observes both components. It is the polynomial tensor,
not the polynomial product (whose responses would instead form a sum). -/
def parallel (S : SourceCtx.{u, v, w} I E) (T : SourceCtx.{u', v', w'} J F) :
    SourceCtx (I × J) (E × F) where
  spec := OracleSpec.ofPFunctor (PFunctor.tensor S.spec.toPFunctor T.spec.toPFunctor)
  impl := fun q env => (S.handler env.1 q.1, T.handler env.2 q.2)

/-- An indexed family of query alternatives, with one environment per component. -/
def family {A : Type k} {Q : A → Type u} {Env : A → Type w}
    (S : (a : A) → SourceCtx.{u, v, w} (Q a) (Env a)) :
    SourceCtx (Sigma Q) ((a : A) → Env a) where
  spec := OracleSpec.sigma (fun a => (S a).spec)
  impl := fun q env => (S q.1).handler (env q.1) q.2

/-- Explicit response-universe lifting, without changing queries or backing data. -/
def liftResponse (S : SourceCtx.{u, v, w} I E) : SourceCtx.{u, max v v', w} I E where
  spec := fun q => ULift.{v'} (S.spec q)
  impl := fun q env => ⟨S.handler env q⟩

@[simp]
theorem tensor_handler_inl (S : SourceCtx.{u, v, w} I E)
    (T : SourceCtx.{u', v, w'} J F) (env : E × F) (q : I) :
    (S.tensor T).handler env (.inl q) = S.handler env.1 q := rfl

@[simp]
theorem tensor_handler_inr (S : SourceCtx.{u, v, w} I E)
    (T : SourceCtx.{u', v, w'} J F) (env : E × F) (q : J) :
    (S.tensor T).handler env (.inr q) = T.handler env.2 q := rfl

@[simp]
theorem parallel_handler (S : SourceCtx.{u, v, w} I E)
    (T : SourceCtx.{u', v', w'} J F) (env : E × F) (q : I × J) :
    (S.parallel T).handler env q = (S.handler env.1 q.1, T.handler env.2 q.2) := rfl

@[simp]
theorem family_handler {A : Type k} {Q : A → Type u} {Env : A → Type w}
    (S : (a : A) → SourceCtx.{u, v, w} (Q a) (Env a))
    (env : (a : A) → Env a) (a : A) (q : Q a) :
    (family S).handler env ⟨a, q⟩ = (S a).handler (env a) q := rfl

/-- Interpret a program using precisely the answers of the supplied environment. -/
def eval (S : SourceCtx.{u, v, w} I E) (env : E) {α : Type v}
    (program : OracleComp S.spec α) : α :=
  simulateQ (S.handler env) program

/-- Environments with equal handlers cannot be distinguished by any query program. -/
theorem eval_eq_of_handler_eq (S : SourceCtx.{u, v, w} I E) {env env' : E}
    (h : S.handler env = S.handler env') {α : Type v} (program : OracleComp S.spec α) :
    S.eval env program = S.eval env' program :=
  congrArg (fun impl => simulateQ impl program) h

/-- Primitive queries are complete tests for observational equality of environments. -/
theorem handler_eq_iff_eval_eq (S : SourceCtx.{u, v, w} I E) (env env' : E) :
    S.handler env = S.handler env' ↔
      ∀ (α : Type v) (program : OracleComp S.spec α),
        S.eval env program = S.eval env' program := by
  constructor
  · intro h α program
    exact S.eval_eq_of_handler_eq h program
  · intro h
    funext q
    simpa [eval] using h (S.spec q) (liftM (S.spec.query q))

end SourceCtx

variable {I : Type u} {E : Type w} {J : Type u'} {F : Type w'}
  {K : Type u''} {G : Type w''} {L : Type u'''} {H : Type w'''}

/-- A pure polynomial query route whose contravariant environment map realizes its answers. -/
structure SourceHom (S : SourceCtx.{u, v, w} I E) (T : SourceCtx.{u', v', w'} J F) where
  /-- Send queries forward and pull responses back. -/
  route : PFunctor.Lens S.spec.toPFunctor T.spec.toPFunctor
  /-- Realize the source backing data from target backing data. -/
  onEnv : F → E
  /-- Routing and backing-data interpretation give the same answer. -/
  commutes : ∀ (env : F) (q : I),
    S.handler (onEnv env) q = route.toFunB q (T.handler env (route.toFunA q))

namespace SourceHom

variable {S : SourceCtx.{u, v, w} I E} {T : SourceCtx.{u', v', w'} J F}
  {U : SourceCtx.{u'', v'', w''} K G} {V : SourceCtx.{u''', v''', w'''} L H}

/-- Pull back arbitrary behavior, without assuming it comes from a backing environment. -/
def pull (f : SourceHom S T) (impl : QueryImpl T.spec Id) : QueryImpl S.spec Id :=
  fun q => f.route.toFunB q (impl (f.route.toFunA q))

/-- The two data fields determine a source morphism; the coherence proof is irrelevant. -/
@[ext]
theorem ext {f g : SourceHom S T} (hroute : f.route = g.route)
    (henv : f.onEnv = g.onEnv) : f = g := by
  cases f
  cases g
  cases hroute
  cases henv
  rfl

/-- Identity routing and identity backing-data map. -/
def id (S : SourceCtx.{u, v, w} I E) : SourceHom S S where
  route := PFunctor.Lens.id S.spec.toPFunctor
  onEnv := fun env => env
  commutes := fun _ _ => rfl

/-- Compose routes in function order; environment maps compose in the reverse direction. -/
def comp (g : SourceHom T U) (f : SourceHom S T) : SourceHom S U where
  route := PFunctor.Lens.comp g.route f.route
  onEnv := f.onEnv ∘ g.onEnv
  commutes := fun env q => by
    change S.handler (f.onEnv (g.onEnv env)) q =
      f.route.toFunB q (g.route.toFunB (f.route.toFunA q)
        (U.handler env (g.route.toFunA (f.route.toFunA q))))
    rw [f.commutes, g.commutes]

@[simp]
theorem pull_id (impl : QueryImpl S.spec Id) : (id S).pull impl = impl := rfl

@[simp]
theorem pull_comp (g : SourceHom T U) (f : SourceHom S T)
    (impl : QueryImpl U.spec Id) : (g.comp f).pull impl = f.pull (g.pull impl) := rfl

/-- Naturality of source interpretation, as an equality of complete handlers. -/
@[simp]
theorem pull_handler (f : SourceHom S T) (env : F) :
    f.pull (T.handler env) = S.handler (f.onEnv env) := by
  funext q
  exact (f.commutes env q).symm

@[simp]
theorem id_comp (f : SourceHom S T) : (id T).comp f = f := by
  cases f
  rfl

@[simp]
theorem comp_id (f : SourceHom S T) : f.comp (id S) = f := by
  cases f
  rfl

theorem comp_assoc (h : SourceHom U V) (g : SourceHom T U) (f : SourceHom S T) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- Canonical routing from a reindexed signature into the original source. -/
def fromReindex (S : SourceCtx.{u, v, w} I E) (f : J → I) :
    SourceHom (S.reindex f) S where
  route := ⟨f, fun _ answer => answer⟩
  onEnv := fun env => env
  commutes := fun _ _ => rfl

/-- The unchanged signature is realized by the new backing-data presentation. -/
def toComapEnv (S : SourceCtx.{u, v, w} I E) (f : F → E) :
    SourceHom S (S.comapEnv f) where
  route := PFunctor.Lens.id S.spec.toPFunctor
  onEnv := f
  commutes := fun _ _ => rfl

/-- Left weakening ignores the additional right environment. -/
def inl (S : SourceCtx.{u, v, w} I E) (T : SourceCtx.{u', v, w'} J F) :
    SourceHom S (S.tensor T) where
  route := PFunctor.Lens.inl (P := S.spec.toPFunctor) (Q := T.spec.toPFunctor)
  onEnv := Prod.fst
  commutes := fun _ _ => rfl

/-- Right weakening ignores the additional left environment. -/
def inr (S : SourceCtx.{u, v, w} I E) (T : SourceCtx.{u', v, w'} J F) :
    SourceHom T (S.tensor T) where
  route := ⟨Sum.inr, fun _ answer => answer⟩
  onEnv := Prod.snd
  commutes := fun _ _ => rfl

/-- Combine componentwise coherent routes, allowing a noninjective index map. -/
def familyMap {A : Type k} {B : Type k'}
    {QA : A → Type u} {EA : A → Type w} {QB : B → Type u'} {EB : B → Type w'}
    (S : (a : A) → SourceCtx.{u, v, w} (QA a) (EA a))
    (T : (b : B) → SourceCtx.{u', v', w'} (QB b) (EB b))
    (index : A → B) (f : (a : A) → SourceHom (S a) (T (index a))) :
    SourceHom (SourceCtx.family S) (SourceCtx.family T) where
  route :=
    ⟨fun q => ⟨index q.1, (f q.1).route.toFunA q.2⟩,
      fun q answer => (f q.1).route.toFunB q.2 answer⟩
  onEnv := fun env a => (f a).onEnv (env (index a))
  commutes := fun env q => (f q.1).commutes (env (index q.1)) q.2

/-- Componentwise identity routing is identity routing of the complete family. -/
@[simp]
theorem familyMap_id {A : Type k} {Q : A → Type u} {Env : A → Type w}
    (S : (a : A) → SourceCtx.{u, v, w} (Q a) (Env a)) :
    familyMap S S (fun a => a) (fun a => id (S a)) = id (SourceCtx.family S) := rfl

/-- Family routing preserves composition, including contravariant backing-data maps. -/
theorem familyMap_comp {A : Type k} {B : Type k'} {C : Type k''}
    {QA : A → Type u} {EA : A → Type w} {QB : B → Type u'} {EB : B → Type w'}
    {QC : C → Type u''} {EC : C → Type w''}
    (S : (a : A) → SourceCtx.{u, v, w} (QA a) (EA a))
    (T : (b : B) → SourceCtx.{u', v', w'} (QB b) (EB b))
    (U : (c : C) → SourceCtx.{u'', v'', w''} (QC c) (EC c))
    (index : A → B) (next : B → C)
    (f : (a : A) → SourceHom (S a) (T (index a)))
    (g : (b : B) → SourceHom (T b) (U (next b))) :
    (familyMap T U next g).comp (familyMap S T index f) =
      familyMap S U (next ∘ index) (fun a => (g (index a)).comp (f a)) := rfl

/-- Select one component of an indexed source family. -/
def inFamily {A : Type k} {Q : A → Type u} {Env : A → Type w}
    (S : (a : A) → SourceCtx.{u, v, w} (Q a) (Env a)) (a : A) :
    SourceHom (S a) (SourceCtx.family S) where
  route := ⟨fun q => ⟨a, q⟩, fun _ answer => answer⟩
  onEnv := fun env => env a
  commutes := fun _ _ => rfl

/-- A family-index equality transports queries and backing data together. -/
def congrFamily {A : Type k} {Q : A → Type u} {Env : A → Type w}
    (S : (a : A) → SourceCtx.{u, v, w} (Q a) (Env a))
    {a b : A} (h : a = b) : SourceHom (S a) (S b) := by
  cases h
  exact id (S a)

@[simp]
theorem congrFamily_refl {A : Type k} {Q : A → Type u} {Env : A → Type w}
    (S : (a : A) → SourceCtx.{u, v, w} (Q a) (Env a)) (a : A) :
    congrFamily S (rfl : a = a) = id (S a) := rfl

theorem congrFamily_trans {A : Type k} {Q : A → Type u} {Env : A → Type w}
    (S : (a : A) → SourceCtx.{u, v, w} (Q a) (Env a))
    {a b c : A} (h : a = b) (h' : b = c) :
    (congrFamily S h').comp (congrFamily S h) = congrFamily S (h.trans h') := by
  cases h
  cases h'
  rfl

/-- Route into explicitly lifted responses and unwrap the answer. -/
def toLiftResponse (S : SourceCtx.{u, v, w} I E) :
    SourceHom S (S.liftResponse.{u, v, w, v'}) where
  route := ⟨fun q => q, fun _ answer => answer.down⟩
  onEnv := fun env => env
  commutes := fun _ _ => rfl

/-- Route out of explicitly lifted responses and rewrap the answer. -/
def fromLiftResponse (S : SourceCtx.{u, v, w} I E) :
    SourceHom (S.liftResponse.{u, v, w, v'}) S where
  route := ⟨fun q => q, fun _ answer => ⟨answer⟩⟩
  onEnv := fun env => env
  commutes := fun _ _ => rfl

section Programs

variable {A : SourceCtx.{u, v, w} I E} {B : SourceCtx.{u', v, w'} J F}

/-- The homogeneous-response program adapter for a pure route. -/
def toQueryImpl (f : SourceHom A B) : QueryImpl A.spec (OracleComp B.spec) :=
  fun q => f.route.toFunB q <$>
    (liftM (B.spec.query (f.route.toFunA q)) : OracleComp B.spec _)

/-- Interpreting a routed primitive query agrees with pure handler pullback. -/
@[simp]
theorem simulateQ_toQueryImpl (f : SourceHom A B) (impl : QueryImpl B.spec Id) (q : I) :
    simulateQ impl (f.toQueryImpl q) = f.pull impl q := by
  calc
    _ = f.route.toFunB q <$> impl (f.route.toFunA q) := by
      simp only [toQueryImpl, simulateQ_map, simulateQ_spec_query]
    _ = _ := rfl

/-- Route a program with the existing interpreter; no new virtual-oracle package is introduced. -/
def mapProgram (f : SourceHom A B) {α : Type v} (program : OracleComp A.spec α) :
    OracleComp B.spec α :=
  simulateQ f.toQueryImpl program

/-- Program routing commutes with interpretation by the matching backing environment. -/
theorem eval_mapProgram (f : SourceHom A B) (env : F) {α : Type v}
    (program : OracleComp A.spec α) :
    B.eval env (f.mapProgram program) = A.eval (f.onEnv env) program := by
  have h : QueryImpl.compose (B.handler env) f.toQueryImpl = A.handler (f.onEnv env) := by
    funext q
    exact (simulateQ_toQueryImpl f (B.handler env) q).trans (f.commutes env q).symm
  change simulateQ (B.handler env) (simulateQ f.toQueryImpl program) = _
  rw [← QueryImpl.simulateQ_compose, h]
  rfl

end Programs

end SourceHom

/-- An invertible coherent source route, on both queries and backing data. -/
structure SourceEquiv (S : SourceCtx.{u, v, w} I E) (T : SourceCtx.{u', v', w'} J F) where
  /-- Forward query routing. -/
  toHom : SourceHom S T
  /-- Inverse query routing. -/
  invHom : SourceHom T S
  /-- The source round trip preserves both data fields. -/
  left_inv : invHom.comp toHom = SourceHom.id S
  /-- The target round trip preserves both data fields. -/
  right_inv : toHom.comp invHom = SourceHom.id T

namespace SourceEquiv

variable {S : SourceCtx.{u, v, w} I E} {T : SourceCtx.{u', v', w'} J F}

/-- Identity equivalence. -/
def refl (S : SourceCtx.{u, v, w} I E) : SourceEquiv S S :=
  ⟨SourceHom.id S, SourceHom.id S, rfl, rfl⟩

/-- Reverse an equivalence. -/
def symm {S : SourceCtx.{u, v, w} I E} {T : SourceCtx.{u', v', w'} J F}
    (e : SourceEquiv S T) : SourceEquiv T S :=
  ⟨e.invHom, e.toHom, e.right_inv, e.left_inv⟩

/-- Compose equivalences without identifying their carrier universes. -/
def trans {S : SourceCtx.{u, v, w} I E} {T : SourceCtx.{u', v', w'} J F}
    {U : SourceCtx.{u'', v'', w''} K G} (e : SourceEquiv S T) (f : SourceEquiv T U) :
    SourceEquiv S U where
  toHom := f.toHom.comp e.toHom
  invHom := e.invHom.comp f.invHom
  left_inv := by
    rw [SourceHom.comp_assoc, ← SourceHom.comp_assoc f.invHom,
      f.left_inv, SourceHom.id_comp, e.left_inv]
  right_inv := by
    rw [SourceHom.comp_assoc, ← SourceHom.comp_assoc e.toHom,
      e.right_inv, SourceHom.id_comp, f.right_inv]

/-- Pulling arbitrary source behavior through both directions recovers that behavior. -/
@[simp]
theorem pull_inv (e : SourceEquiv S T) (impl : QueryImpl S.spec Id) :
    e.toHom.pull (e.invHom.pull impl) = impl := by
  rw [← SourceHom.pull_comp, e.left_inv, SourceHom.pull_id]

/-- Pulling arbitrary target behavior through both directions recovers that behavior. -/
@[simp]
theorem inv_pull (e : SourceEquiv S T) (impl : QueryImpl T.spec Id) :
    e.invHom.pull (e.toHom.pull impl) = impl := by
  rw [← SourceHom.pull_comp, e.right_inv, SourceHom.pull_id]

/-- Explicit universe lifting loses neither query behavior nor backing data. -/
def liftResponse (S : SourceCtx.{u, v, w} I E) :
    SourceEquiv S (S.liftResponse.{u, v, w, v'}) where
  toHom := SourceHom.toLiftResponse S
  invHom := SourceHom.fromLiftResponse S
  left_inv := rfl
  right_inv := rfl

end SourceEquiv

end Interaction.Oracle
