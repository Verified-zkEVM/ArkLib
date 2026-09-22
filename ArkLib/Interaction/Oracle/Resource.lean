/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Source

/-!
# Interpreted oracle models and named contexts

`OracleModel` interprets a named family of oracle interfaces and admissible realizations. It also
assigns protocol metadata and reified property symbols to each name. Every promised property comes
with evidence that all admissible realizations satisfy its interpretation.

`NamedContext` represents a subcontext by an injective family of names. A
`NamedContext.Inclusion` preserves those names exactly. A `NamedContext.View` is an indexed family
of references into one named context; several view indices may refer to the same context index.
Combining contexts with `disjointUnion` requires their names to be disjoint, whereas `View.share`
combines indexed views of the same context and permits aliases.

Forgetting names and metadata yields coherent `SourceCtx` and `SourceHom` values, including the
dependent transport of query and realization types. Property symbols are reified syntax with no
assumed decidable equality; their semantics comes only from `OracleModel.satisfies`.
-/

@[expose] public section

universe i q a e o p d s h t j k

namespace Interaction.Oracle

/-- An interpretation of named oracle interfaces, realizations, metadata, and reified properties.

A refined realization type can express a guarantee such as a degree bound without placing the
polynomial in the query interface. The promised-property predicate may be empty, so a property
language need not be inhabited when no property is promised. -/
structure OracleModel (Id : Type i) (Query : Id → Type q) (Realization : Id → Type a)
    (Owner : Type o) (Origin : Type p) (PropertySymbol : Id → Type d) where
  /-- The interpreted source for one oracle name. -/
  source : (r : Id) → SourceCtx.{q, e, a} (Query r) (Realization r)
  /-- Who is responsible for this oracle; not inferred from its query signature. -/
  owner : Id → Owner
  /-- The oracle's origin, in a client-supplied provenance language. -/
  origin : Id → Origin
  /-- The semantic interpretation of a property symbol on an admissible realization. -/
  satisfies : (r : Id) → PropertySymbol r → Realization r → Prop
  /-- The reified properties promised for each oracle name. -/
  promised : (r : Id) → PropertySymbol r → Prop
  /-- Every admissible realization satisfies every promised property. -/
  satisfies_promises : ∀ (r : Id) (d : PropertySymbol r), promised r d → ∀ obj, satisfies r d obj

namespace OracleModel

variable {Id : Type i} {Query : Id → Type q} {Realization : Id → Type a}
  {Owner : Type o} {Origin : Type p} {PropertySymbol : Id → Type d}

/-- A selected guarantee carries its property symbol and evidence that it is promised. -/
abbrev Guarantee
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (r : Id) := {d : PropertySymbol r // C.promised r d}

/-- A promised property holds of every admissible realization for its oracle name. -/
theorem satisfies_guarantee
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (r : Id) (guarantee : C.Guarantee r) (obj : Realization r) :
    C.satisfies r guarantee.val obj :=
  C.satisfies_promises r guarantee.val guarantee.property obj

end OracleModel

/-- A represented subcontext whose indices have distinct names. -/
structure NamedContext (Id : Type i) where
  /-- Indices for the represented names; these need not cover the entire model. -/
  Index : Type s
  /-- The injective assignment of a name to each context index. -/
  name : Index ↪ Id

namespace NamedContext

variable {Id : Type i}

/-- The empty named context. -/
def empty : NamedContext.{i, s} Id where
  Index := PEmpty
  name := ⟨PEmpty.elim, fun x => PEmpty.elim x⟩

/-- The context containing exactly one name. Repeated references belong in a `NamedContext.View`. -/
def single (r : Id) : NamedContext.{i, 0} Id where
  Index := PUnit
  name := ⟨fun _ => r, fun _ _ _ => Subsingleton.elim _ _⟩

/-- Reindex a named context along an injection. -/
def reindex (S : NamedContext.{i, s} Id) {A : Type t} (f : A ↪ S.Index) :
    NamedContext.{i, t} Id where
  Index := A
  name := ⟨fun a => S.name (f a), fun _ _ h => f.injective (S.name.injective h)⟩

/-- Two named contexts have no name in common. -/
def Disjoint (S : NamedContext.{i, s} Id) (T : NamedContext.{i, t} Id) : Prop :=
  ∀ (x : S.Index) (y : T.Index), S.name x ≠ T.name y

theorem Disjoint.symm {S : NamedContext.{i, s} Id} {T : NamedContext.{i, t} Id}
    (h : S.Disjoint T) : T.Disjoint S :=
  fun y x eq => h x y eq.symm

/-- A nonempty named context is not disjoint from itself. -/
theorem not_disjoint_self (S : NamedContext.{i, s} Id) (x : S.Index) :
    ¬ S.Disjoint S :=
  fun h => h x x rfl

/-- Combine two name-disjoint contexts. -/
def disjointUnion (S : NamedContext.{i, s} Id) (T : NamedContext.{i, t} Id)
    (h : S.Disjoint T) : NamedContext.{i, max s t} Id where
  Index := S.Index ⊕ T.Index
  name :=
    ⟨Sum.elim S.name T.name, by
      intro x y eq
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (S.name.injective eq)
        | inr y => exact (h x y eq).elim
      | inr x =>
        cases y with
        | inl y => exact (h y x eq.symm).elim
        | inr y => exact congrArg Sum.inr (T.name.injective eq)⟩

@[simp]
theorem disjointUnion_name_inl (S : NamedContext.{i, s} Id) (T : NamedContext.{i, t} Id)
    (h : S.Disjoint T) (x : S.Index) : (S.disjointUnion T h).name (.inl x) = S.name x := rfl

@[simp]
theorem disjointUnion_name_inr (S : NamedContext.{i, s} Id) (T : NamedContext.{i, t} Id)
    (h : S.Disjoint T) (y : T.Index) : (S.disjointUnion T h).name (.inr y) = T.name y := rfl

variable {Query : Id → Type q} {Realization : Id → Type a}
  {Owner : Type o} {Origin : Type p} {PropertySymbol : Id → Type d}

/-- Interpret the indexed oracle family named by this context. -/
def asSource (S : NamedContext.{i, s} Id)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol) :
    SourceCtx.{max s q, e, max s a}
      ((x : S.Index) × Query (S.name x)) ((x : S.Index) → Realization (S.name x)) :=
  SourceCtx.sigma (fun x => C.source (S.name x))

/-- A promised guarantee holds for the realization interpreting this context index. -/
theorem asSource_guarantee (S : NamedContext.{i, s} Id)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (env : (x : S.Index) → Realization (S.name x)) (x : S.Index)
    (guarantee : C.Guarantee (S.name x)) :
    C.satisfies (S.name x) guarantee.val (env x) :=
  C.satisfies_guarantee (S.name x) guarantee (env x)

@[simp]
theorem asSource_handler (S : NamedContext.{i, s} Id)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (env : (x : S.Index) → Realization (S.name x)) (x : S.Index) (q : Query (S.name x)) :
    (S.asSource C).handler env ⟨x, q⟩ = (C.source (S.name x)).handler (env x) q := rfl


/-- Interpreting a disjoint union agrees with summing the interpreted sources.

The query maps distribute dependent query families over the sum of context indices; the
environment maps split and combine their realization families. Both round trips preserve query
routing and every realization. -/
def disjointUnionSourceEquiv (S : NamedContext.{i, s} Id) (T : NamedContext.{i, t} Id)
    (h : S.Disjoint T)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol) :
    SourceEquiv ((S.disjointUnion T h).asSource C) ((S.asSource C).sum (T.asSource C)) where
  toHom :=
    { route :=
        { toFunA := fun
            | ⟨.inl x, query⟩ => .inl ⟨x, query⟩
            | ⟨.inr x, query⟩ => .inr ⟨x, query⟩
          toFunB := by
            rintro ⟨x, query⟩ answer
            cases x <;> exact answer }
      pullEnv := fun env x => match x with
        | .inl x => env.1 x
        | .inr x => env.2 x
      commutes := by
        rintro env ⟨x, query⟩
        cases x <;> rfl }
  invHom :=
    { route :=
        { toFunA := fun
            | .inl ⟨x, query⟩ => ⟨.inl x, query⟩
            | .inr ⟨x, query⟩ => ⟨.inr x, query⟩
          toFunB := by
            intro query answer
            cases query <;> exact answer }
      pullEnv := fun env => (fun x => env (.inl x), fun x => env (.inr x))
      commutes := by
        intro env query
        cases query <;> rfl }
  left_inv := by
    apply SourceHom.ext
    · apply PFunctor.Lens.ext_mapObj
      rintro ⟨x, query⟩
      cases x <;> rfl
    · funext env x
      cases x <;> rfl
  right_inv := by
    apply SourceHom.ext
    · apply PFunctor.Lens.ext_mapObj
      intro query
      cases query <;> rfl
    · rfl

end NamedContext

variable {Id : Type i}

/-- A name-preserving inclusion between represented named contexts. -/
structure NamedContext.Inclusion (S : NamedContext.{i, s} Id) (T : NamedContext.{i, t} Id) where
  /-- The target context index for each source context index. -/
  map : S.Index → T.Index
  /-- The oracle name is preserved exactly. -/
  name_eq : ∀ x, T.name (map x) = S.name x

namespace NamedContext.Inclusion

variable {S : NamedContext.{i, s} Id} {T : NamedContext.{i, t} Id}
  {U : NamedContext.{i, j} Id} {V : NamedContext.{i, k} Id}

/-- A name-preserving inclusion is injective. -/
theorem injective (f : NamedContext.Inclusion S T) : Function.Injective f.map := by
  intro x y h
  apply S.name.injective
  exact (f.name_eq x).symm.trans ((congrArg T.name h).trans (f.name_eq y))

/-- Extensionality of context inclusions. -/
@[ext]
theorem ext {f g : NamedContext.Inclusion S T} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity context inclusion. -/
def id (S : NamedContext.{i, s} Id) : NamedContext.Inclusion S S :=
  ⟨fun x => x, fun _ => rfl⟩

/-- Compose context inclusions in function order. -/
def comp (g : NamedContext.Inclusion T U) (f : NamedContext.Inclusion S T) :
    NamedContext.Inclusion S U :=
  ⟨g.map ∘ f.map, fun x => (g.name_eq (f.map x)).trans (f.name_eq x)⟩

@[simp]
theorem id_comp (f : NamedContext.Inclusion S T) : (id T).comp f = f := by cases f; rfl

@[simp]
theorem comp_id (f : NamedContext.Inclusion S T) : f.comp (id S) = f := by cases f; rfl

theorem comp_assoc (h : NamedContext.Inclusion U V) (g : NamedContext.Inclusion T U)
    (f : NamedContext.Inclusion S T) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- Include an injectively reindexed context in its original context. -/
def fromReindex (S : NamedContext.{i, s} Id) {A : Type t} (f : A ↪ S.Index) :
    NamedContext.Inclusion (S.reindex f) S :=
  ⟨f, fun _ => rfl⟩

/-- Include the left context in a disjoint union. -/
def inl (S : NamedContext.{i, s} Id) (T : NamedContext.{i, t} Id)
    (h : S.Disjoint T) : NamedContext.Inclusion S (S.disjointUnion T h) :=
  ⟨Sum.inl, fun _ => rfl⟩

/-- Include the right context in a disjoint union. -/
def inr (S : NamedContext.{i, s} Id) (T : NamedContext.{i, t} Id)
    (h : S.Disjoint T) : NamedContext.Inclusion T (S.disjointUnion T h) :=
  ⟨Sum.inr, fun _ => rfl⟩

variable {Query : Id → Type q} {Realization : Id → Type a}
  {Owner : Type o} {Origin : Type p} {PropertySymbol : Id → Type d}

/-- Interpret a context inclusion as a source morphism. -/
def toSourceHom (f : NamedContext.Inclusion S T)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol) :
    SourceHom (S.asSource C) (T.asSource C) :=
  SourceHom.sigmaMap (fun x => C.source (S.name x)) (fun y => C.source (T.name y))
    f.map (fun x => SourceHom.congrFamily C.source (f.name_eq x).symm)

/-- Interpreting the identity inclusion yields the identity source morphism. -/
@[simp]
theorem toSourceHom_id (S : NamedContext.{i, s} Id)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol) :
    (id S).toSourceHom C = SourceHom.id (S.asSource C) := rfl

/-- Interpreting context inclusions preserves composition. -/
theorem toSourceHom_comp (g : NamedContext.Inclusion T U) (f : NamedContext.Inclusion S T)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol) :
    (g.comp f).toSourceHom C = (g.toSourceHom C).comp (f.toSourceHom C) := by
  dsimp only [toSourceHom, NamedContext.asSource, comp]
  rw [SourceHom.sigmaMap_comp]
  congr 1
  funext x
  exact (SourceHom.congrFamily_trans C.source (f.name_eq x).symm
    (g.name_eq (f.map x)).symm).symm

/-- Owner metadata agrees along a context inclusion. -/
theorem owner_eq (f : NamedContext.Inclusion S T)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (x : S.Index) : C.owner (T.name (f.map x)) = C.owner (S.name x) :=
  congrArg C.owner (f.name_eq x)

/-- Origin metadata agrees along a context inclusion. -/
theorem origin_eq (f : NamedContext.Inclusion S T)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (x : S.Index) : C.origin (T.name (f.map x)) = C.origin (S.name x) :=
  congrArg C.origin (f.name_eq x)

/-- A pulled realization satisfies every guarantee promised at its preserved name. -/
theorem pulled_guarantee (f : NamedContext.Inclusion S T)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (env : (y : T.Index) → Realization (T.name y)) (x : S.Index)
    (guarantee : C.Guarantee (S.name x)) :
    C.satisfies (S.name x) guarantee.val ((f.toSourceHom C).pullEnv env x) :=
  C.satisfies_guarantee (S.name x) guarantee ((f.toSourceHom C).pullEnv env x)

end NamedContext.Inclusion

/-- An indexed family of references into a named context. -/
structure NamedContext.View (S : NamedContext.{i, s} Id) where
  /-- Indices of the view, possibly containing aliases. -/
  Index : Type h
  /-- The referenced context index; this map may be many-to-one. -/
  toIndex : Index → S.Index

namespace NamedContext.View

variable {S : NamedContext.{i, s} Id} {T : NamedContext.{i, t} Id}

/-- The full view containing one view index for each context index. -/
def full (S : NamedContext.{i, s} Id) : NamedContext.View.{i, s, s} S :=
  ⟨S.Index, fun x => x⟩

/-- Reindex a view; a noninjective map introduces aliases. -/
def reindex (view : NamedContext.View.{i, s, h} S) {A : Type j} (f : A → view.Index) :
    NamedContext.View.{i, s, j} S :=
  ⟨A, view.toIndex ∘ f⟩

/-- Reindexing by the identity function preserves the view. -/
@[simp]
theorem reindex_id (view : NamedContext.View.{i, s, h} S) :
    view.reindex (fun x => x) = view := by cases view; rfl

/-- Successive view reindexings compose. -/
theorem reindex_comp (view : NamedContext.View.{i, s, h} S) {A : Type j} {B : Type k}
    (f : A → view.Index) (g : B → A) :
    (view.reindex f).reindex g = view.reindex (f ∘ g) := rfl

/-- Combine two indexed views of the same named context. -/
def share (left : NamedContext.View.{i, s, h} S) (right : NamedContext.View.{i, s, j} S) :
    NamedContext.View S :=
  ⟨left.Index ⊕ right.Index, Sum.elim left.toIndex right.toIndex⟩

@[simp]
theorem share_toIndex_inl (left : NamedContext.View.{i, s, h} S)
    (right : NamedContext.View.{i, s, j} S) (x : left.Index) :
    (left.share right).toIndex (.inl x) = left.toIndex x := rfl

@[simp]
theorem share_toIndex_inr (left : NamedContext.View.{i, s, h} S)
    (right : NamedContext.View.{i, s, j} S) (x : right.Index) :
    (left.share right).toIndex (.inr x) = right.toIndex x := rfl

/-- The oracle name referenced by a view index. -/
def name (view : NamedContext.View.{i, s, h} S) (x : view.Index) : Id :=
  S.name (view.toIndex x)

/-- Two view indices alias exactly when they reference the same named-context index. -/
theorem name_eq_iff (view : NamedContext.View.{i, s, h} S) (x y : view.Index) :
    view.name x = view.name y ↔ view.toIndex x = view.toIndex y :=
  S.name.injective.eq_iff

/-- Combine views whose underlying named contexts are disjoint. -/
def disjointUnion (left : NamedContext.View.{i, s, h} S)
    (right : NamedContext.View.{i, t, j} T) (h : S.Disjoint T) :
    NamedContext.View (S.disjointUnion T h) :=
  ⟨left.Index ⊕ right.Index, Sum.map left.toIndex right.toIndex⟩

variable {Query : Id → Type q} {Realization : Id → Type a}
  {Owner : Type o} {Origin : Type p} {PropertySymbol : Id → Type d}

/-- Interpret a view using the realization family indexed by its named context. -/
def asSource (view : NamedContext.View.{i, s, h} S)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol) :
    SourceCtx.{max h q, e, max s a}
      ((x : view.Index) × Query (view.name x)) ((x : S.Index) → Realization (S.name x)) :=
  (S.asSource C).reindex (fun query => ⟨view.toIndex query.1, query.2⟩)

/-- Interpret a view as reindexing over the same realization family. -/
def toSourceHom (view : NamedContext.View.{i, s, h} S)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol) :
    SourceHom (view.asSource C) (S.asSource C) :=
  SourceHom.fromReindex (S.asSource C)
    (fun query : (x : view.Index) × Query (view.name x) => ⟨view.toIndex query.1, query.2⟩)

@[simp]
theorem asSource_handler (view : NamedContext.View.{i, s, h} S)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (env : (x : S.Index) → Realization (S.name x)) (x : view.Index) (q : Query (view.name x)) :
    (view.asSource C).handler env ⟨x, q⟩ =
      (C.source (view.name x)).handler (env (view.toIndex x)) q := rfl

/-- Every alias inherits each guarantee promised for the realization it references. -/
theorem asSource_guarantee (view : NamedContext.View.{i, s, h} S)
    (C : OracleModel.{i, q, a, e, o, p, d} Id Query Realization Owner Origin PropertySymbol)
    (env : (x : S.Index) → Realization (S.name x)) (x : view.Index)
    (guarantee : C.Guarantee (view.name x)) :
    C.satisfies (view.name x) guarantee.val (env (view.toIndex x)) :=
  C.satisfies_guarantee (view.name x) guarantee (env (view.toIndex x))

end NamedContext.View

end Interaction.Oracle
