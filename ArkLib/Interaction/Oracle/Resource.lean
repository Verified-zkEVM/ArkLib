/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Source

/-!
# Resource identity and ideal guarantees

`ResourceCatalog` assigns typed oracle objects and metadata to stable resource identities. Its
selected reified guarantees come with an interpretation on actual backing objects and a proof that
those objects satisfy the interpretation. An unselected descriptor grants no guarantee.

`ResourceSchema` allocates distinct identities: its slot-to-identity map is injective. By contrast,
a `ResourceView` exposes handles that may alias the same allocated slot. Its environment still has
one object per allocation, never one independent object per handle. Tensor requires disjoint
identities; it neither manufactures fresh identities nor silently treats overlap as sharing.

`SchemaHom` preserves stable identities. Forgetting its metadata yields a coherent `SourceHom`,
including transport of dependent query and object types. The catalog is fixed along this map, so
owner, origin, and the meaning of a selected guarantee cannot be changed by renaming a handle.

This is an ideal resource boundary, not a memory allocator, a cryptographic commitment, a cost
model, or a proof of knowledge. Descriptors have no assumed decidable equality. A later compiler
must use their specified meaning rather than compare uninterpreted labels.
-/

universe i q a e o p d s h t j k

namespace Interaction.Oracle

/-- A fixed interpretation of stable resource identities, interfaces, and reified guarantees.

A refined backing type can express a guarantee such as a degree bound without storing a polynomial
in the query interface. The selected-descriptor predicate may be empty, so unused descriptor
languages need not be inhabited. -/
structure ResourceCatalog (Id : Type i) (Query : Id → Type q) (Object : Id → Type a)
    (Owner : Type o) (Origin : Type p) (Descriptor : Id → Type d) where
  /-- Extensional access to one resource's backing object. -/
  source : (r : Id) → SourceCtx.{q, e, a} (Query r) (Object r)
  /-- Who is responsible for this resource; not inferred from its query signature. -/
  owner : Id → Owner
  /-- The resource's origin, in a client-supplied provenance language. -/
  origin : Id → Origin
  /-- The semantic interpretation of a descriptor on the actual backing object. -/
  meaning : (r : Id) → Descriptor r → Object r → Prop
  /-- The reified ideal guarantees selected for each identity. -/
  required : (r : Id) → Descriptor r → Prop
  /-- Every admissible object realizes every selected ideal guarantee. -/
  valid : ∀ (r : Id) (d : Descriptor r), required r d → ∀ obj, meaning r d obj

namespace ResourceCatalog

variable {Id : Type i} {Query : Id → Type q} {Object : Id → Type a}
  {Owner : Type o} {Origin : Type p} {Descriptor : Id → Type d}

/-- A selected guarantee carries its descriptor and the evidence that it is required. -/
abbrev Guarantee
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (r : Id) := {d : Descriptor r // C.required r d}

/-- A selected descriptor holds of every admissible object for its resource identity. -/
theorem realizes
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (r : Id) (guarantee : C.Guarantee r) (obj : Object r) :
    C.meaning r guarantee.val obj :=
  C.valid r guarantee.val guarantee.property obj

end ResourceCatalog

/-- A set of allocated resource slots with distinct stable identities. -/
structure ResourceSchema (Id : Type i) where
  /-- Allocated slots; this need not include every identity in the catalog. -/
  Slot : Type s
  /-- Allocation never gives two independently realized slots the same identity. -/
  key : Slot ↪ Id

namespace ResourceSchema

variable {Id : Type i}

/-- No resources are allocated. -/
def empty : ResourceSchema.{i, s} Id where
  Slot := PEmpty
  key := ⟨PEmpty.elim, fun x => PEmpty.elim x⟩

/-- Allocate exactly one resource. Multiple handles to it belong in a `ResourceView`. -/
def single (r : Id) : ResourceSchema.{i, 0} Id where
  Slot := PUnit
  key := ⟨fun _ => r, fun _ _ _ => Subsingleton.elim _ _⟩

/-- Restrict or rename allocated slots without duplicating them. -/
def reindex (S : ResourceSchema.{i, s} Id) {A : Type t} (f : A ↪ S.Slot) :
    ResourceSchema.{i, t} Id where
  Slot := A
  key := ⟨fun a => S.key (f a), fun _ _ h => f.injective (S.key.injective h)⟩

/-- Two allocations have no stable identity in common. -/
def Disjoint (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id) : Prop :=
  ∀ (x : S.Slot) (y : T.Slot), S.key x ≠ T.key y

theorem Disjoint.symm {S : ResourceSchema.{i, s} Id} {T : ResourceSchema.{i, t} Id}
    (h : S.Disjoint T) : T.Disjoint S :=
  fun y x eq => h x y eq.symm

/-- A nonempty allocation cannot be tensored with itself as a disjoint allocation. -/
theorem not_disjoint_self (S : ResourceSchema.{i, s} Id) (x : S.Slot) :
    ¬ S.Disjoint S :=
  fun h => h x x rfl

/-- Combine disjoint allocations without changing either side's stable identities. -/
def tensor (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id)
    (h : S.Disjoint T) : ResourceSchema.{i, max s t} Id where
  Slot := S.Slot ⊕ T.Slot
  key :=
    ⟨Sum.elim S.key T.key, by
      intro x y eq
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (S.key.injective eq)
        | inr y => exact (h x y eq).elim
      | inr x =>
        cases y with
        | inl y => exact (h y x eq.symm).elim
        | inr y => exact congrArg Sum.inr (T.key.injective eq)⟩

@[simp]
theorem tensor_key_inl (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id)
    (h : S.Disjoint T) (x : S.Slot) : (S.tensor T h).key (.inl x) = S.key x := rfl

@[simp]
theorem tensor_key_inr (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id)
    (h : S.Disjoint T) (y : T.Slot) : (S.tensor T h).key (.inr y) = T.key y := rfl

variable {Query : Id → Type q} {Object : Id → Type a}
  {Owner : Type o} {Origin : Type p} {Descriptor : Id → Type d}

/-- Forget metadata, interpreting exactly the allocated objects and no unused catalog entries. -/
def asSource (S : ResourceSchema.{i, s} Id)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    SourceCtx.{max s q, e, max s a}
      ((x : S.Slot) × Query (S.key x)) ((x : S.Slot) → Object (S.key x)) :=
  SourceCtx.family (fun x => C.source (S.key x))

/-- A selected guarantee holds for the object answering this allocated resource's queries. -/
theorem asSource_guarantee (S : ResourceSchema.{i, s} Id)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (env : (x : S.Slot) → Object (S.key x)) (x : S.Slot)
    (guarantee : C.Guarantee (S.key x)) :
    C.meaning (S.key x) guarantee.val (env x) :=
  C.realizes (S.key x) guarantee (env x)

@[simp]
theorem asSource_handler (S : ResourceSchema.{i, s} Id)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (env : (x : S.Slot) → Object (S.key x)) (x : S.Slot) (q : Query (S.key x)) :
    (S.asSource C).handler env ⟨x, q⟩ = (C.source (S.key x)).handler (env x) q := rfl


/-- Forgetting a disjoint allocation tensor agrees with tensoring its extensional sources.

The explicit equivalence accounts for the dependent sum of slots and the product presentation of
backing environments. Both round trips preserve query routing and the complete backing data. -/
def tensorSourceEquiv (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id)
    (h : S.Disjoint T)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    SourceEquiv ((S.tensor T h).asSource C) ((S.asSource C).tensor (T.asSource C)) where
  toHom :=
    { route :=
        { toFunA := fun
            | ⟨.inl x, query⟩ => .inl ⟨x, query⟩
            | ⟨.inr x, query⟩ => .inr ⟨x, query⟩
          toFunB := by
            rintro ⟨x, query⟩ answer
            cases x <;> exact answer }
      onEnv := fun env x => match x with
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
      onEnv := fun env => (fun x => env (.inl x), fun x => env (.inr x))
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

end ResourceSchema

variable {Id : Type i}

/-- An allocation map preserving stable identities, not just extensionally equal answers. -/
structure SchemaHom (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id) where
  /-- Target allocation serving each source slot. -/
  map : S.Slot → T.Slot
  /-- Stable identity is unchanged. This also fixes its catalog entry and object type. -/
  key_eq : ∀ x, T.key (map x) = S.key x

namespace SchemaHom

variable {S : ResourceSchema.{i, s} Id} {T : ResourceSchema.{i, t} Id}
  {U : ResourceSchema.{i, j} Id} {V : ResourceSchema.{i, k} Id}

/-- A coherent allocation map cannot merge distinct resources. -/
theorem injective (f : SchemaHom S T) : Function.Injective f.map := by
  intro x y h
  apply S.key.injective
  exact (f.key_eq x).symm.trans ((congrArg T.key h).trans (f.key_eq y))

/-- Extensionality of allocation maps. -/
@[ext]
theorem ext {f g : SchemaHom S T} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity allocation map. -/
def id (S : ResourceSchema.{i, s} Id) : SchemaHom S S :=
  ⟨fun x => x, fun _ => rfl⟩

/-- Compose allocation maps in function order. -/
def comp (g : SchemaHom T U) (f : SchemaHom S T) : SchemaHom S U :=
  ⟨g.map ∘ f.map, fun x => (g.key_eq (f.map x)).trans (f.key_eq x)⟩

@[simp]
theorem id_comp (f : SchemaHom S T) : (id T).comp f = f := by cases f; rfl

@[simp]
theorem comp_id (f : SchemaHom S T) : f.comp (id S) = f := by cases f; rfl

theorem comp_assoc (h : SchemaHom U V) (g : SchemaHom T U) (f : SchemaHom S T) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- Inclusion of an injectively reindexed allocation. -/
def fromReindex (S : ResourceSchema.{i, s} Id) {A : Type t} (f : A ↪ S.Slot) :
    SchemaHom (S.reindex f) S :=
  ⟨f, fun _ => rfl⟩

/-- Left allocation inclusion for a disjoint tensor. -/
def inl (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id)
    (h : S.Disjoint T) : SchemaHom S (S.tensor T h) :=
  ⟨Sum.inl, fun _ => rfl⟩

/-- Right allocation inclusion for a disjoint tensor. -/
def inr (S : ResourceSchema.{i, s} Id) (T : ResourceSchema.{i, t} Id)
    (h : S.Disjoint T) : SchemaHom T (S.tensor T h) :=
  ⟨Sum.inr, fun _ => rfl⟩

variable {Query : Id → Type q} {Object : Id → Type a}
  {Owner : Type o} {Origin : Type p} {Descriptor : Id → Type d}

/-- Forget resource metadata while retaining the matching dependent backing-data transport. -/
def toSourceHom (f : SchemaHom S T)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    SourceHom (S.asSource C) (T.asSource C) :=
  SourceHom.familyMap (fun x => C.source (S.key x)) (fun y => C.source (T.key y))
    f.map (fun x => SourceHom.congrFamily C.source (f.key_eq x).symm)

/-- Forgetting allocation identity preserves identity routing, including backing data. -/
@[simp]
theorem toSourceHom_id (S : ResourceSchema.{i, s} Id)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    (id S).toSourceHom C = SourceHom.id (S.asSource C) := rfl

/-- Forgetting allocation identity preserves composition, not merely query labels. -/
theorem toSourceHom_comp (g : SchemaHom T U) (f : SchemaHom S T)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    (g.comp f).toSourceHom C = (g.toSourceHom C).comp (f.toSourceHom C) := by
  dsimp only [toSourceHom, ResourceSchema.asSource, comp]
  rw [SourceHom.familyMap_comp]
  congr 1
  funext x
  exact (SourceHom.congrFamily_trans C.source (f.key_eq x).symm
    (g.key_eq (f.map x)).symm).symm

/-- Owner metadata is preserved independently of the extensional handler. -/
theorem owner_eq (f : SchemaHom S T)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (x : S.Slot) : C.owner (T.key (f.map x)) = C.owner (S.key x) :=
  congrArg C.owner (f.key_eq x)

/-- Origin metadata is preserved independently of the extensional handler. -/
theorem origin_eq (f : SchemaHom S T)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (x : S.Slot) : C.origin (T.key (f.map x)) = C.origin (S.key x) :=
  congrArg C.origin (f.key_eq x)

/-- The routed environment satisfies each selected guarantee about the routed object. -/
theorem pulled_guarantee (f : SchemaHom S T)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (env : (y : T.Slot) → Object (T.key y)) (x : S.Slot)
    (guarantee : C.Guarantee (S.key x)) :
    C.meaning (S.key x) guarantee.val ((f.toSourceHom C).onEnv env x) :=
  C.realizes (S.key x) guarantee ((f.toSourceHom C).onEnv env x)

end SchemaHom

/-- Handles exposing an allocation. Unlike the allocation's key, resolution may be many-to-one. -/
structure ResourceView (S : ResourceSchema.{i, s} Id) where
  /-- Public handles, possibly with aliases. -/
  Handle : Type h
  /-- Aliases resolve to one allocated object rather than two asserted-equal copies. -/
  resolve : Handle → S.Slot

namespace ResourceView

variable {S : ResourceSchema.{i, s} Id} {T : ResourceSchema.{i, t} Id}

/-- Expose each allocated slot under its own handle. -/
def full (S : ResourceSchema.{i, s} Id) : ResourceView.{i, s, s} S :=
  ⟨S.Slot, fun x => x⟩

/-- Reindex exposed handles; noninjective maps introduce sharing without allocating anything. -/
def reindex (view : ResourceView.{i, s, h} S) {A : Type j} (f : A → view.Handle) :
    ResourceView.{i, s, j} S :=
  ⟨A, view.resolve ∘ f⟩

/-- Handle reindexing preserves identity. -/
@[simp]
theorem reindex_id (view : ResourceView.{i, s, h} S) :
    view.reindex (fun x => x) = view := by cases view; rfl

/-- Handle reindexing preserves composition without changing the allocation. -/
theorem reindex_comp (view : ResourceView.{i, s, h} S) {A : Type j} {B : Type k}
    (f : A → view.Handle) (g : B → A) :
    (view.reindex f).reindex g = view.reindex (f ∘ g) := rfl

/-- Combine two views of the same allocation with explicit sharing, not a disjoint tensor. -/
def share (left : ResourceView.{i, s, h} S) (right : ResourceView.{i, s, j} S) :
    ResourceView S :=
  ⟨left.Handle ⊕ right.Handle, Sum.elim left.resolve right.resolve⟩

@[simp]
theorem share_resolve_inl (left : ResourceView.{i, s, h} S)
    (right : ResourceView.{i, s, j} S) (x : left.Handle) :
    (left.share right).resolve (.inl x) = left.resolve x := rfl

@[simp]
theorem share_resolve_inr (left : ResourceView.{i, s, h} S)
    (right : ResourceView.{i, s, j} S) (x : right.Handle) :
    (left.share right).resolve (.inr x) = right.resolve x := rfl

/-- The stable identity of the allocation serving a handle. -/
def key (view : ResourceView.{i, s, h} S) (x : view.Handle) : Id :=
  S.key (view.resolve x)

/-- Aliasing is equality of physical slots, equivalently equality of their stable identities. -/
theorem key_eq_iff (view : ResourceView.{i, s, h} S) (x y : view.Handle) :
    view.key x = view.key y ↔ view.resolve x = view.resolve y :=
  S.key.injective.eq_iff

/-- Combine exposed handles only after checking the underlying allocations are disjoint. -/
def tensor (left : ResourceView.{i, s, h} S) (right : ResourceView.{i, t, j} T)
    (h : S.Disjoint T) : ResourceView (S.tensor T h) :=
  ⟨left.Handle ⊕ right.Handle, Sum.map left.resolve right.resolve⟩

variable {Query : Id → Type q} {Object : Id → Type a}
  {Owner : Type o} {Origin : Type p} {Descriptor : Id → Type d}

/-- Forget handle metadata but retain the original, allocation-indexed backing environment. -/
def asSource (view : ResourceView.{i, s, h} S)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    SourceCtx.{max h q, e, max s a}
      ((x : view.Handle) × Query (view.key x)) ((x : S.Slot) → Object (S.key x)) :=
  (S.asSource C).reindex (fun query => ⟨view.resolve query.1, query.2⟩)

/-- Exposing handles is pure reindexing over the same backing objects. -/
def toSourceHom (view : ResourceView.{i, s, h} S)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor) :
    SourceHom (view.asSource C) (S.asSource C) :=
  SourceHom.fromReindex (S.asSource C)
    (fun query : (x : view.Handle) × Query (view.key x) => ⟨view.resolve query.1, query.2⟩)

@[simp]
theorem asSource_handler (view : ResourceView.{i, s, h} S)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (env : (x : S.Slot) → Object (S.key x)) (x : view.Handle) (q : Query (view.key x)) :
    (view.asSource C).handler env ⟨x, q⟩ =
      (C.source (view.key x)).handler (env (view.resolve x)) q := rfl

/-- Every alias inherits each selected guarantee of the single object it observes. -/
theorem asSource_guarantee (view : ResourceView.{i, s, h} S)
    (C : ResourceCatalog.{i, q, a, e, o, p, d} Id Query Object Owner Origin Descriptor)
    (env : (x : S.Slot) → Object (S.key x)) (x : view.Handle)
    (guarantee : C.Guarantee (view.key x)) :
    C.meaning (view.key x) guarantee.val (env (view.resolve x)) :=
  C.realizes (view.key x) guarantee (env (view.resolve x))

end ResourceView

end Interaction.Oracle
