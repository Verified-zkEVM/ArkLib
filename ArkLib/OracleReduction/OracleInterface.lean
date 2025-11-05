/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ArkLib.ToVCVio.SimOracle
import ArkLib.Data.MvPolynomial.Notation
import Mathlib.Algebra.Polynomial.Roots
-- import ArkLib.Data.MlPoly.Basic

/-!
  # Definitions and Instances for `OracleInterface`

  We define `OracleInterface`, which is a type class that augments a type with an oracle interface
  for that type. The interface specifies the type of queries, the type of responses, and the
  oracle's behavior for a given underlying element of the type.

  `OracleInterface` is used to restrict the verifier's access to the input oracle statements and the
  prover's messages in an interactive oracle reduction (see `Basic.lean`).

  We define `OracleInterface` instances for common types:

  - Univariate and multivariate polynomials. These instances turn polynomials into oracles for which
    one can query at a point, and the response is the evaluation of the polynomial on that point.

  - Vectors. This instance turns vectors into oracles for which one can query specific positions.
-/

universe u v w

open OracleComp OracleSpec OracleQuery

/-- `OracleInterface` is a type class that provides an oracle interface for a type `Message`.
  It consists of:
  - a query type `Query`,
  - a response type `Response`,
  - a function `answer` that given a message `m : Message` and a query `q : Query`,
  returns a response `r : Response`.

TODO: turn `(Query, Response)` into a general `PFunctor` (i.e. `Response : Query → Type`) This
allows for better compositionality of `OracleInterface`, including (indexed) sum, instead of
requiring indexed family of `OracleInterface`s.

However, this won't be possible until `OracleSpec` is changed to be an alias for `PFunctor` -/
@[ext]
class OracleInterface (Message : Type u) where
  Query : Type v
  Response : Type w
  answer : Message → Query → Response

namespace OracleInterface

/-- The default instance for `OracleInterface`, where the query is trivial (a `Unit`) and the
  response returns the data. We do not register this as an instance, instead explicitly calling it
  where necessary.
-/
def instDefault {Message : Type u} : OracleInterface Message where
  Query := Unit
  Response := Message
  answer := fun m _ => m

instance {Message : Type u} : Inhabited (OracleInterface Message) :=
  ⟨instDefault⟩

open SimOracle

/-- Converts an indexed type family of oracle interfaces into an oracle specification.

Notation: `[v]ₒ` for when the oracle interfaces can be inferred, and `[v]ₒ'O` for when the oracle
interfaces need to be specified. -/
def toOracleSpec {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)] :
    OracleSpec ι := fun i => ((O i).Query, (O i).Response)

@[inherit_doc] notation "[" v "]ₒ" => toOracleSpec v
@[inherit_doc] notation "[" v "]ₒ'" oI:max => toOracleSpec v (O := oI)

/-- Given an underlying data for an indexed type family of oracle interfaces `v`,
    we can give an implementation of all queries to the interface defined by `v` -/
def toOracleImpl {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)]
    (data : ∀ i, v i) : QueryImpl [v]ₒ Id where
  impl | query i t => (O i).answer (data i) t

/-- Any function type has a canonical `OracleInterface` instance, whose `answer` is the function
  itself. -/
instance (i : Fin 0) : OracleInterface i.elim0 := Fin.elim0 i

@[reducible, inline]
instance instFunction {α β : Type*} : OracleInterface (α → β) where
  Query := α
  Response := β
  answer := id

instance {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)]
    [h : ∀ i, DecidableEq (Query (v i))]
    [h' : ∀ i, DecidableEq (Response (v i))] :
    [v]ₒ.DecidableEq where
  domain_decidableEq' := h
  range_decidableEq' := h'

instance {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)]
    [h : ∀ i, Fintype (Response (v i))]
    [h' : ∀ i, Inhabited (Response (v i))] :
    [v]ₒ.FiniteRange where
  range_fintype' := h
  range_inhabited' := h'

@[reducible, inline]
instance {ι₁ : Type u} {T₁ : ι₁ → Type v} [inst₁ : ∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type u} {T₂ : ι₂ → Type v} [inst₂ : ∀ i, OracleInterface (T₂ i)] :
    ∀ i, OracleInterface (Sum.rec T₁ T₂ i) :=
  fun i => match i with
    | .inl i => inst₁ i
    | .inr i => inst₂ i

/-- The tensor product oracle interface for the product of two types `α` and `β`, each with its own
  oracle interface, is defined as:
  - The query & response types are the product of the two query & response types.
  - The oracle will run both oracles and return the pair of responses.

This is a low priority instance since we do not expect to have this behavior often. See `instProd`
for the sum behavior on the interface. -/
@[reducible, inline]
instance (priority := low) instTensorProd {α β : Type*}
    [Oα : OracleInterface α] [Oβ : OracleInterface β] : OracleInterface (α × β) where
  Query := Oα.Query × Oβ.Query
  Response := Oα.Response × Oβ.Response
  answer := fun (a, b) (q₁, q₂) => (Oα.answer a q₁, Oβ.answer b q₂)

/-- The product oracle interface for the product of two types `α` and `β`, each with its own oracle
  interface, is defined as:
  - The query & response types are the sum type of the two query & response types.
  - The oracle will answer depending on the input query.

This is the behavior more often assumed, i.e. when we send multiple oracle messages in a round.
See `instTensor` for the tensor product behavior on the interface. -/
@[reducible, inline]
instance instProd {α β : Type*} [Oα : OracleInterface α] [Oβ : OracleInterface β] :
    OracleInterface (α × β) where
  Query := Oα.Query ⊕ Oβ.Query
  Response := Oα.Response ⊕ Oβ.Response
  answer := fun (a, b) q => match q with
    | .inl q => .inl (Oα.answer a q)
    | .inr q => .inr (Oβ.answer b q)

/-- The indexed tensor product oracle interface for the dependent product of a type family `v`,
    indexed by `ι`, each having an oracle interface, is defined as:
  - The query & response types are the dependent product of the query & response types of the type
    family.
  - The oracle, on a given query specifying the index `i` of the type family, will run the oracle of
    `v i` and return the response.

This is a low priority instance since we do not expect to have this behavior often. See
`instProdForall` for the product behavior on the interface (with dependent sums for the query and
response types). -/
@[reducible, inline]
instance (priority := low) instTensorForall {ι : Type u} (v : ι → Type v)
    [O : ∀ i, OracleInterface (v i)] : OracleInterface (∀ i, v i) where
  Query := (i : ι) → (O i).Query
  Response := (i : ι) → (O i).Response
  answer := fun f q i => (O i).answer (f i) (q i)

/-- The indexed product oracle interface for the dependent product of a type family `v`, indexed by
    `ι`, each having an oracle interface, is defined as:
  - The query & response types are the dependent product of the query & response types of the type
    family.
  - The oracle, on a given query specifying the index `i` of the type family, will run the oracle
    of `v i` and return the response.

This is the behavior usually assumed, i.e. when we send multiple oracle messages in a round.
See `instTensorForall` for the tensor product behavior on the interface. -/
@[reducible, inline]
instance instProdForall {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)] :
    OracleInterface (∀ i, v i) where
  Query := (i : ι) × (O i).Query
  Response := (i : ι) × (O i).Response
  answer := fun f ⟨i, q⟩ => ⟨i, (O i).answer (f i) q⟩

def append {ι₁ : Type u} {T₁ : ι₁ → Type v} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type u} {T₂ : ι₂ → Type v} [∀ i, OracleInterface (T₂ i)] : OracleSpec (ι₁ ⊕ ι₂) :=
  [Sum.rec T₁ T₂]ₒ

/-- Combines multiple oracle specifications into a single oracle by routing queries to the
      appropriate underlying oracle. Takes:
    - A base oracle specification `oSpec`
    - An indexed type family `T` with `OracleInterface` instances
    - Values of that type family
  Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
def simOracle {ι : Type u} (oSpec : OracleSpec ι) {ι' : Type v} {T : ι' → Type w}
    [∀ i, OracleInterface (T i)] (t : (i : ι') → T i) :
    SimOracle.Stateless (oSpec ++ₒ [T]ₒ) oSpec :=
  idOracle ++ₛₒ (fnOracle [T]ₒ (fun i => answer (t i)))

/-- Combines multiple oracle specifications into a single oracle by routing queries to the
      appropriate underlying oracle. Takes:
    - A base oracle specification `oSpec`
    - Two indexed type families `T₁` and `T₂` with `OracleInterface` instances
    - Values of those type families
  Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
def simOracle2 {ι : Type u} (oSpec : OracleSpec ι)
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) : SimOracle.Stateless (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) oSpec :=
  idOracle ++ₛₒ
    fnOracle ([T₁]ₒ ++ₒ [T₂]ₒ) (fun i => match i with
      | .inl i => answer (t₁ i)
      | .inr i => answer (t₂ i))

open Finset in
/-- A message type together with a `OracleInterface` instance is said to have **oracle distance**
  (at most) `d` if for any two distinct messages, there is at most `d` queries that distinguish
  them, i.e.

  `#{q | OracleInterface.answer a q = OracleInterface.answer b q} ≤ d`.

  This property corresponds to the distance of a code, when the oracle instance is to encode the
  message and the query is a position of the codeword. In particular, it applies to
  `(Mv)Polynomial`. -/
def distanceLE (Message : Type*) [O : OracleInterface Message]
    [Fintype (O.Query)] [DecidableEq (O.Response)] (d : ℕ) : Prop :=
  ∀ a b : Message, a ≠ b → #{q | OracleInterface.answer a q = OracleInterface.answer b q} ≤ d

section Polynomial

open Polynomial MvPolynomial

variable {R : Type*} [CommSemiring R] {d : ℕ} {σ : Type*}

/-- Univariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomial : OracleInterface R[X] where
  Query := R
  Response := R
  answer := fun poly point => poly.eval point

/-- Univariate polynomials with degree at most `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomialDegreeLE : OracleInterface (R⦃≤ d⦄[X]) where
  Query := R
  Response := R
  answer := fun ⟨poly, _⟩ point => poly.eval point

/-- Univariate polynomials with degree less than `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomialDegreeLT : OracleInterface (R⦃< d⦄[X]) where
  Query := R
  Response := R
  answer := fun ⟨poly, _⟩ point => poly.eval point

/-- Multivariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instMvPolynomial : OracleInterface (R[X σ]) where
  Query := σ → R
  Response := R
  answer := fun poly point => eval point poly

/-- Multivariate polynomials with individual degree at most `d` can be accessed via evaluation
queries. -/
@[reducible, inline]
instance instMvPolynomialDegreeLE : OracleInterface (R⦃≤ d⦄[X σ]) where
  Query := σ → R
  Response := R
  answer := fun ⟨poly, _⟩ point => eval point poly

instance [Fintype σ] [DecidableEq σ] [Fintype R] : Fintype (OracleInterface.Query (R⦃≤ d⦄[X σ])) :=
  inferInstanceAs (Fintype (σ → R))

end Polynomial

section Vector

variable {n : ℕ} {α : Type*}

/- Vectors of the form `Fin n → α` can be accessed via queries on their indices. We no longer have
   this instance separately since it can be inferred from the instance for `Function`. -/
-- instance instOracleInterfaceForallFin :
--     OracleInterface (Fin n → α) := OracleInterface.instFunction

/-- Vectors of the form `List.Vector α n` can be accessed via queries on their indices. -/
instance instListVector : OracleInterface (List.Vector α n) where
  Query := Fin n
  Response := α
  answer := fun vec i => vec[i]

/-- Vectors of the form `Vector α n` can be accessed via queries on their indices. -/
instance instVector : OracleInterface (Vector α n) where
  Query := Fin n
  Response := α
  answer := fun vec i => vec[i]

end Vector

end OracleInterface

section PolynomialDistance

-- TODO: refactor these theorems and move them into the appropriate `(Mv)Polynomial` files

open Polynomial MvPolynomial OracleInterface

variable {R : Type*} [CommRing R] {d : ℕ} [Fintype R] [DecidableEq R] [IsDomain R]

-- TODO: golf this theorem
@[simp]
theorem distanceLE_polynomial_degreeLT : distanceLE (R⦃< d⦄[X]) (d - 1) := by
  simp [distanceLE, instPolynomialDegreeLT, mem_degreeLT]
  intro p hp p' hp' hNe
  have : ∀ q ∈ Finset.univ, p.eval q = p'.eval q ↔ q ∈ (p - p').roots := by
    intro q _
    simp
    constructor <;> intro h
    · constructor
      · intro h'; contrapose! hNe; exact sub_eq_zero.mp h'
      · simp [h]
    · exact sub_eq_zero.mp h.2
  conv =>
    enter [1, 1]
    apply Finset.filter_congr this
  simp [Membership.mem, Finset.filter, Finset.card]
  have : (p - p').roots.card < d := by
    have hSubNe : p - p' ≠ 0 := sub_ne_zero_of_ne hNe
    have hSubDegLt : (p - p').degree < d := lt_of_le_of_lt (degree_sub_le p p') (by simp [hp, hp'])
    have := Polynomial.card_roots hSubNe
    have : (p - p').roots.card < (d : WithBot ℕ) := lt_of_le_of_lt this hSubDegLt
    simp at this; exact this
  refine Nat.le_sub_one_of_lt (lt_of_le_of_lt ?_ this)
  apply Multiset.card_le_card
  rw [Multiset.le_iff_subset]
  · intro x hx; simp at hx; exact hx
  · simp [Multiset.nodup_iff_count_le_one]
    intro a; simp [Multiset.count_filter, Multiset.count_univ]
    aesop

theorem distanceLE_polynomial_degreeLE : distanceLE (R⦃≤ d⦄[X]) d := by
  simp [distanceLE, instPolynomialDegreeLE, mem_degreeLE]
  intro a ha b hb hNe
  simp [Finset.card_filter_le_iff]
  intro s hs
  have habNe : a - b ≠ 0 := sub_ne_zero_of_ne hNe
  have hab : (a - b).degree ≤ d := le_trans (degree_sub_le a b) (by simp [ha, hb])
  have : ¬ s.val ≤ (a - b).roots := by
    intro h
    have h1 : s.val.card ≤ (a - b).roots.card := Multiset.card_le_card h
    have h2 : (a - b).roots.card ≤ (d : WithBot ℕ) := le_trans (card_roots habNe) hab
    simp at h2
    contrapose! hs
    exact le_trans h1 h2
  rw [Multiset.le_iff_subset s.nodup] at this
  simp [Multiset.subset_iff] at this
  obtain ⟨x, hMem, hx⟩ := this
  exact ⟨x, hMem, fun h => by simp_all⟩

theorem distanceLE_mvPolynomial_degreeLE {σ : Type*} [Fintype σ] [DecidableEq σ] :
    distanceLE (R⦃≤ d⦄[X σ]) (Fintype.card σ * d) := by
  simp [distanceLE, instMvPolynomialDegreeLE,
    MvPolynomial.mem_restrictDegree]
  intro a ha b hb hNe
  sorry

end PolynomialDistance
