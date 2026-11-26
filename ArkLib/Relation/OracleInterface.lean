/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.OracleComp.SimSemantics.Append
public import CompPoly.Data.MvPolynomial.Notation
public import Mathlib.Algebra.Polynomial.Roots
public import ArkLib.Data.MvPolynomial.Degrees
public import ToMathlib.Algebra.MvPolynomial.SchwartzZippel
-- import ArkLib.Data.MlPoly.Basic

/-!
  # Definitions and Instances for `OracleInterface`

  We define `OracleInterface`, which is a type class that augments a type with an oracle interface
  for that type. The interface specifies the type of queries, the type of responses, and the
  oracle's behavior for a given underlying element of the type.

  `OracleInterface` is used to restrict the verifier's access to the input oracle statements and the
  prover's messages in an interactive oracle reduction. Both the interaction layer
  (`ArkLib.Interaction`) and the legacy layer (`ArkLib.OracleReduction`) use it.

  We define `OracleInterface` instances for common types:

  - Univariate and multivariate polynomials. These instances turn polynomials into oracles for which
    one can query at a point, and the response is the evaluation of the polynomial on that point.

  - Vectors. This instance turns vectors into oracles for which one can query specific positions.
-/

@[expose] public section

universe u v

open OracleComp OracleSpec OracleQuery

/-- VCVio's empty oracle specification `[]ₒ` at `Type`. No argument of `emptySpec` determines its
two universes, so each use of `[]ₒ` needs a universe annotation. This alias has no universe
parameters. -/
abbrev emptySpec0 : OracleSpec.{0, 0} PEmpty := emptySpec.{0, 0}

/-- `OracleInterface` is a type class that provides an oracle interface for a type `Message`.
  It consists of:
  - a query type `Query`,
  - a specification `spec`, which gives the response type `spec q` of each query `q`,
  - a function `answer` that, given a message `m : Message` and a query `q : Query`, returns a
    response in `spec q`.

The field `answer` has type `Message → (q : Query) → spec q` rather than
`Message → QueryImpl spec Id`. The two types agree by `rfl`, but the second puts `Id` in the
expected type of instance bodies, where it blocks instance search (for example the `Semiring`
instance that `Polynomial.eval` needs). -/
@[ext]
class OracleInterface (Message : Type) : Type 1 where
  /-- The type of queries. -/
  Query : Type
  /-- The response type of each query. -/
  spec : OracleSpec.{0, 0} Query
  /-- The response of a message to each query. -/
  answer : Message → (q : Query) → spec q

namespace OracleInterface

/-- The response type of a query `q`. -/
def Response {Message : Type} [O : OracleInterface Message]
    (q : O.Query) : Type :=
  O.spec q

/-- Pointwise decidable response equality induces a decidable predicate for equality of two
oracle answers. -/
instance instDecidablePredAnswerEq {Message : Type} [O : OracleInterface Message]
    [∀ q, DecidableEq (O.spec q)] (a b : Message) :
    DecidablePred (fun q => answer a q = answer b q) := fun q =>
  (inferInstance : DecidableEq (O.spec q)) (answer a q) (answer b q)

/-- The default instance for `OracleInterface`, where the query is trivial (a `Unit`) and the
  response returns the data. We do not register this as an instance, instead explicitly calling it
  where necessary.
-/
@[reducible]
def instDefault {Message : Type} : OracleInterface Message where
  Query := Unit
  spec := fun _ => Message
  answer m _ := m

instance {Message : Type} : Inhabited (OracleInterface Message) :=
  ⟨instDefault⟩

/-- Converts an indexed type family of oracle interfaces into an oracle specification.

Notation: `[v]ₒ` for when the oracle interfaces can be inferred, and `[v]ₒ'O` for when the oracle
interfaces need to be specified. -/
def toOracleSpec {ι : Type u} (v : ι → Type) [O : ∀ i, OracleInterface (v i)] :
    OracleSpec ((i : ι) × (O i).Query) := fun q => (O q.1).Response q.2

@[inherit_doc] notation "[" v "]ₒ" => toOracleSpec v
@[inherit_doc] notation "[" v "]ₒ'" oI:max => toOracleSpec v (O := oI)

/-- Any function type has a canonical `OracleInterface` instance, whose `answer` is the function
  itself. -/
instance (i : Fin 0) : OracleInterface i.elim0 := Fin.elim0 i

@[reducible, inline]
instance instFunction {α β : Type} : OracleInterface (α → β) where
  Query := α
  spec := α →ₒ β
  answer f q := f q

@[reducible, inline]
instance {ι₁ : Type u} {T₁ : ι₁ → Type} [inst₁ : ∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type u} {T₂ : ι₂ → Type} [inst₂ : ∀ i, OracleInterface (T₂ i)] :
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
instance (priority := low) instTensorProd {α β : Type}
    [Oα : OracleInterface α] [Oβ : OracleInterface β] : OracleInterface (α × β) where
  Query := Oα.Query × Oβ.Query
  spec := fun | (q₁, q₂) => Oα.Response q₁ × Oβ.Response q₂
  answer x := fun | (q₁, q₂) => (Oα.answer x.1 q₁, Oβ.answer x.2 q₂)

/-- The product oracle interface for the product of two types `α` and `β`, each with its own oracle
  interface, is defined as:
  - The query & response types are the sum type of the two query & response types.
  - The oracle will answer depending on the input query.

This is the behavior more often assumed, i.e. when we send multiple oracle messages in a round.
See `instTensorProd` for the tensor product behavior on the interface. -/
@[reducible, inline]
instance instProd {α β : Type} [Oα : OracleInterface α] [Oβ : OracleInterface β] :
    OracleInterface (α × β) where
  Query := Oα.Query ⊕ Oβ.Query
  spec := Oα.spec + Oβ.spec
  answer x := QueryImpl.add (m := Id) (Oα.answer x.1) (Oβ.answer x.2)

/-- The indexed product oracle interface for the dependent product of a type family `v`, indexed by
    `ι`, each having an oracle interface, is defined as:
  - The query & response types are the dependent product of the query & response types of the type
    family.
  - The oracle, on a given query specifying the index `i` of the type family, will run the oracle
    of `v i` and return the response.

This is the behavior usually assumed, i.e. when we send multiple oracle messages in a round. -/
@[reducible, inline]
instance instProdForall {ι : Type} (v : ι → Type) [O : ∀ i, OracleInterface (v i)] :
    OracleInterface (∀ i, v i) where
  Query := (i : ι) × (O i).Query
  spec := fun q => (O q.1).Response q.2
  answer x q := (O q.1).answer (x q.1) q.2

/-- Answer each query to an indexed family of oracle interfaces from the family's values. -/
def simOracle0 {ι : Type u} (T : ι → Type)
    [O : ∀ i, OracleInterface (T i)]
    (t : (i : ι) → T i) : QueryImpl [T]ₒ Id :=
  fun q => (O q.1).answer (t q.1) q.2

/-- Combines multiple oracle specifications into a single oracle by routing queries to the
      appropriate underlying oracle. Takes:
    - A base oracle specification `oSpec`
    - An indexed type family `T` with `OracleInterface` instances
    - Values of that type family
  Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
def simOracle {ι : Type u} (oSpec : OracleSpec ι)
    {ι' : Type v} {T : ι' → Type}
    [∀ i, OracleInterface (T i)] (t : (i : ι') → T i) :
    QueryImpl (oSpec + [T]ₒ) (OracleComp oSpec) :=
  QueryImpl.addLift (QueryImpl.id oSpec) (simOracle0 T t)

/-- Combines multiple oracle specifications into a single oracle by routing queries to the
      appropriate underlying oracle. Takes:
    - A base oracle specification `oSpec`
    - Two indexed type families `T₁` and `T₂` with `OracleInterface` instances
    - Values of those type families
  Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
def simOracle2 {ι : Type u} (oSpec : OracleSpec ι)
    {ι₁ : Type v} {T₁ : ι₁ → Type}
    [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type}
    [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) :
    QueryImpl (oSpec + ([T₁]ₒ + [T₂]ₒ)) (OracleComp oSpec) :=
  QueryImpl.addLift (QueryImpl.id oSpec)
    (QueryImpl.add (simOracle0 T₁ t₁) (simOracle0 T₂ t₂))

/-- Simulating a query to the second oracle family through `simOracle2` answers it from that
family's values. For an oracle verifier this family is the prover's messages.

The query is stated at its single-step lift into the combined specification. A verifier's
`query` elaborates through a longer `MonadLiftT` chain, so this rewrites it only up to instance
unfolding (`OracleVerifier.toVerifier_verify_of_query_guard` uses it with `erw`). -/
theorem simulateQ_simOracle2_liftM_query_snd {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) (j : ι₂) (q : Query (T₂ j)) :
    simulateQ (simOracle2 oSpec t₁ t₂)
      (liftM (OracleSpec.query (spec := [T₂]ₒ) ⟨j, q⟩) :
        OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) = pure (answer (t₂ j) q) :=
  rfl

/-- The queries on which two messages give the same oracle answer. -/
def agreementQueries {Message : Type} (O : OracleInterface Message)
    [Fintype O.Query] [∀ q, DecidableEq (O.spec q)] (a b : Message) : Finset O.Query :=
  Finset.univ.filter fun q => answer a q = answer b q

@[simp]
lemma mem_agreementQueries {Message : Type} {O : OracleInterface Message}
    [Fintype O.Query] [∀ q, DecidableEq (O.spec q)] {a b : Message} {q : O.Query} :
    q ∈ O.agreementQueries a b ↔ answer a q = answer b q := by
  simp [agreementQueries]

/-- A message type together with a `OracleInterface` instance is said to have **oracle distance**
  (at most) `d` if for any two distinct messages, there is at most `d` queries that distinguish
  them, i.e.

  `#{q | OracleInterface.answer a q = OracleInterface.answer b q} ≤ d`.

  This property corresponds to the distance of a code, when the oracle instance is to encode the
  message and the query is a position of the codeword. In particular, it applies to
  `(Mv)Polynomial`. -/
def distanceLE {Message : Type} (O : OracleInterface Message)
    [Fintype O.Query] [∀ q, DecidableEq (O.spec q)] (d : ℕ) : Prop :=
  ∀ a b : Message, a ≠ b → (O.agreementQueries a b).card ≤ d

section Polynomial

open Polynomial MvPolynomial

variable (R : Type) [CommSemiring R] (d : ℕ) (σ : Type)

/-- Univariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomial : OracleInterface (Polynomial R) where
  Query := R
  spec := R →ₒ R
  answer p point := p.eval point

/-- Univariate polynomials with degree at most `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomialDegreeLE : OracleInterface (R⦃≤ d⦄[X]) where
  Query := R
  spec := R →ₒ R
  answer p point := p.1.eval point

/-- Univariate polynomials with degree less than `d` can be accessed via evaluation queries. -/
@[reducible, inline]
instance instPolynomialDegreeLT : OracleInterface (R⦃< d⦄[X]) where
  Query := R
  spec := R →ₒ R
  answer p point := p.1.eval point

/-- Multivariate polynomials can be accessed via evaluation queries. -/
noncomputable instance instMvPolynomial : OracleInterface (R[X σ]) where
  Query := (σ → R)
  spec := (σ → R) →ₒ R
  answer p points := p.eval points

/-- Multivariate polynomials with individual degree at most `d` can be accessed via evaluation
queries. -/
noncomputable instance instMvPolynomialDegreeLE : OracleInterface (R⦃≤ d⦄[X σ]) where
  Query := (σ → R)
  spec := (σ → R) →ₒ R
  answer p points := p.1.eval points

instance [Fintype σ] [DecidableEq σ] [Fintype R] :
    Fintype (OracleInterface.Query (R⦃≤ d⦄[X σ])) :=
  inferInstanceAs (Fintype (σ → R))

end Polynomial

section Vector

variable {n : ℕ} {α : Type}

/-- Vectors of the form `List.Vector α n` can be accessed via queries on their indices. -/
instance instListVector : OracleInterface (List.Vector α n) where
  Query := (Fin n)
  spec := Fin n →ₒ α
  answer v i := v[i]

/-- Vectors of the form `Vector α n` can be accessed via queries on their indices. -/
instance instVector : OracleInterface (Vector α n) where
  Query := (Fin n)
  spec := Fin n →ₒ α
  answer v i := v[i]

end Vector

end OracleInterface

section PolynomialDistance

-- TODO: refactor these theorems and move them into the appropriate `(Mv)Polynomial` files

open Polynomial MvPolynomial OracleInterface

variable {R : Type} [CommRing R] {d : ℕ} [Fintype R] [DecidableEq R] [IsDomain R]

-- TODO: golf this theorem
@[simp]
theorem distanceLE_polynomial_degreeLT :
    distanceLE (instPolynomialDegreeLT R d) (d - 1) := by
  simp only [distanceLE, ne_eq, instPolynomialDegreeLT, Subtype.forall,
    mem_degreeLT, Subtype.mk.injEq]
  intro p hp p' hp' hNe
  have hEvalRoot : ∀ q ∈ Finset.univ, p.eval q = p'.eval q ↔ q ∈ (p - p').roots := by
    intro q _
    simp only [mem_roots', ne_eq, IsRoot.def, Polynomial.eval_sub]
    constructor <;> intro h
    · constructor
      · intro h'; contrapose! hNe; exact sub_eq_zero.mp h'
      · simp [h]
    · exact sub_eq_zero.mp h.2
  conv =>
    enter [1, 1]
    apply Finset.filter_congr hEvalRoot
  simp only [mem_roots', ne_eq, IsRoot.def, Polynomial.eval_sub]
  have : (p - p').roots.card < d := by
    have hSubNe : p - p' ≠ 0 := sub_ne_zero_of_ne hNe
    have hSubDegLt : (p - p').degree < d := lt_of_le_of_lt (degree_sub_le p p') (by simp [hp, hp'])
    have := Polynomial.card_roots hSubNe
    have : (p - p').roots.card < (d : WithBot ℕ) := lt_of_le_of_lt this hSubDegLt
    simp only [Nat.cast_lt] at this
    exact this
  refine Nat.le_sub_one_of_lt (lt_of_le_of_lt ?_ this)
  apply Multiset.card_le_card
  rw [Multiset.le_iff_subset]
  · intro x hx
    rw [mem_roots']
    simpa only [IsRoot.def, Polynomial.eval_sub] using (Multiset.mem_filter.mp hx).2
  · exact Finset.univ.nodup.filter _

theorem distanceLE_polynomial_degreeLE :
    distanceLE (instPolynomialDegreeLT R d) d := by
  intro a b hab
  exact le_trans (distanceLE_polynomial_degreeLT a b hab) (Nat.sub_le d 1)

/-- Schwartz-Zippel-type distance bound for multivariable polynomials of degree ≤ d.
    The bound is `Fintype.card σ * d * Fintype.card R ^ (Fintype.card σ - 1)` (the earlier
    bound `Fintype.card σ * d` was false; see counterexample in comment history). -/
theorem distanceLE_mvPolynomial_degreeLE {σ : Type} [Fintype σ] [DecidableEq σ] :
    distanceLE (instMvPolynomialDegreeLE R d σ)
      (Fintype.card σ * d * Fintype.card R ^ (Fintype.card σ - 1)) := by
  intro a b hab
  have hne : (a : MvPolynomial σ R) - (b : MvPolynomial σ R) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hab (Subtype.ext h)
  have hdeg : ((a : MvPolynomial σ R) - (b : MvPolynomial σ R)).totalDegree
      ≤ Fintype.card σ * d :=
    MvPolynomial.totalDegree_le_card_mul_of_mem_restrictDegree _ d (sub_mem a.2 b.2)
  have hcount := MvPolynomial.card_zeros_le_of_totalDegree_le _ hne hdeg
  refine le_trans (le_of_eq ?_) hcount
  simp only [instMvPolynomialDegreeLE, map_sub, sub_eq_zero]
  rfl

end PolynomialDistance
