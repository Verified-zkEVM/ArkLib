/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-!
# Typed tuple fingerprints

A schema assigns a fixed payload width and an injective tag to each of finitely many buses.
`Schema.fingerprint` computes the ascending-power payload encoding with its tag at one global
maximum width. Both schema and raw-key construction check the required representation contracts.

The formal polynomial uses the existing executable `Polynomial.ofFn` coefficient representation.
Its coefficient laws prove injectivity before evaluation; evaluation at a particular challenge
need not be injective. In particular, positive-width bus tags disappear at challenge zero.

The power-order and sign translation lemmas describe mathematical formulas extracted from the
pinned implementation references. They do not assert equivalence of Lean and Rust programs.

## References

The [LogUp implementation comparison](../../../docs/kb/concepts/logup.md) records the pinned
Plonky3 descending-power and Stwo ascending-power conventions. General translation lemmas below
make the bus-tag sign and payload order explicit; the acceptance fixtures record exact revisions.
-/

@[expose] public section

open scoped BigOperators

namespace TaggedTuple

/-- Fixed widths and distinct tags for a finite collection of typed buses. -/
structure Schema (B : Type*) (b W : ℕ) where
  widths : Vector ℕ b
  tags : Vector B b
  width_le : ∀ i : Fin b, widths[i.val] ≤ W
  tags_injective : Function.Injective (fun i : Fin b ↦ tags[i.val])

namespace Schema

variable {B E : Type*} {b W : ℕ}

/-- Check the global width bound and tag uniqueness without enumerating the tag carrier. -/
def mk? [DecidableEq B] (widths : Vector ℕ b) (tags : Vector B b) :
    Option (Schema B b W) :=
  if h : (∀ i : Fin b, widths[i.val] ≤ W) ∧
      Function.Injective (fun i : Fin b ↦ tags[i.val]) then
    some ⟨widths, tags, h.1, h.2⟩
  else none

/-- Construction rejects exactly an oversized width or repeated bus tag. -/
theorem mk?_eq_none_iff [DecidableEq B] (widths : Vector ℕ b) (tags : Vector B b) :
    mk? (W := W) widths tags = none ↔
      ¬ ((∀ i : Fin b, widths[i.val] ≤ W) ∧
        Function.Injective (fun i : Fin b ↦ tags[i.val])) := by
  simp [mk?]

/-- The checked constructor succeeds exactly when the supplied data satisfies the schema. -/
theorem isSome_mk? [DecidableEq B] (widths : Vector ℕ b) (tags : Vector B b) :
    (mk? (W := W) widths tags).isSome ↔
      (∀ i : Fin b, widths[i.val] ≤ W) ∧
        Function.Injective (fun i : Fin b ↦ tags[i.val]) := by
  simp [mk?]

/-- A successfully checked schema retains exactly the supplied widths and tags. -/
theorem data_of_mk?_eq_some [DecidableEq B] {widths : Vector ℕ b} {tags : Vector B b}
    {schema : Schema B b W} (h : mk? widths tags = some schema) :
    schema.widths = widths ∧ schema.tags = tags := by
  unfold mk? at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · contradiction

/-- A semantic key retains its bus and that bus's declared number of payload coordinates. -/
abbrev Key (schema : Schema B b W) := (bus : Fin b) × Vector B schema.widths[bus.val]

/-- Check a raw bus index and payload length before constructing a semantic key. -/
def key? (schema : Schema B b W) (bus : ℕ) (payload : Array B) : Option schema.Key :=
  if hb : bus < b then
    if hp : payload.size = schema.widths[bus] then
      some ⟨⟨bus, hb⟩, ⟨payload, hp⟩⟩
    else none
  else none

/-- Successful key construction preserves both the bus index and all payload entries. -/
theorem data_of_key?_eq_some {schema : Schema B b W} {bus : ℕ} {payload : Array B}
    {key : schema.Key} (h : schema.key? bus payload = some key) :
    key.1.val = bus ∧ key.2.toArray = payload := by
  unfold key? at h
  split at h
  · split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · contradiction
  · contradiction

/-- Rejection means that the bus is absent or its payload has the wrong declared width. -/
theorem key?_eq_none_iff (schema : Schema B b W) (bus : ℕ) (payload : Array B) :
    schema.key? bus payload = none ↔
      ∀ hb : bus < b, payload.size ≠ schema.widths[bus] := by
  simp [key?]

/-- The padded base-field coefficient column: tag at the global width, declared payload below
it, and zero at every other position. This is meaningful row by row even when buses vary. -/
def coefficient [Zero B] (schema : Schema B b W) (key : schema.Key) (j : Fin (W + 1)) : B :=
  if j.val = W then schema.tags[key.1.val]
  else if h : j.val < schema.widths[key.1.val] then key.2[j.val] else 0

/-- The final coefficient column contains the bus tag. -/
@[simp]
theorem coefficient_width [Zero B] (schema : Schema B b W) (key : schema.Key) :
    schema.coefficient key (Fin.last W) = schema.tags[key.1.val] := by
  simp [coefficient]

/-- A column below the declared width contains the corresponding payload coordinate. -/
theorem coefficient_payload [Zero B] (schema : Schema B b W) (key : schema.Key)
    (j : Fin (W + 1)) (hj : j.val < schema.widths[key.1.val]) :
    schema.coefficient key j = key.2[j.val] := by
  have hlt := lt_of_lt_of_le hj (schema.width_le key.1)
  simp [coefficient, Nat.ne_of_lt hlt, hj]

/-- Columns outside the declared payload, other than the tag column, are zero. -/
theorem coefficient_eq_zero [Zero B] (schema : Schema B b W) (key : schema.Key)
    (j : Fin (W + 1)) (hne : j.val ≠ W) (hpad : schema.widths[key.1.val] ≤ j.val) :
    schema.coefficient key j = 0 := by
  simp [coefficient, hne, Nat.not_lt.mpr hpad]

section Semiring

variable [CommSemiring B] [CommSemiring E]

/-- Horner evaluation with the bus tag at the global maximum payload width. -/
def fingerprint (schema : Schema B b W) (f : B →+* E) (beta : E) (key : schema.Key) : E :=
  key.2.toList.foldr (fun a acc ↦ f a + beta * acc)
    (f schema.tags[key.1.val] * beta ^ (W - schema.widths[key.1.val]))

/-- The formal coefficient encoding, using an executable finite coefficient representation. -/
def polynomial [DecidableEq E] (schema : Schema B b W) (f : B →+* E)
    (key : schema.Key) : Polynomial E :=
  Polynomial.ofFn (W + 1) fun j ↦ f (schema.coefficient key j)

/-- The tag occupies a coefficient disjoint from every payload coordinate. -/
@[simp]
theorem coeff_polynomial_width [DecidableEq E] (schema : Schema B b W) (f : B →+* E)
    (key : schema.Key) : (schema.polynomial f key).coeff W = f schema.tags[key.1.val] := by
  simp [polynomial, coefficient]

/-- Each declared payload coordinate is recovered from its formal coefficient. -/
theorem coeff_polynomial_payload [DecidableEq E] (schema : Schema B b W) (f : B →+* E)
    (key : schema.Key) (j : Fin schema.widths[key.1.val]) :
    (schema.polynomial f key).coeff j.val = f key.2[j.val] := by
  have hj : j.val < W := lt_of_lt_of_le j.isLt (schema.width_le key.1)
  rw [polynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)]
  simp [coefficient, Nat.ne_of_lt hj, j.isLt]

/-- Every formal fingerprint has degree at most the global width, including width zero. -/
theorem natDegree_polynomial_le [DecidableEq E] (schema : Schema B b W) (f : B →+* E)
    (key : schema.Key) : (schema.polynomial f key).natDegree ≤ W := by
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)

/-- Distinct typed keys have distinct formal polynomials under an injective coefficient map. -/
theorem polynomial_injective [DecidableEq E] (schema : Schema B b W) (f : B →+* E)
    (hf : Function.Injective f) : Function.Injective (schema.polynomial f) := by
  rintro ⟨bus, payload⟩ ⟨bus', payload'⟩ h
  have hbus : bus = bus' := schema.tags_injective
    (hf (by simpa using congrArg (fun p : Polynomial E ↦ p.coeff W) h))
  subst bus'
  congr 1
  apply Vector.ext
  intro j hj
  apply hf
  simpa only [coeff_polynomial_payload schema f ⟨bus, payload⟩ ⟨j, hj⟩,
    coeff_polynomial_payload schema f ⟨bus, payload'⟩ ⟨j, hj⟩] using
    congrArg (fun p : Polynomial E ↦ p.coeff j) h

private theorem foldr_horner_eq (f : B →+* E) (beta tail : E) (payload : List B) :
    payload.foldr (fun a acc ↦ f a + beta * acc) tail =
      tail * beta ^ payload.length + ∑ j : Fin payload.length, f payload[j.val] * beta ^ j.val := by
  induction payload with
  | nil => simp
  | cons a payload ih =>
    simp only [List.foldr_cons, ih, List.length_cons, Fin.sum_univ_succ,
      Fin.val_zero, List.getElem_cons_zero, pow_zero, mul_one, Fin.val_succ,
      List.getElem_cons_succ]
    rw [mul_add, Finset.mul_sum]
    have hsum :
        (∑ j : Fin payload.length, beta * (f payload[j.val] * beta ^ j.val)) =
          ∑ j : Fin payload.length, f payload[j.val] * beta ^ (j.val + 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    rw [hsum, pow_succ]
    ring

/-- The Horner implementation has ascending payload powers and the tag at the global width. -/
theorem fingerprint_eq_sum (schema : Schema B b W) (f : B →+* E) (beta : E)
    (key : schema.Key) :
    schema.fingerprint f beta key = f schema.tags[key.1.val] * beta ^ W +
      ∑ j : Fin schema.widths[key.1.val], f key.2[j.val] * beta ^ j.val := by
  rw [fingerprint, foldr_horner_eq]
  simp only [Vector.length_toList, Vector.getElem_toList]
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (schema.width_le key.1)]
  congr 1
  exact Fintype.sum_equiv (finCongr Vector.length_toList) _ _ (fun _ ↦ rfl)

private theorem coeff_sum_monomial {n j : ℕ} (v : Fin n → E) :
    (∑ i : Fin n, Polynomial.monomial i.val (v i)).coeff j =
      if h : j < n then v ⟨j, h⟩ else 0 := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  split
  · next h =>
      rw [Finset.sum_eq_single ⟨j, h⟩]
      · simp
      · intro i _ hi
        apply ite_eq_right
        intro hij
        exact hi (Fin.ext hij)
      · simp
  · next h =>
      apply Finset.sum_eq_zero
      intro i _
      apply ite_eq_right
      intro hij
      exact h (hij ▸ i.isLt)

/-- The formal coefficient representation is the canonical tag-plus-payload polynomial. -/
theorem polynomial_eq_sum [DecidableEq E] (schema : Schema B b W) (f : B →+* E)
    (key : schema.Key) :
    schema.polynomial f key = Polynomial.C (f schema.tags[key.1.val]) * Polynomial.X ^ W +
      ∑ j : Fin schema.widths[key.1.val], Polynomial.monomial j.val (f key.2[j.val]) := by
  ext j
  rw [Polynomial.coeff_add, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial,
    coeff_sum_monomial]
  by_cases hj : j < W + 1
  · rw [polynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
    by_cases heq : j = W
    · subst j
      simp [coefficient, Nat.not_lt.mpr (schema.width_le key.1)]
    · by_cases hw : j < schema.widths[key.1.val]
      · simp [coefficient, heq, Ne.symm heq, hw]
      · simp [coefficient, heq, Ne.symm heq, hw]
  · rw [polynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
    have hw : ¬ j < schema.widths[key.1.val] := by
      have := schema.width_le key.1
      omega
    simp [hw, show W ≠ j by omega]

/-- Evaluating the executable formal view agrees with the Horner fingerprint. -/
theorem eval_polynomial [DecidableEq E] (schema : Schema B b W) (f : B →+* E)
    (beta : E) (key : schema.Key) :
    (schema.polynomial f key).eval beta = schema.fingerprint f beta key := by
  rw [polynomial_eq_sum, fingerprint_eq_sum]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

/-- The scalar fingerprint is a linear combination of fixed-width base coefficient columns.
Thus a source can interpolate those columns without interpreting a semantic key off the cube. -/
theorem fingerprint_eq_sum_coefficient (schema : Schema B b W) (f : B →+* E)
    (beta : E) (key : schema.Key) :
    schema.fingerprint f beta key =
      ∑ j : Fin (W + 1), f (schema.coefficient key j) * beta ^ j.val := by
  classical
  rw [← eval_polynomial, polynomial, Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Reversing payload coordinates translates ascending powers to descending Horner order. -/
theorem fingerprint_reverse_eq_foldl (schema : Schema B b W) (f : B →+* E)
    (beta : E) (bus : Fin b) (payload : Vector B schema.widths[bus.val]) :
    schema.fingerprint f beta ⟨bus, payload.reverse⟩ =
      f schema.tags[bus.val] * beta ^ W +
        payload.toList.foldl (fun acc a ↦ f a + acc * beta) 0 := by
  rw [fingerprint_eq_sum, List.foldl_eq_foldr_reverse]
  simp only [← Vector.toList_reverse]
  simp_rw [mul_comm _ beta]
  rw [foldr_horner_eq]
  simp only [Vector.getElem_reverse, Vector.toList_reverse, List.length_reverse,
    Vector.length_toList, zero_mul, List.getElem_reverse, Vector.getElem_toList, zero_add]
  congr 1
  exact (Fintype.sum_equiv (finCongr Vector.length_toList) _ _ (fun _ ↦ rfl)).symm

/-- With no payload coordinates, the fingerprint is the bus tag for every challenge. -/
theorem fingerprint_width_zero (schema : Schema B b 0) (f : B →+* E)
    (beta : E) (key : schema.Key) :
    schema.fingerprint f beta key = f schema.tags[key.1.val] := by
  have hw : schema.widths[key.1.val] = 0 := Nat.eq_zero_of_le_zero (schema.width_le key.1)
  rw [fingerprint_eq_sum]
  simp [hw]

end Semiring

section Ring

variable [CommRing B] [CommRing E]

/-- A negative tag and reversed coordinates translate a positive bus offset minus descending
payload powers into an offset minus the canonical fingerprint. -/
theorem sub_fingerprint_reverse_of_tag_eq_neg (schema : Schema B b W) (f : B →+* E)
    (alpha beta : E) (bus : Fin b) (payload : Vector B schema.widths[bus.val])
    (sourceTag : B) (htag : schema.tags[bus.val] = -sourceTag) :
    alpha - schema.fingerprint f beta ⟨bus, payload.reverse⟩ =
      alpha + f sourceTag * beta ^ W -
        payload.toList.foldl (fun acc a ↦ f a + acc * beta) 0 := by
  rw [fingerprint_reverse_eq_foldl, htag, map_neg]
  ring

/-- At zero tag the canonical payload uses ascending powers; subtracting an offset gives the
ascending-power combiner, the negative of the offset-minus-fingerprint denominator. -/
theorem fingerprint_sub_of_tag_eq_zero (schema : Schema B b W) (f : B →+* E)
    (offset beta : E) (bus : Fin b) (payload : Vector B schema.widths[bus.val])
    (htag : schema.tags[bus.val] = 0) :
    schema.fingerprint f beta ⟨bus, payload⟩ - offset =
      (∑ j : Fin schema.widths[bus.val], f payload[j.val] * beta ^ j.val) - offset := by
  simp [fingerprint_eq_sum, htag]

end Ring

end Schema
end TaggedTuple
