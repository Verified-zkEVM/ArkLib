/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Data.Polynomial.TaggedTupleProbability
import CompPoly.Fields.KoalaBear.Ext6
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-!
# Executable typed fingerprints and selected-key isolation

Source-convention fixtures quote mathematical equations extracted from the exact pinned
revisions below. They do not execute Rust or prove cross-language equivalence.
-/

open TaggedTuple OracleComp
open scoped BigOperators ProbabilityTheory ENNReal

namespace TaggedTupleTest

abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def schema : Schema F 2 3 where
  widths := #v[2, 1]
  tags := #v[2, 4]
  width_le := by decide
  tags_injective := by decide

def key : schema.Key := ⟨0, #v[3, 5]⟩

-- All checked boundaries are executable, including the empty schema and width zero.
example : (Schema.mk? (W := 3) #v[2, 1] (#v[2, 4] : Vector F 2)).isSome := by decide
example : Schema.mk? (W := 3) #v[2, 1] (#v[2, 2] : Vector F 2) = none := by decide
example : Schema.mk? (W := 1) #v[2, 1] (#v[2, 4] : Vector F 2) = none := by decide
example : (Schema.mk? (W := 0) #v[0, 0] (#v[0, 1] : Vector F 2)).isSome := by decide
example : (Schema.mk? (W := 0) (#v[] : Vector Nat 0) (#v[] : Vector F 0)).isSome := by decide
example : schema.key? 0 #[3, 5] = some key := by decide
example : schema.key? 2 #[3, 5] = none := by decide
example : schema.key? 0 #[3, 5, 0] = none := by decide
example : schema.key? 1 #[3, 5] = none := by decide

def genericFingerprint {B E : Type} [CommSemiring B] [CommSemiring E] {b W : Nat}
    (s : Schema B b W) (f : B →+* E) (beta : E) (k : s.Key) : E :=
  s.fingerprint f beta k

def genericPolynomial {B E : Type} [CommSemiring B] [CommSemiring E] [DecidableEq E]
    {b W : Nat} (s : Schema B b W) (f : B →+* E) (k : s.Key) : Polynomial E :=
  s.polynomial f k

def genericCoefficient {B : Type} [Zero B] {b W : Nat}
    (s : Schema B b W) (k : s.Key) (j : Fin (W + 1)) : B := s.coefficient k j

example : genericFingerprint schema (RingHom.id F) 2 key = 12 := by decide
example : (genericPolynomial schema (RingHom.id F) key).coeff 0 = 3 := by decide
example : (genericPolynomial schema (RingHom.id F) key).coeff 1 = 5 := by decide
example : (genericPolynomial schema (RingHom.id F) key).coeff 2 = 0 := by decide
example : (genericPolynomial schema (RingHom.id F) key).coeff 3 = 2 := by decide
example : (genericPolynomial schema (RingHom.id F) key).coeff 4 = 0 := by decide

example : Function.Injective (schema.polynomial (RingHom.id F)) :=
  schema.polynomial_injective _ Function.injective_id
example : (schema.polynomial (RingHom.id F) key).natDegree ≤ 3 :=
  schema.natDegree_polynomial_le _ _
example (beta : F) : (schema.polynomial (RingHom.id F) key).eval beta =
    schema.fingerprint (RingHom.id F) beta key := schema.eval_polynomial _ _ _

-- Row-dependent buses are interpolated through padded coefficient columns, not by asking
-- for a semantic bus or payload at a non-Boolean field point.
def rowKey1 : schema.Key := ⟨1, #v[7]⟩
def interpolatedCoefficient (x : F) (j : Fin 4) : F :=
  (1-x) * genericCoefficient schema key j + x * genericCoefficient schema rowKey1 j
example (x beta : F) :
    (1-x) * schema.fingerprint (RingHom.id F) beta key +
      x * schema.fingerprint (RingHom.id F) beta rowKey1 =
        ∑ j : Fin 4, interpolatedCoefficient x j * beta ^ j.val := by
  rw [Schema.fingerprint_eq_sum_coefficient, Schema.fingerprint_eq_sum_coefficient]
  simp only [RingHom.id_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [interpolatedCoefficient, genericCoefficient]
  ring
example : interpolatedCoefficient 2 3 = 6 := by decide
example : ∀ bus : Fin 2, schema.tags[bus.val] ≠ 6 := by decide
example : (∑ j : Fin 4, interpolatedCoefficient 2 j * (3 : F)^j.val) = 5 := by decide

-- Different buses with identical payloads collide at beta=0 when W>0.
def busSchema : Schema F 2 1 where
  widths := #v[1, 1]
  tags := #v[0, 1]
  width_le := by decide
  tags_injective := by decide
def busKey0 : busSchema.Key := ⟨0, #v[3]⟩
def busKey1 : busSchema.Key := ⟨1, #v[3]⟩
example : busKey0 ≠ busKey1 := by decide
example : busSchema.fingerprint (RingHom.id F) 0 busKey0 =
    busSchema.fingerprint (RingHom.id F) 0 busKey1 := by decide
example : busSchema.polynomial (RingHom.id F) busKey0 ≠
    busSchema.polynomial (RingHom.id F) busKey1 :=
  fun h ↦ (by decide : busKey0 ≠ busKey1) (busSchema.polynomial_injective _ Function.injective_id h)

def emptyPayloads : Schema F 2 0 where
  widths := #v[0, 0]
  tags := #v[0, 1]
  width_le := by decide
  tags_injective := by decide
example (beta : F) : emptyPayloads.fingerprint (RingHom.id F) beta ⟨1, #v[]⟩ = 1 :=
  emptyPayloads.fingerprint_width_zero _ _ _
def emptyKeys : Finset emptyPayloads.Key := {⟨0, #v[]⟩, ⟨1, #v[]⟩}
example : Pr{let beta ← $ᵗ F}[∃ k ∈ emptyKeys.erase ⟨0, #v[]⟩,
    emptyPayloads.fingerprint (RingHom.id F) beta k =
      emptyPayloads.fingerprint (RingHom.id F) beta ⟨0, #v[]⟩] ≤ 0 := by
  simpa only [Nat.mul_zero, Nat.cast_zero, ENNReal.zero_div] using
    emptyPayloads.prob_not_isolated_le (RingHom.id F) Function.injective_id
      emptyKeys ⟨0, #v[]⟩ (by simp [emptyKeys])

-- Erasing the declared width loses semantic information: these raw lists alias.
example (beta : F) : ([3] : List F).foldr (fun a acc ↦ a + beta * acc) 0 =
    ([3, 0] : List F).foldr (fun a acc ↦ a + beta * acc) 0 := by simp
example (beta : F) : ([3] : List F).foldl (fun acc a ↦ a + acc * beta) 0 =
    ([0, 3] : List F).foldl (fun acc a ↦ a + acc * beta) 0 := by simp

-- Plonky3 9734387626cf5a859885de6a6b30dc49532ed96c:
-- lookup/src/logup.rs combine_elements and lookup/src/challenges.rs new.
-- denominator = alpha+(bus+1)*beta^W-descendingHorner(payload).
def negativeTagSchema : Schema F 1 3 where
  widths := #v[2]
  tags := #v[-2]
  width_le := by decide
  tags_injective := by decide

example (alpha beta : F) (payload : Vector F 2) :
    alpha - negativeTagSchema.fingerprint (RingHom.id F) beta ⟨0, payload.reverse⟩ =
      alpha + 2 * beta^3 - payload.toList.foldl (fun acc a ↦ a + acc * beta) 0 :=
  negativeTagSchema.sub_fingerprint_reverse_of_tag_eq_neg _ _ _ _ _ 2 rfl

example : (7 : F) + 2*2^3 - ([3,5] : List F).foldl (fun acc a ↦ a+acc*2) 0 =
    7 - negativeTagSchema.fingerprint (RingHom.id F) 2 ⟨0, #v[5,3]⟩ := by decide

-- A second asymmetric vector avoids the first vector's accidental equality between the
-- raw positive-tag canonical fingerprint and the Plonky3 denominator.
example : schema.fingerprint (RingHom.id F) 3 ⟨0, #v[4,7]⟩ = 11 := by decide
example : (5 : F) + 2*3^3 - ([4,7] : List F).foldl (fun acc a ↦ a+acc*3) 0 = 6 := by decide
example : (5 : F) - negativeTagSchema.fingerprint (RingHom.id F) 3 ⟨0, #v[7,4]⟩ = 6 := by decide
example : schema.fingerprint (RingHom.id F) 3 ⟨0, #v[4,7]⟩ ≠
    5 - negativeTagSchema.fingerprint (RingHom.id F) 3 ⟨0, #v[7,4]⟩ := by decide

-- Stwo 826591c6c371376810ca8213b5812d5daf6d5092:
-- constraint-framework/src/logup.rs combine = sum_j value[j]*alpha^j-z.
def payloadSchema : Schema F 1 2 where
  widths := #v[2]
  tags := #v[0]
  width_le := by decide
  tags_injective := by decide
example (z beta : F) (payload : Vector F 2) :
    payloadSchema.fingerprint (RingHom.id F) beta ⟨0, payload⟩ - z =
      (∑ j : Fin 2, payload[j.val] * beta^j.val) - z :=
  payloadSchema.fingerprint_sub_of_tag_eq_zero _ _ _ _ _ rfl
example : payloadSchema.fingerprint (RingHom.id F) 2 ⟨0, #v[3,5]⟩ - 7 = 6 := by decide

-- OpenVM 362c7ad8c6b042b320471a137e3eadec7ec69a44: single.rs eval_interactions
-- places tag at OWN width w. It agrees with global W only after the stated correction.
example : (2*2^2 + 3 + 5*2 : F) = 4 := by decide
example : schema.fingerprint (RingHom.id F) 2 key = (4 + 2*(2^3-2^2) : F) := by decide
-- Distinct tags alone do not protect its own-width convention from a zero leading tag.
example (beta : F) : 1*beta^1 + 0 = 0*beta^2 + (0 + 1*beta) := by ring

-- SP1 d83ed91f96701209613720708f36ffce0e98ed33: execution.rs generate_interaction_vals.
-- Supplied coefficients [4,6], argument2, payload[3], alpha7. These coefficients are not
-- asserted to equal powers of one beta or a particular partial_lagrange seed output.
example : (7 + 4*2 + 6*3 : F) = 16 := by decide

def pairSchema : Schema F 2 1 where
  widths := #v[1,1]
  tags := #v[0,1]
  width_le := by decide
  tags_injective := by decide
def pairKeys (i : Fin 2) : pairSchema.Key :=
  ⟨i, Vector.replicate pairSchema.widths[i.val] (0 : F)⟩
def pairWeights (i : Fin 2) : F := if i = 0 then 1 else -1

theorem pairKeys_card : (Finset.univ.image pairKeys).card = 2 := by decide

example : Finset.univ.sumFiber pairKeys pairWeights (pairKeys 0) = 1 := by decide

theorem pair_selected_bound :
    Pr{let beta ← $ᵗ F}[Finset.univ.sumFiber
      (pairSchema.fingerprint (RingHom.id F) beta ∘ pairKeys) pairWeights
      (pairSchema.fingerprint (RingHom.id F) beta (pairKeys 0)) = 0] ≤ (1 : ℝ≥0∞)/17 := by
  simpa only [pairKeys_card, Nat.reduceSub, Nat.reduceMul, Nat.cast_one, ZMod.card,
    Nat.cast_ofNat] using
      pairSchema.prob_sumFiber_fingerprint_eq_zero_le (RingHom.id F) Function.injective_id
        Finset.univ pairKeys pairWeights (pairKeys 0) (by decide)

theorem pair_selected_event (beta : F) :
    Finset.univ.sumFiber (pairSchema.fingerprint (RingHom.id F) beta ∘ pairKeys) pairWeights
      (pairSchema.fingerprint (RingHom.id F) beta (pairKeys 0)) = 0 ↔ beta = 0 := by
  have hzero : pairSchema.fingerprint (RingHom.id F) beta (pairKeys 0) = 0 := by
    rw [Schema.fingerprint_eq_sum]
    simp only [pairKeys, Vector.getElem_replicate, RingHom.id_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    change (0 : F) * beta ^ 1 = 0
    exact zero_mul _
  have hone : pairSchema.fingerprint (RingHom.id F) beta (pairKeys 1) = beta := by
    rw [Schema.fingerprint_eq_sum]
    simp only [pairKeys, Vector.getElem_replicate, RingHom.id_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    change (1 : F) * beta ^ 1 = beta
    simp
  simp only [Finset.sumFiber_eq_sum_ite, Fin.sum_univ_two, Function.comp_apply, hzero, hone]
  by_cases h : beta = 0
  · simp [pairWeights, h]
  · simp [pairWeights, h]

theorem pair_selected_probability :
    Pr{let beta ← $ᵗ F}[Finset.univ.sumFiber
      (pairSchema.fingerprint (RingHom.id F) beta ∘ pairKeys) pairWeights
      (pairSchema.fingerprint (RingHom.id F) beta (pairKeys 0)) = 0] = (1 : ℝ≥0∞)/17 := by
  simp only [pair_selected_event]
  rw [SampleableType.prEvent_uniformSample]
  have hcard : ({beta : F | beta = 0} : Finset F).card = 1 := by decide
  simp only [hcard, ZMod.card, Nat.cast_one, Nat.cast_ofNat]

example : Pr{let beta ← $ᵗ F}[∀ encoded, Finset.univ.sumFiber
    (pairSchema.fingerprint (RingHom.id F) beta ∘ pairKeys) pairWeights encoded = 0] ≤
      (1 : ℝ≥0∞)/17 := by
  simpa only [pairKeys_card, Nat.reduceSub, Nat.reduceMul, Nat.cast_one, ZMod.card,
    Nat.cast_ofNat] using
      pairSchema.prob_fingerprint_balanced_le (RingHom.id F) Function.injective_id
        Finset.univ pairKeys pairWeights ⟨pairKeys 0, by decide⟩

example : (1 : ℝ≥0∞)/17 < 1 := by norm_num

-- The selected key remains isolated at beta0 although the OTHER two keys collide.
def threeKeys (i : Fin 3) : payloadSchema.Key :=
  ⟨0, if i = 0 then #v[1,0] else if i = 1 then #v[0,1] else #v[0,2]⟩
def threeWeights (i : Fin 3) : F := ![5,3,-8] i
example : payloadSchema.fingerprint (RingHom.id F) 0 (threeKeys 1) =
    payloadSchema.fingerprint (RingHom.id F) 0 (threeKeys 2) := by decide
example : threeKeys 1 ≠ threeKeys 2 := by decide
example : Finset.univ.sumFiber
    (payloadSchema.fingerprint (RingHom.id F) 0 ∘ threeKeys) threeWeights
    (payloadSchema.fingerprint (RingHom.id F) 0 (threeKeys 0)) =
      Finset.univ.sumFiber threeKeys threeWeights (threeKeys 0) :=
  Finset.sumFiber_comp_eq_of_isolated _ _ _ _ _ (by decide)

-- Balance transports for every beta, independently of collisions.
example (beta : F) (encoded : F) : Finset.univ.sumFiber
    (pairSchema.fingerprint (RingHom.id F) beta ∘ pairKeys) (fun _ ↦ (0 : F)) encoded = 0 :=
  Finset.sumFiber_comp_eq_zero _ _ _ _ (fun _ ↦ by simp [Finset.sumFiber]) _

-- Natural counts can vanish before compression; fingerprints do not repair this premise.
example : (17 : F) = 0 := by decide
example : (17 : Nat) ≠ 0 := by decide
example : Finset.univ.sumFiber (fun _ : Fin 17 ↦ pairKeys 0) (fun _ ↦ (1 : Nat))
    (pairKeys 0) = 17 := by decide
example : Finset.univ.sumFiber (fun _ : Fin 17 ↦ pairKeys 0) (fun _ ↦ (1 : F))
    (pairKeys 0) = 0 := by decide

-- Choosing weights after beta can charge collisions between ANY pair, exceeding selected-key
-- isolation. These three fixed keys encode 0, beta, and 2*beta+1.
def adaptiveSchema : Schema F 3 1 where
  widths := #v[1,1,1]
  tags := #v[0,1,2]
  width_le := by decide
  tags_injective := by decide
def adaptiveKeys (i : Fin 3) : adaptiveSchema.Key :=
  ⟨i, Vector.replicate adaptiveSchema.widths[i.val] (if i = 2 then 1 else 0)⟩
def adaptiveWeights (beta : F) (i : Fin 3) : F :=
  if beta = 0 then ![1,-1,0] i
  else if beta = 8 then ![1,0,-1] i
  else if beta = 16 then ![0,1,-1] i
  else ![1,0,0] i
example : (3 : ℚ)/17 > 2/17 := by norm_num

def extensionSchema : Schema KoalaBear.Field 1 2 where
  widths := #v[2]
  tags := #v[2]
  width_le := by decide
  tags_injective := by decide

def extensionFingerprint (_ : Unit) : KoalaBear.Ext6 :=
  extensionSchema.fingerprint (CompPoly.Extension.Ext.ofBaseRingHom KoalaBear.ext6Params)
    KoalaBear.ext6Gen ⟨0, #v[3,5]⟩

def largeSchema : Schema F 1 100000 where
  widths := #v[100000]
  tags := #v[1]
  width_le := by decide
  tags_injective := by decide
def largeFingerprint (_ : Unit) : F :=
  largeSchema.fingerprint (RingHom.id F) 1 ⟨0, Vector.replicate 100000 0⟩

open Lean Elab Command

run_cmd do
  unless largeFingerprint () == 1 do throwError "large Horner fold failed"
  unless (genericPolynomial schema (RingHom.id F) key).coeff 3 == 2 do
    throwError "executable formal coefficient view failed"
  unless CompPoly.Extension.Ext.coeffs (extensionFingerprint ()) == #v[3,5,2,0,0,0] do
    throwError "nontrivial base-to-extension fingerprint has wrong coefficients"
  let bad := (List.finRange 17).filter fun i ↦
    let beta : F := i.val
    Finset.univ.sumFiber (pairSchema.fingerprint (RingHom.id F) beta ∘ pairKeys)
      pairWeights (pairSchema.fingerprint (RingHom.id F) beta (pairKeys 0)) == 0
  unless bad.length == 1 do throwError "selected-fiber bad-challenge count is not1"
  let adaptBad := (List.finRange 17).filter fun i ↦
    let beta : F := i.val
    (List.finRange 17).all fun j ↦
      Finset.univ.sumFiber (adaptiveSchema.fingerprint (RingHom.id F) beta ∘ adaptiveKeys)
        (adaptiveWeights beta) (j.val : F) == 0
  unless adaptBad.length == 3 do throwError "adaptive-weight collision count is not3"
  unless (List.finRange 17).all (fun i ↦
      (List.finRange 3).any fun j ↦
        Finset.univ.sumFiber adaptiveKeys (adaptiveWeights (i.val : F)) (adaptiveKeys j) != 0) do
    throwError "adaptive counterexample accidentally balances before compression"

run_cmd do
  for name in #[``Schema.mk?, ``Schema.key?, ``Schema.coefficient, ``Schema.fingerprint,
      ``Schema.polynomial, ``genericFingerprint, ``genericPolynomial, ``genericCoefficient,
      ``largeFingerprint, ``extensionFingerprint] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable fingerprint IR for `{name}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Schema.mk?_eq_none_iff, ``Schema.isSome_mk?, ``Schema.data_of_mk?_eq_some,
      ``Schema.data_of_key?_eq_some, ``Schema.key?_eq_none_iff,
      ``Schema.coefficient_width, ``Schema.coefficient_payload, ``Schema.coefficient_eq_zero,
      ``Schema.coeff_polynomial_width, ``Schema.coeff_polynomial_payload,
      ``Schema.natDegree_polynomial_le, ``Schema.polynomial_injective,
      ``Schema.fingerprint_eq_sum, ``Schema.polynomial_eq_sum, ``Schema.eval_polynomial,
      ``Schema.fingerprint_eq_sum_coefficient,
      ``Schema.fingerprint_reverse_eq_foldl, ``Schema.fingerprint_width_zero,
      ``Schema.sub_fingerprint_reverse_of_tag_eq_neg, ``Schema.fingerprint_sub_of_tag_eq_zero,
      ``Probability.prob_polynomial_eval_exists_eq_le, ``Schema.prob_not_isolated_le,
      ``Schema.prob_sumFiber_fingerprint_eq_zero_le, ``Schema.prob_fingerprint_balanced_le,
      ``Finset.sumFiber_comp, ``Finset.sumFiber_comp_eq_zero, ``pair_selected_bound,
      ``pair_selected_event, ``pair_selected_probability] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected fingerprint axiom in `{name}`"

end TaggedTupleTest
