/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.OracleComp.SimSemantics.Append

/-!
# Overwrite-mode duplex sponge

The ideal-model sponge for duplex-sponge Fiat–Shamir holds a permutation state and two cursors.
Initialization uses a hash oracle, and absorb and squeeze use only the forward permutation oracle.
-/

@[expose] public section

open OracleSpec OracleComp

namespace OracleSpec

/-- The oracle specification for the forward permutation of a type `α`. Just a wrapper around
`α →ₒ α` -/
@[reducible]
def forwardPermutationOracle (α : Type*) : OracleSpec α := α →ₒ α

/-- The oracle specification for the backward permutation of a type `α`. Just a wrapper around
`α →ₒ α` -/
@[reducible]
def backwardPermutationOracle (α : Type*) : OracleSpec α := α →ₒ α

/-- Oracle specification for an ideal permutation, which is the concatenation of the specifications
  for the forward and backward directions. -/
@[reducible]
def permutationOracle (α : Type*) : OracleSpec (α ⊕ α) :=
  forwardPermutationOracle α + backwardPermutationOracle α

/-- Interpret a fixed permutation in both oracle directions. -/
@[reducible]
def permutationOracleQueryImpl {α : Type} (p : Equiv.Perm α) :
    QueryImpl (permutationOracle α) ProbComp
  | Sum.inl state => pure (p state)
  | Sum.inr state => pure (p.symm state)

end OracleSpec

/-- The alphabet of the sponge has a distinguished zero symbol for the initial rate. -/
class SpongeUnit (α : Type) extends Zero α

/-- **[CO25, Construction 3.3]** Width and rate of a sponge over the alphabet `U`. -/
class SpongeSize (U : Type) where
  /-- The width of the sponge, equal to rate R plus capacity. -/
  N : Nat
  /-- The rate of the sponge. -/
  R : Nat
  /-- The rate is less than the width. -/
  R_lt_N : R < N := by omega
  /-- The rate is non-zero (i.e. positive). -/
  [neZero_R : NeZero R]

attribute [instance] SpongeSize.neZero_R

attribute [simp, grind] SpongeSize.R_lt_N

namespace SpongeSize

variable (U : Type) [sz : SpongeSize U]

/-- The capacity of the sponge, defined as `N - R`, the width minus the rate. -/
def C : Nat := sz.N - sz.R

instance : NeZero (C U) where
  out := by
    have := sz.R_lt_N
    simp [C]; omega

@[simp, grind] lemma R_le_N : sz.R ≤ sz.N := Nat.le_of_lt sz.R_lt_N

@[simp, grind] lemma R_pos : 0 < sz.R := Nat.pos_of_neZero (R U)

@[simp, grind] lemma C_pos : 0 < C U := by simp [C]

@[simp, grind] lemma N_pos : 0 < sz.N := by have := sz.R_lt_N; simp; omega

@[simp, grind =] lemma R_plus_C_eq_N : sz.R + C U = sz.N := by simp [C]

end SpongeSize

/-- View and update the symbol vector of a permutation state. -/
class SpongeState (U : Type) [SpongeUnit U] [SpongeSize U] (α : Type*) extends Zero α where
  /-- Read the symbols of the state. -/
  get : α → Vector U (SpongeSize.N U)
  /-- Replace the symbols of the state. -/
  update : α → Vector U (SpongeSize.N U) → α

namespace SpongeState

variable {U : Type} [SpongeUnit U] [SpongeSize U] {C : Type} [SpongeState U C]

/-- Update the exposed vector representation of the state. -/
def modify (state : C) (f : Vector U (SpongeSize.N U) → Vector U (SpongeSize.N U)) : C :=
  SpongeState.update state (f (SpongeState.get state))

end SpongeState

/-- The canonical permutation state: a vector of `N = R + C` units, i.e. the *permutation state*
  `s ∈ Σ^{r+c}` of [CO25, §3]. The paper's *sponge state* `(s, i_A, i_S)` additionally carries
  the absorb and squeeze cursors; see `DuplexSponge`. -/
@[reducible]
def CanonicalSpongeState (U : Type) [SpongeUnit U] [SpongeSize U] : Type :=
  Vector U (SpongeSize.N U)

namespace CanonicalSpongeState

variable {U : Type} [SpongeUnit U] [SpongeSize U]

/-- `Vector.take` with an exact-length result when a bound proof is available. -/
@[inline] def takeExact {n : Nat} (v : Vector U n) (k : Nat) (h : k ≤ n) : Vector U k :=
  (Vector.take v k).cast (by simp [Nat.min_eq_left h])

/-- The rate segment of a canonical permutation state, which is the first `R` elements of the
  state -/
@[reducible]
def rateSegment (state : CanonicalSpongeState U) : Vector U (SpongeSize.R U) :=
  takeExact state (SpongeSize.R U) (SpongeSize.R_le_N U)

/-- The capacity segment of a canonical permutation state, which is the last `C` elements of the
  state -/
@[reducible]
def capacitySegment (state : CanonicalSpongeState U) : Vector U (SpongeSize.C U) :=
  Vector.drop state (SpongeSize.R U)

/-- Rate and capacity segments recompose the canonical permutation state. -/
lemma rate_capacity_recompose (v : CanonicalSpongeState U) :
    (v.rateSegment.append v.capacitySegment).cast (SpongeSize.R_plus_C_eq_N U) = v := by
  rw [← Vector.toList_inj, Vector.toList_cast]
  have happend : (v.rateSegment.append v.capacitySegment).toList
      = v.rateSegment.toList ++ v.capacitySegment.toList := Vector.toList_append
  rw [happend]
  change ((v.take (SpongeSize.R U)).cast (by simp)).toList ++
    (v.drop (SpongeSize.R U)).toList = v.toList
  simp only [Vector.toList_cast, Vector.toList_take, Vector.toList_drop, List.take_append_drop]
/-- A permutation state's rate and capacity determine it jointly. -/
lemma rate_capacity_injective :
    Function.Injective (fun v : CanonicalSpongeState U => (v.rateSegment, v.capacitySegment)) := by
  intro v w h
  change (v.rateSegment, v.capacitySegment) = (w.rateSegment, w.capacitySegment) at h
  obtain ⟨hr, hc⟩ := Prod.mk.inj h
  rw [← rate_capacity_recompose v, ← rate_capacity_recompose w, hr, hc]

/-- The state `DuplexSponge.start` builds carries the hash answer as its capacity segment. -/
lemma capacitySegment_startState
    (a : Vector U (SpongeSize.C U)) (h : SpongeSize.R U + SpongeSize.C U = SpongeSize.N U) :
    CanonicalSpongeState.capacitySegment (U := U)
      ((Vector.replicate (SpongeSize.R U) (0 : U) ++ a).cast h) = a := by
  change ((Vector.replicate (SpongeSize.R U) (0 : U) ++ a).cast h).drop (SpongeSize.R U) = a
  ext k hk
  simp only [Vector.getElem_drop, Vector.getElem_cast]
  rw [Vector.getElem_append_right (by omega)]
  · simp only [Nat.add_sub_cancel_left]
    rfl
  · omega

/-- The canonical permutation state is its own symbol vector. -/
instance : SpongeState U (Vector U (SpongeSize.N U)) where
  get := id
  update := fun _ v => v

end CanonicalSpongeState

/-- **[CO25, Construction 3.3]** The permutation state and the absorb and squeeze cursors. -/
structure DuplexSponge (U : Type) [SpongeUnit U] [SpongeSize U] (C : Type*)
    [SpongeState U C] where
  /-- The input and output type of the permutation. -/
  state : C
  /-- Current position in the rate portion for absorbing data. -/
  absorbPos : Fin (SpongeSize.R U + 1)
  /-- Current position in the rate portion for squeezing data. -/
  squeezePos : Fin (SpongeSize.R U + 1)
deriving Inhabited

/-- **[CO25, Construction 3.3]** The "canonical" duplex sponge (as in the paper) over a sponge unit
  type U, which consists of the following:
1. A state `Vector U (SpongeSize.N U)`
2. An absorb position `Fin (SpongeSize.R U + 1)`
3. A squeeze position `Fin (SpongeSize.R U + 1)`
-/
@[reducible]
def CanonicalDuplexSponge (U : Type) [SpongeUnit U] [SpongeSize U] :=
  DuplexSponge U (CanonicalSpongeState U)

namespace DuplexSponge

variable {U : Type} [SpongeUnit U] [SpongeSize U] {C : Type} [SpongeState U C]

/-- The zero vector and zero cursors form a duplex sponge state. -/
instance : Zero (DuplexSponge U C) where
  zero := {
    state := 0,
    absorbPos := 0,
    squeezePos := 0
  }

/-- Supporting lemma for **[CO25, Construction 3.3]**: the squeeze position is below the state width
`N`. -/
@[simp, grind] lemma squeezePos_lt_N (sponge : DuplexSponge U C) :
    sponge.squeezePos < SpongeSize.N U :=
  lt_of_le_of_lt (Fin.is_le _) (SpongeSize.R_lt_N (U := U))

/-- Supporting lemma for **[CO25, Construction 3.3]**: the absorb position is below the state width
`N`. -/
@[simp, grind] lemma absorbPos_lt_N (sponge : DuplexSponge U C) :
    sponge.absorbPos < SpongeSize.N U :=
  lt_of_le_of_lt (Fin.is_le _) (SpongeSize.R_lt_N (U := U))

/-- **[CO25, Construction 3.3]** Start the ideal-model duplex sponge. Query the hash oracle
at `a` to fill the capacity and set the rate to zero. The absorb cursor starts at zero and the
squeeze cursor starts at `R`. The salted DSFS construction and its security analysis use this
initializer. -/
def start {α : Type} (a : α) : OracleComp (α →ₒ Vector U (SpongeSize.C U)) (DuplexSponge U C) := do
  let capacitySegment : Vector U (SpongeSize.C U) ← query (spec := α →ₒ Vector U (SpongeSize.C U)) a
  let vecSponge := (Vector.replicate (SpongeSize.R U) (0 : U)) ++ capacitySegment
  return {
    state := SpongeState.update (α := C) (0 : C) (vecSponge.cast (by simp)),
    absorbPos := 0,
    squeezePos := Fin.last (SpongeSize.R U)
  }

/-- **[CO25, Construction 3.3]** Absorb a list of symbols by overwriting the rate.
Permute whenever the absorb cursor reaches the end of the rate. A nonempty absorb moves
the squeeze cursor to the end of the rate and an empty absorb returns the original sponge. -/
def absorb (sponge : DuplexSponge U C) (ls : List U) :
    OracleComp (forwardPermutationOracle C) (DuplexSponge U C) :=
  match ls with
  | [] => pure sponge
  -- Otherwise, process the list one element at a time
  | x :: xs =>
    -- If the absorbing index is at the end of the rate segment, permute the state, overwrite the
    -- first unit of the state vector with the first element of the list, reset the absorbing index
    -- to one, and set the squeezing index to the end of the rate segment
    if sponge.absorbPos = SpongeSize.R U then do
      let permutedState ← query (spec := forwardPermutationOracle _) (sponge.state)
      let newSponge : DuplexSponge U C := {
        state := SpongeState.modify permutedState (Vector.set · 0 x),
        absorbPos := 1
        squeezePos := Fin.last (SpongeSize.R U) }
      -- Then recursively run absorb on the remaining list
      absorb newSponge xs
    else do
      -- Otherwise, overwrite the absorbing index with the first element of the list, increment the
      -- absorbing index, set the squeezing index to the end of the rate segment, and recursively
      -- run absorb on the remaining list
      let newSponge : DuplexSponge U C := {
        state := SpongeState.modify sponge.state (Vector.set · (sponge.absorbPos : Nat) x),
        absorbPos := sponge.absorbPos + 1,
        squeezePos := Fin.last (SpongeSize.R U) }
      absorb newSponge xs

/-- **[CO25, Construction 3.3]** Squeeze the requested number of rate symbols.
A nonempty squeeze resets the absorb cursor and permutes whenever the squeeze cursor reaches
the end of the rate. An empty squeeze returns the original sponge. -/
def squeeze (sponge : DuplexSponge U C) (len : Nat) :
    OracleComp (forwardPermutationOracle C) (Vector U len × DuplexSponge U C) :=
  match len with
  -- If the length is 0, return an empty vector and the same sponge
  | 0 => pure (#v[], sponge)
  -- Otherwise, recursively squeeze out the first element and the rest
  | n + 1 => do
    -- Set absorbing index to zero
    let sponge1 : DuplexSponge U C := { sponge with absorbPos := 0 }
    let sponge2 ← if sponge1.squeezePos = SpongeSize.R U then
      let permutedState ← query (spec := forwardPermutationOracle _) (sponge1.state)
      let sponge2 : DuplexSponge U C := { sponge1 with state := permutedState, squeezePos := 0 }
      pure sponge2
    else
      pure sponge1
    let squeezedVal := (SpongeState.get sponge2.state)[sponge2.squeezePos]
    let sponge3 := { sponge2 with squeezePos := sponge2.squeezePos + 1 }
    -- Recursively squeeze the rest
    let (restVec, sponge4) ← squeeze sponge3 n
    -- Return the concatenation of the squeezed value, the recursive squeezed vector, and the
    -- updated sponge
    return (restVec.insertIdx 0 squeezedVal, sponge4)

/-- Consecutive absorbs are exactly one absorb of the concatenated input. Absorbing an empty
list is a complete no-op, so the empty case is definitional. -/
theorem absorb_append (s : DuplexSponge U C) (xs ys : List U) :
    s.absorb (xs ++ ys) = (do let t ← s.absorb xs; t.absorb ys) := by
  induction xs generalizing s with
  | nil => simp only [List.nil_append, absorb, pure_bind]
  | cons x xs ih =>
    simp only [List.cons_append, absorb]
    split
    · simp only [bind_assoc]
      exact bind_congr fun _ => ih _
    · exact ih _

end DuplexSponge

instance : SpongeUnit UInt8 where
