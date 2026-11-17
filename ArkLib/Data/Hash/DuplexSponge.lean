/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Classes.Initialize
public import VCVio.OracleComp.SimSemantics.Append

/-!
  # Duplex Sponge API (Overwrite Mode)

  This file contains the API for the duplex sponge, which is a sponge that can be used to hash
  data.

  The duplex operations are based on the June 2025 version of the
  [spongefish](https://github.com/arkworks-rs/spongefish) Rust library.
-/

@[expose] public section

open OracleSpec OracleComp

section move_elsewhere

/-- **[CO25, Construction 3.3]** A class for types with a permutation on it, which is just a
  function `permute : α → α`. See `LawfulPermute` for the requirement that this is actually a
  permutation. -/
class Permute (α : Type*) where
  permute : α → α

/-- A class with a `Permute` instance is lawful if `permute` is actually a permutation /
  equivalence (i.e. there is a function `permuteInv` such that `permuteInv` is a left and right
  inverse of `permute`) -/
class LawfulPermute (α : Type*) [Permute α] where
  permuteInv : α → α
  left_inv : Function.LeftInverse permuteInv Permute.permute
  right_inv : Function.RightInverse permuteInv Permute.permute

/-- Constructing a `Permute` instance from an `Equiv` -/
@[reducible]
def Permute.ofEquiv (α : Type*) (e : Equiv α α) : Permute α where
  permute := e.toFun

/-- Constructing an `Equiv` from a `Permute` and `LawfulPermute` instances -/
def Equiv.ofLawfulPermute (α : Type*) [Permute α] [LawfulPermute α] : Equiv α α where
  toFun := Permute.permute
  invFun := LawfulPermute.permuteInv
  left_inv := LawfulPermute.left_inv
  right_inv := LawfulPermute.right_inv

/-- Direction of permutation, defined as a wrapper around `Unit ⊕ Unit` -/
abbrev PermuteDir := Unit ⊕ Unit

namespace PermuteDir

/-- Forward direction of the permutation oracle -/
abbrev Fwd : PermuteDir := Sum.inl ()
/-- Backward direction of the permutation oracle -/
abbrev Bwd : PermuteDir := Sum.inr ()

end PermuteDir

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

/-- Canonical implementation of the forward permutation oracle spec with an actual permutation. -/
def forwardPermutationOracleImpl (α : Type*) [Permute α] :
    QueryImpl (forwardPermutationOracle α) Id :=
  Permute.permute (α := α)

/-- Canonical implementation of the backward permutation oracle spec with an actual (lawful)
  permutation. -/
def backwardPermutationOracleImpl (α : Type*) [Permute α] [LawfulPermute α] :
    QueryImpl (backwardPermutationOracle α) Id :=
  LawfulPermute.permuteInv (α := α)

/-- Canonical implementation of the permutation oracle spec with an actual permutation.
(of course, during proofs, we would idealize the permutation as being random) -/
def permutationOracleImpl (α : Type*) [Permute α] [LawfulPermute α] :
    QueryImpl (permutationOracle α) Id :=
  forwardPermutationOracleImpl α + backwardPermutationOracleImpl α

end move_elsewhere

/-- **[CO25, Construction 3.3]** A symbol type for a cryptographic sponge. The zero symbol
initializes sponge states, as in the `Unit` interface of
[spongefish v0.9.0](https://github.com/arkworks-rs/spongefish/blob/v0.9.0/spongefish/src/duplex_sponge.rs#L30-L33). -/
class SpongeUnit (α : Type) extends Zero α

/-- Functional interface for duplex sponge states over the alphabet `U`.

The absorb and squeeze methods correspond to the operations in
[Spongefish v0.9.0](https://github.com/arkworks-rs/spongefish/blob/v0.9.0/spongefish/src/duplex_sponge.rs).
Lean also exposes a zero state, 32-byte initialization through `Initialize`, and a ratchet.
Spongefish exposes session initialization through its separate `DuplexSpongeInit` trait. -/
class DuplexSpongeInterface (U : Type) [SpongeUnit U] (α : Type*)
    extends Inhabited α, Zero α, Initialize α (Vector UInt8 32) where
  /-- Absorb an array of symbols and return the updated sponge. -/
  absorbUnchecked : α × Array U → α
  /-- Fill the output array and return it with the updated sponge. -/
  squeezeUnchecked : α × Array U → α × Array U
  /-- Permute the state, clear the rate, and move the squeeze cursor to the end of the rate. -/
  ratchetUnchecked : α → α

/-- **[CO25, Construction 3.3]** Type class for storing the length & rate of a sponge
permutation. -/
class SpongeSize where
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

variable [sz : SpongeSize]

/-- The capacity of the sponge, defined as `N - R`, the width minus the rate. -/
def C : Nat := sz.N - sz.R

instance : NeZero sz.C where
  out := by
    have := sz.R_lt_N
    simp [C]; omega

@[simp, grind] lemma R_le_N : sz.R ≤ sz.N := Nat.le_of_lt sz.R_lt_N

@[simp, grind] lemma R_pos : 0 < sz.R := Nat.pos_of_neZero R

@[simp, grind] lemma C_pos : 0 < sz.C := by simp [C]

@[simp, grind] lemma N_pos : 0 < sz.N := by have := sz.R_lt_N; simp; omega

@[simp, grind =] lemma R_plus_C_eq_N : sz.R + sz.C = sz.N := by simp [C]

end SpongeSize

/-- Type class for the state of a cryptographic permutation used in the duplex sponge construction.

Rust interface:
```rust
pub trait Permutation: Zeroize + Default + Clone + AsRef<[Self::U]> + AsMut<[Self::U]> {
    type U: Unit;
    const N: usize;  // The width of the sponge
    const R: usize;  // The rate of the sponge
    fn new(iv: [u8; 32]) -> Self;
    fn permute(&mut self);
}
```
Note that we do not quite know how to handle `AsRef` and `AsMut`. My interpretation is that they
basically provide a way to get to the underlying state of the sponge, which is `Vector U N`. Because
of this, I give a tentative API for `AsRef` and `AsMut` basically as a lens between `α` and `Vector
U N` (i.e. `view` and `update`).

UPDATE: we also move the `permute` function out of the `SpongeState` class, as our functions
`absorb/squeeze/ratchet` will be defined as oracle computations (having access to oracle API of a
permutation, i.e. two oracles of type `C → C` for forward and backward directions).

UPDATE: we also modularize this type class by not requiring extra properties like Inhabited. So
really, we just have a lens between `α` and `Vector U N`, along with Zeroize and Initialize.
-/
class SpongeState (U : Type) [SpongeUnit U] [SpongeSize] (α : Type*) extends
    Zero α,
    Initialize α (Vector UInt8 32)
    where
  get : α → Vector U SpongeSize.N
  update : α → Vector U SpongeSize.N → α

namespace SpongeState

-- TODO: this should really be part of a lens package / library

variable {U : Type} [SpongeUnit U] [SpongeSize] {C : Type} [SpongeState U C]

def modify (state : C) (f : Vector U SpongeSize.N → Vector U SpongeSize.N) : C :=
  SpongeState.update state (f (SpongeState.get state))

end SpongeState

/-- The canonical permutation state: a vector of `N = R + C` units, i.e. the *permutation state*
  `s ∈ Σ^{r+c}` of [CO25, §3]. The paper's *sponge state* `(s, i_A, i_S)` additionally carries
  the absorb and squeeze cursors; see `DuplexSponge`. -/
@[reducible]
def CanonicalSpongeState (U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  Vector U SpongeSize.N

namespace CanonicalSpongeState

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- `Vector.take` with an exact-length result when a bound proof is available. -/
@[inline] def takeExact {n : Nat} (v : Vector U n) (k : Nat) (h : k ≤ n) : Vector U k :=
  (Vector.take v k).cast (by simp [Nat.min_eq_left h])

/-- The rate segment of a canonical permutation state, which is the first `R` elements of the
  state -/
@[reducible]
def rateSegment (state : CanonicalSpongeState U) : Vector U SpongeSize.R :=
  takeExact state SpongeSize.R SpongeSize.R_le_N

/-- The capacity segment of a canonical permutation state, which is the last `C` elements of the
  state -/
@[reducible]
def capacitySegment (state : CanonicalSpongeState U) : Vector U SpongeSize.C :=
  Vector.drop state SpongeSize.R

/-- Rate and capacity segments recompose the canonical permutation state. -/
lemma rate_capacity_recompose (v : CanonicalSpongeState U) :
    (v.rateSegment.append v.capacitySegment).cast SpongeSize.R_plus_C_eq_N = v := by
  rw [← Vector.toList_inj, Vector.toList_cast]
  have happend : (v.rateSegment.append v.capacitySegment).toList
      = v.rateSegment.toList ++ v.capacitySegment.toList := Vector.toList_append
  rw [happend]
  change ((v.take SpongeSize.R).cast (by simp)).toList ++
    (v.drop SpongeSize.R).toList = v.toList
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
    (a : Vector U SpongeSize.C) (h : SpongeSize.R + SpongeSize.C = SpongeSize.N) :
    CanonicalSpongeState.capacitySegment (U := U)
      ((Vector.replicate SpongeSize.R (0 : U) ++ a).cast h) = a := by
  change ((Vector.replicate SpongeSize.R (0 : U) ++ a).cast h).drop SpongeSize.R = a
  ext k hk
  simp only [Vector.getElem_drop, Vector.getElem_cast]
  rw [Vector.getElem_append_right (by omega)]
  · simp only [Nat.add_sub_cancel_left]
    rfl
  · omega

/-- The canonical permutation state satisfies the `SpongeState` type class -/
instance :
    SpongeState U (Vector U SpongeSize.N) where
  -- PROBLEM: no canonical implementation of this. We temporarily set it to the all-zero vector
  new := fun _ => 0
  get := id
  update := fun _ v => v

end CanonicalSpongeState

/-- **[CO25, Construction 3.3]** A generalized duplex sponge (Rust version), where we may designate
  the permutation type `C` to be any type that satisfies the `SpongeState` type class.

  In our formalization, we just instantiate `C = Vector U SpongeSize.N`, which is the "canonical"
  duplex sponge representation.

Rust interface:
```rust
#[derive(Clone, PartialEq, Eq, Default, Zeroize, ZeroizeOnDrop)]
pub struct DuplexSponge<C: Permutation> {
    permutation: C,
    absorb_pos: usize,
    squeeze_pos: usize,
}
```
-/
structure DuplexSponge (U : Type) [SpongeUnit U] [SpongeSize] (C : Type*)
    [SpongeState U C] where
  /-- The state of the permutation used in the duplex sponge -/
  state : C
  /-- Current position in the rate portion for absorbing data (0 ≤ absorbPos ≤ R) -/
  absorbPos : Fin (SpongeSize.R + 1)
  /-- Current position in the rate portion for squeezing data (0 ≤ squeezePos ≤ R) -/
  squeezePos : Fin (SpongeSize.R + 1)
deriving Inhabited

/-- **[CO25, Construction 3.3]** The "canonical" duplex sponge (as in the paper) over a sponge unit
  type U, which consists of the following:
1. A state `Vector U SpongeSize.N`
2. An absorb position `Fin (SpongeSize.R + 1)`
3. A squeeze position `Fin (SpongeSize.R + 1)`
-/
@[reducible]
def CanonicalDuplexSponge (U : Type) [SpongeUnit U] [SpongeSize] :=
  DuplexSponge U (CanonicalSpongeState U)

namespace DuplexSponge

variable {U : Type} [SpongeUnit U] [SpongeSize] {C : Type} [SpongeState U C]

-- Make DuplexSponge zeroizable
instance : Zero (DuplexSponge U C) where
  zero := {
    state := 0,
    absorbPos := 0,
    squeezePos := 0
  }

/-- Supporting lemma for **[CO25, Construction 3.3]**: the squeeze position is below the state width
`N`. -/
@[simp, grind] lemma squeezePos_lt_N (sponge : DuplexSponge U C) :
    sponge.squeezePos < SpongeSize.N :=
  lt_of_le_of_lt (Fin.is_le _) (SpongeSize.R_lt_N)

/-- Supporting lemma for **[CO25, Construction 3.3]**: the absorb position is below the state width
`N`. -/
@[simp, grind] lemma absorbPos_lt_N (sponge : DuplexSponge U C) :
    sponge.absorbPos < SpongeSize.N :=
  lt_of_le_of_lt (Fin.is_le _) (SpongeSize.R_lt_N)

@[simp, grind] lemma fin_chunkSize_lt_N (arrSize : Nat) (i : Fin (min arrSize SpongeSize.R)) :
    i < SpongeSize.N := by
  refine lt_of_le_of_lt ?_ SpongeSize.R_lt_N
  omega

@[simp, grind] lemma fin_chunkSize_plus_absorbPos_lt_N (absorbPos arrSize : Nat)
    (i : Fin (min arrSize (SpongeSize.R - absorbPos))) :
    absorbPos + i < SpongeSize.N := by
  refine lt_of_le_of_lt ?_ SpongeSize.R_lt_N
  omega

/-- **[CO25, Construction 3.3]** Start the ideal-model duplex sponge. Query the hash oracle
at `a` to fill the capacity and set the rate to zero. The absorb cursor starts at zero and the
squeeze cursor starts at `R`. The salted DSFS construction and its security analysis use this
initializer.

`DuplexSponge.absorbInitialObject` instead absorbs an encoded object through the rate from a
fixed zero state. That layout models session initialization for the overwrite-mode sponge in
[Spongefish v0.9.0](https://github.com/arkworks-rs/spongefish/blob/v0.9.0/spongefish/src/duplex_sponge.rs). -/
def start {α : Type} (a : α) : OracleComp (α →ₒ Vector U SpongeSize.C) (DuplexSponge U C) := do
  let capacitySegment : Vector U SpongeSize.C ← query (spec := α →ₒ Vector U SpongeSize.C) a
  let vecSponge := (Vector.replicate SpongeSize.R (0 : U)) ++ capacitySegment
  return {
    state := SpongeState.update (α := C) (0 : C) (vecSponge.cast (by simp)),
    absorbPos := 0,
    squeezePos := Fin.last SpongeSize.R
  }

/-- Delegate initialization to the underlying state instance, with cursors zero and `R`.
The canonical vector state instance ignores the seed and returns the zero state. -/
instance : Initialize (DuplexSponge U C) (Vector UInt8 32) where
  new iv := {
    state := Initialize.new iv,
    absorbPos := 0,
    squeezePos := Fin.last SpongeSize.R
  }

/-- **[CO25, Construction 3.3]** Absorb a list of units into the sponge (paper version).

Paper algorithm (process one element at a time):
1. If the input is empty, return immediately — absorbing nothing is a complete no-op.
2. Otherwise, set `i_s' := R` (forces a permutation on the next squeeze) and:
   - If `absorb_pos = R` then permute the state and set `absorb_pos := 0`.
   - Let `x` be the first input element and `x'` the remaining elements.
   - Overwrite `state[absorb_pos]` with `x` (using `Vector.set`).
   - Set `absorb_pos := absorb_pos + 1` and recursively call on `x'`.

The differences from the Rust version:
1. We use `List` instead of `Array`.
2. We absorb one element at a time, not chunks.

Difference from the paper: we fold the permute into an if-else branch, instead of invoking recursion
on that branch (thus complicating the termination argument). Note also that we have structural
recursion here, which is better behaved definitionally than well-founded recursion.

Note on the empty input: absorbing the empty list leaves the sponge **completely** untouched, in
particular it does not re-arm the squeeze pointer at `R`. This aligns the model with the reference
implementation `spongefish/src/duplex_sponge.rs`, whose `absorb(&[])` never touches `squeeze_pos`
(and dually `squeeze(&mut [])` is a no-op, which the Lean `squeeze` already matches).
-/
def absorb (sponge : DuplexSponge U C) (ls : List U) :
    OracleComp (forwardPermutationOracle C) (DuplexSponge U C) :=
  match ls with
  -- If the list is empty, return the sponge unchanged (a complete no-op: the squeezing index is
  -- *not* re-armed, matching the reference Rust implementation)
  | [] => pure sponge
  -- Otherwise, process the list one element at a time
  | x :: xs =>
    -- If the absorbing index is at the end of the rate segment, permute the state, overwrite the
    -- first unit of the state vector with the first element of the list, reset the absorbing index
    -- to one, and set the squeezing index to the end of the rate segment
    if sponge.absorbPos = SpongeSize.R then do
      let permutedState ← query (spec := forwardPermutationOracle _) (sponge.state)
      let newSponge : DuplexSponge U C := {
        state := SpongeState.modify permutedState (Vector.set · 0 x),
        absorbPos := 1
        squeezePos := Fin.last SpongeSize.R }
      -- Then recursively run absorb on the remaining list
      absorb newSponge xs
    else do
      -- Otherwise, overwrite the absorbing index with the first element of the list, increment the
      -- absorbing index, set the squeezing index to the end of the rate segment, and recursively
      -- run absorb on the remaining list
      let newSponge : DuplexSponge U C := {
        state := SpongeState.modify sponge.state (Vector.set · (sponge.absorbPos : Nat) x),
        absorbPos := sponge.absorbPos + 1,
        squeezePos := Fin.last SpongeSize.R }
      absorb newSponge xs

/--
### Absorb an array of units into the sponge (Rust version)

Difference from the paper version: we absorb chunks at a time, not a single element at a time.

1. If `input` is empty, return immediately — a complete no-op that in particular does *not*
   re-arm the squeeze pointer, mirroring the early return in `duplex_sponge.rs`'s `absorb`
   (see its `empty_absorb_is_a_no_op` test).
2. Set `squeeze_pos := R`.
3. While `input` is nonempty:
   - If `absorb_pos == R` (rate full):
     • Permute the state and reset `absorb_pos := 0`.
     • Continue with the same `input` (no input consumed in this step).
   - Else:
     • `chunk_len := min(input.len, R - absorb_pos)`.
     • Copy `chunk_len` items from `input` into `state[absorb_pos .. absorb_pos + chunk_len)`.
     • Update `absorb_pos += chunk_len` and drop `chunk_len` from `input`.

To guide Lean's termination proof, we use the pair `(arr.size, absorbPos)` (with lex order)
as the termination measure.
-/
def absorbFast (sponge : DuplexSponge U C) (arr : Array U) :
    OracleComp (forwardPermutationOracle C) (DuplexSponge U C) := do
  -- If the array is empty, return the sponge unchanged (a complete no-op: the squeezing index
  -- is *not* re-armed, matching the early return in the reference Rust implementation)
  if hEmpty : arr.isEmpty then
    return sponge
  else
    -- Set `squeeze_pos = R` before entering the loop.
    let sponge1 : DuplexSponge U C := { sponge with squeezePos := Fin.last SpongeSize.R }
    -- If the absorbing index is exactly at the end of the rate segment, we must permute
    -- and reset the absorbing index to 0, then recurse on the same input array.
    if hFull : sponge.absorbPos = SpongeSize.R then do
      -- For termination proof
      have : 0 < sponge.absorbPos := by apply Fin.lt_def.mpr; rw [hFull]; simp
      let permutedState ← query (spec := forwardPermutationOracle _) (sponge.state)
      let newSponge : DuplexSponge U C := { sponge1 with state := permutedState, absorbPos := 0 }
      absorbFast newSponge arr
    else do
      -- Otherwise we have available rate space. Compute the maximal chunk that fits.
      let chunkSize := min arr.size (SpongeSize.R - sponge.absorbPos)
      -- Copy that chunk from the input array into the rate slice of the state.
      let vecState : Vector U _ := SpongeState.get sponge1.state
      let newVecState := Fin.foldl chunkSize
        (fun vec i => vec.set (sponge.absorbPos + i) arr[i]) vecState
      -- Update the state, and advance the absorbing index by `chunkSize`
      let newSponge := { sponge1 with
        state := SpongeState.update sponge1.state newVecState,
        absorbPos := sponge.absorbPos + ⟨chunkSize, by omega⟩ }
      -- For termination proof
      have : arr.size - min arr.size (SpongeSize.R - ↑sponge.absorbPos) < arr.size := by
        simp only [tsub_lt_self_iff, lt_inf_iff, tsub_pos_iff_lt, and_self_left]
        exact ⟨Array.size_pos_iff.mpr (by simpa using hEmpty), by omega⟩
      absorbFast newSponge (arr.drop chunkSize)
termination_by (arr.size, sponge.absorbPos)

/-- This is the Rust version once we fix an implementation of the permutation. -/
def absorbUnchecked [Permute C] (sponge : DuplexSponge U C) (arr : Array U) : DuplexSponge U C :=
  simulateQ (forwardPermutationOracleImpl C) (absorbFast sponge arr)

/-- **[CO25, Construction 3.3]** Squeeze out a vector of units from the sponge (paper version).

We differ from the paper version in that we fold in the permute step into the loop, instead of
having a recursive call with length unchanged (which would not fall under structural recursion).

Compared to the Rust version:
1. We squeeze out a precise number of `len` units, not into an array of undetermined size
2. Our squeezing is done one element at a time, not chunks
-/
def squeeze (sponge : DuplexSponge U C) (len : Nat) :
    OracleComp (forwardPermutationOracle C) (Vector U len × DuplexSponge U C) :=
  match len with
  -- If the length is 0, return an empty vector and the same sponge
  | 0 => pure (#v[], sponge)
  -- Otherwise, recursively squeeze out the first element and the rest
  | n + 1 => do
    -- Set absorbing index to zero
    let sponge1 : DuplexSponge U C := { sponge with absorbPos := 0 }
    let sponge2 ← if sponge1.squeezePos = SpongeSize.R then
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

/--
### Squeeze out an array of units from the sponge (Rust version)

Unlike the paper version which specifies the length of the output, this version squeezes out
the rate segment "into" the given array.

1. If output array is empty, return immediately
2. Process output in chunks:
   - If squeeze_pos == R:
     * Permute the state first
     * Reset squeeze_pos = 0, absorb_pos = 0
   - Calculate chunk_size = min(remaining_output.length, R - squeeze_pos)
   - Copy state[squeeze_pos..squeeze_pos + chunk_size] into output
   - Update squeeze_pos += chunk_size
   - Recursively handle remaining output
3. Return updated sponge and filled output array

Note: Unlike absorb which processes input sequentially, squeeze may need to permute
multiple times if the requested output is larger than what's available in the rate.

We define this operation as an oracle computation having access to a permutation oracle.
-/
def squeezeInto (sponge : DuplexSponge U C) (arr : Array U) :
    OracleComp (forwardPermutationOracle C) (DuplexSponge U C × Array U) := do
  if hEmpty : arr.isEmpty then
    return (sponge, #[])
  else
    -- Set absorbing index to zero
    let sponge1 : DuplexSponge U C := { sponge with absorbPos := 0 }
    -- Permute and reset squeezing index if `squeezePos` is at the end of the rate segment
    -- Note: we need to return an attached proof that `squeezePos` is less than the rate
    -- in order to prove termination
    let ⟨sponge2, h⟩ ←
      if hFull : sponge1.squeezePos = SpongeSize.R then do
        let permutedState ← query (spec := forwardPermutationOracle _) sponge1.state
        let sponge2 : DuplexSponge U C := { sponge1 with state := permutedState, squeezePos := 0 }
        have : sponge2.squeezePos < SpongeSize.R := by simp [sponge2]
        let sponge2WithProof : { s : DuplexSponge U C | s.squeezePos < SpongeSize.R } :=
          ⟨sponge2, this⟩
        pure sponge2WithProof
      else
        let sponge2WithProof : { s : DuplexSponge U C | s.squeezePos < SpongeSize.R } :=
          ⟨sponge1, by simp; omega⟩
        pure sponge2WithProof
    -- Extract the chunk from the state
    let chunkSize := min arr.size (SpongeSize.R - sponge2.squeezePos)
    -- First part of the output array is copied from the vector state from `sponge.squeezePos`
    -- to `sponge.squeezePos + chunkSize`
    let extractedChunk := (SpongeState.get (U := U) sponge2.state).extract
      sponge2.squeezePos (sponge2.squeezePos + chunkSize)
    -- Then, update the squeeze position
    let sponge3 := { sponge2 with
      squeezePos := sponge2.squeezePos + (⟨chunkSize, by omega⟩ : Fin _) }
    -- Remaining array, throwing away the first `chunkSize` elements
    let remainingArr := arr.drop chunkSize
    -- Second part of the output array is obtained via recursively calling `squeeze`
    -- with the remaining array
    let ⟨sponge4, newArray⟩ ← squeezeInto sponge3 remainingArr
    return (sponge4, extractedChunk.toArray ++ newArray)
termination_by arr.size
decreasing_by
  simp only [Array.drop_eq_extract, Array.size_extract, min_self, tsub_lt_self_iff, lt_inf_iff,
    tsub_pos_iff_lt, and_self_left] at h ⊢
  exact ⟨Array.size_pos_iff.mpr (by simpa using hEmpty), h⟩

def squeezeUnchecked [Permute C] (sponge : DuplexSponge U C) (arr : Array U) :
    DuplexSponge U C × Array U :=
  Id.run <| simulateQ (forwardPermutationOracleImpl C) (squeezeInto sponge arr)

/-- Permute the state, clear the rate segment, and move the squeeze cursor to `R` so the next
nonempty squeeze permutes again. The absorb cursor is carried forward. -/
def ratchet (sponge : DuplexSponge U C) :
    OracleComp (forwardPermutationOracle C) (DuplexSponge U C) := do
  let permutedState : C ← query (spec := forwardPermutationOracle C) sponge.state
  -- Use the lens to get the state
  let vecState : Vector U SpongeSize.N := SpongeState.get permutedState
  -- Zero out the rate portion
  let zeroed : Vector U SpongeSize.N :=
    Vector.ofFn (fun i => if i < SpongeSize.R then 0 else vecState[i])
  -- Use the lens to update the state
  let newVecState := SpongeState.update permutedState zeroed
  -- Return the updated state with the squeezing index set to the end of the rate segment
  return { sponge with
    state := newVecState,
    squeezePos := Fin.last SpongeSize.R }

/-- Run `ratchet` with the selected permutation implementation. -/
def ratchetUnchecked [Permute C] (sponge : DuplexSponge U C) : DuplexSponge U C :=
  simulateQ (forwardPermutationOracleImpl C) (ratchet sponge)

/-- Implement DuplexSpongeInterface for DuplexSponge. -/
instance [Inhabited C] [Permute C] : DuplexSpongeInterface U (DuplexSponge U C) where
  absorbUnchecked := fun (sponge, arr) => absorbUnchecked sponge arr
  squeezeUnchecked := fun (sponge, arr) => squeezeUnchecked sponge arr
  ratchetUnchecked := ratchetUnchecked

end DuplexSponge

namespace DuplexSponge

variable {U C : Type} [SpongeUnit U] [SpongeSize] [SpongeState U C]

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
