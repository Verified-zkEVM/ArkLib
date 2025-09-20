/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Classes.HasSize
import ArkLib.Data.Classes.Initialize
import ArkLib.Data.Classes.Serde
import VCVio
import ArkLib.ToVCVio.SimOracle

/-!
  # Duplex Sponge API (Overwrite Mode)

  This file contains the API for the duplex sponge, which is a sponge that can be used to hash
  data.

  The API is based on the [spongefish](https://github.com/arkworks-rs/spongefish) Rust library.

  The API is designed to be as close as possible to the Rust implementation (as of June 22, 2025).

  The API is subject to change as spongefish changes.
-/

open OracleSpec OracleComp

section move_elsewhere

/-- A class for types with a permutation on it, which is just a function `permute : α → α`. See
  `LawfulPermute` for the requirement that this is actually a permutation. -/
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
def forwardPermutationOracle (α : Type*) : OracleSpec Unit := α →ₒ α

/-- The oracle specification for the backward permutation of a type `α`. Just a wrapper around
`α →ₒ α` -/
@[reducible]
def backwardPermutationOracle (α : Type*) : OracleSpec Unit := α →ₒ α

/-- Oracle specification for an ideal permutation, which is the concatenation of the specifications
  for the forward and backward directions. -/
@[reducible]
def permutationOracle (α : Type*) : OracleSpec PermuteDir :=
  forwardPermutationOracle α ++ₒ backwardPermutationOracle α

end OracleSpec

/-- Canonical implementation of the forward permutation oracle spec with an actual permutation. -/
def forwardPermutationOracleImpl {α : Type*} [Permute α] :
    QueryImpl (forwardPermutationOracle α) Id where
  impl | query () q => Permute.permute (α := α) q

/-- Canonical implementation of the backward permutation oracle spec with an actual (lawful)
  permutation. -/
def backwardPermutationOracleImpl {α : Type*} [Permute α] [LawfulPermute α] :
    QueryImpl (backwardPermutationOracle α) Id where
  impl | query () q => LawfulPermute.permuteInv (α := α) q

/-- Canonical implementation of the permutation oracle spec with an actual permutation.
(of course, during proofs, we would idealize the permutation as being random) -/
def permutationOracleImpl {α : Type*} [Permute α] [LawfulPermute α] :
    QueryImpl (permutationOracle α) Id :=
  SimOracle.append forwardPermutationOracleImpl backwardPermutationOracleImpl

end move_elsewhere

/-- Type class for types that can be used as units in a cryptographic sponge.

Following the [spongefish](https://github.com/arkworks-rs/spongefish) Rust library, we require the
following:

- The type has a zero (i.e. `Zero` in Lean, simpler than a `zeroize` method)
- The type can be serialized and deserialized to/from `ByteArray`
- The type has a fixed size in bytes
- The type implements `write` and `read` methods, which are used to write and read the unit to/from
  an IO stream. They are implemented by default using the `serialize` and `deserialize` methods, and
  the `IO.FS.Stream.{read/write}` functions.
-/
class SpongeUnit (α : Type) extends Zero α, Serde α ByteArray, HasSize α UInt8 where
  /--
  Rust interface:
  ```rust
    /// Write a bunch of units in the wire.
    fn write(bunch: &[Self], w: &mut impl std::io::Write) -> Result<(), std::io::Error>;
  ```
  Default implementation: serialize each unit of `α`, then write to stream
  -/
  write (stream : IO.FS.Stream) : Array α → IO Unit :=
    Array.foldlM (fun _ a => IO.FS.Stream.write stream (serialize a)) ()
  /--
  Rust interface:
  ```rust
    /// Read a bunch of units from the wire
    fn read(r: &mut impl std::io::Read, bunch: &mut [Self]) -> Result<(), std::io::Error>;
  ```
  Default implementation: read `byteSize * array.length` bytes from stream, deserialize each
  unit of `α`, then return the array if there is no error, otherwise throw an error
  -/
  read (stream : IO.FS.Stream) : Array α → IO (Array α) :=
    fun arr => do
      let bytes ← arr.mapM (fun _ => IO.FS.Stream.read stream (USize.ofNat (HasSize.size α UInt8)))
      let units := bytes.mapM deserialize
      if h : units.isSome
        then return units.get h
        else IO.throwServerError "Failed to read units"

/-- Type class for types that can be used as a duplex sponge, with respect to the sponge unit type
  `U`.

Following the [spongefish](https://github.com/arkworks-rs/spongefish) Rust library, we require the
following:

- The type is inhabited (`Default` in Rust), and can be zeroized (i.e. `Zeroize` in Rust)
- The type can be initialized from a 32-byte vector (seed)
- There are 3 methods:
  - `absorbUnchecked` to absorb an array of units in the sponge
  - `squeezeUnchecked` to squeeze out an array of units, changing the state of the sponge
  - `ratchetUnchecked` to ratchet the state of the sponge
-/
class DuplexSpongeInterface (U : Type) [SpongeUnit U] (α : Type*)
    extends Inhabited α, Zero α, Initialize α (Vector UInt8 32) where
  /-- Absorb new elements in the sponge.
  ```rust
    fn absorb_unchecked(&mut self, input: &[U]) -> &mut Self;
  ```
  -/
  absorbUnchecked : α × Array U → α

  /-- Squeeze out new elements, changing the state of the sponge.
  ```rust
    fn squeeze_unchecked(&mut self, output: &mut [U]) -> &mut Self;
  ```
  -/
  squeezeUnchecked : α × Array U → α × Array U

  /-- Ratcheting.
  ```rust
    fn ratchet_unchecked(&mut self) -> &mut Self;
  ```

  More notes from the Rust implementation:
  ```rust
    /// This operations makes sure that different elements are processed in different blocks.
    /// Right now, this is done by:
    /// - permuting the state.
    /// - zero rate elements.
    /// This has the effect that state holds no information about the elements absorbed so far.
    /// The resulting state is compressed.
  ```
  -/
  ratchetUnchecked : α → α


/-- Type class for storing the length & rate of a sponge permutation. -/
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

instance [sz : SpongeSize] : NeZero sz.C where
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

UPDATE: we also move the `permute` function out of the sponge state class, as our functions
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

/-- The canonical sponge state, which is a vector of units of size `N` -/
@[reducible]
def CanonicalSpongeState (U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  Vector U SpongeSize.N

namespace CanonicalSpongeState

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- The rate segment of a canonical sponge state, which is the first `R` elements of the state -/
@[reducible]
def rateSegment (state : CanonicalSpongeState U) : Vector U SpongeSize.R :=
  -- TODO: define an alternate `take` version that directly returns `k` instead of `min k n`
  (Vector.take state SpongeSize.R).cast (by simp)

/-- The capacity segment of a canonical sponge state, which is the last `C` elements of the state -/
@[reducible]
def capacitySegment (state : CanonicalSpongeState U) : Vector U SpongeSize.C :=
  Vector.drop state SpongeSize.R

/-- The canonical sponge state satisfies the `SpongeState` type class -/
instance {U : Type} [SpongeUnit U] [SpongeSize] :
    SpongeState U (Vector U SpongeSize.N) where
  -- PROBLEM: no canonical implementation of this. We temporarily set it to the all-zero vector
  new := fun _ => 0
  get := id
  update := fun _ v => v

end CanonicalSpongeState

/-- A generalized duplex sponge (Rust version), where we may designate the permutation type `C` to
  be any type that satisfies the `SpongeState` type class.

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

/-- The "canonical" duplex sponge (as in the paper) over a sponge unit type U, which consists of the
  following:
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

@[simp, grind] lemma squeezePos_lt_N (sponge : DuplexSponge U C) :
    sponge.squeezePos < SpongeSize.N :=
  lt_of_le_of_lt (Fin.is_le _) (SpongeSize.R_lt_N)

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

/-- Initialize the duplex sponge, assuming access to an oracle from some other type `α` and an
  element `a : α`.

We query the oracle to get the capacity segment of the sponge (the last `C` elements), then set the
rate segment to be all-zero. We also set `absorbPos` to 0 and `squeezePos` to `R`.
-/
def start {α : Type} (a : α) : OracleComp (α →ₒ Vector U SpongeSize.C) (DuplexSponge U C) := do
  let capacitySegment : Vector U SpongeSize.C ← query (spec := α →ₒ Vector U SpongeSize.C) () a
  let vecSponge := (Vector.replicate SpongeSize.R (0 : U)) ++ capacitySegment
  return {
    state := SpongeState.update (α := C) (0 : C) (vecSponge.cast (by simp)),
    absorbPos := 0,
    squeezePos := Fin.last SpongeSize.R
  }

/-- Make DuplexSponge initializable from 32-byte vector.

NOTE: ideally this should be defined in terms of `start` as in the paper, but it is not currently
the case with the Rust code. -/
instance : Initialize (DuplexSponge U C) (Vector UInt8 32) where
  new iv := {
    state := Initialize.new iv,
    absorbPos := 0,
    squeezePos := Fin.last SpongeSize.R
  }

/--
### Absorb a list of units into the sponge (paper version)

Paper algorithm (process one element at a time):
1. Set `i_s' := R` (forces a permutation on the next squeeze).
2. If the input is empty, return immediately.
3. Otherwise:
   - If `absorb_pos < R` then permute the state and set `absorb_pos := 0`.
   - Let `x` be the first input element and `x'` the remaining elements.
   - Overwrite `state[absorb_pos]` with `x` (using `Vector.set`).
   - Set `absorb_pos := absorb_pos + 1` and recursively call on `x'`.

The differences from the Rust version:
1. We use `List` instead of `Array`.
2. We absorb one element at a time, not chunks.

Difference from the paper: we fold the permute into an if-else branch, instead of invoking recursion
on that branch (thus complicating the termination argument). Note also that we have structural
recursion here, which is better behaved definitionally than well-founded recursion.
-/
def absorb (sponge : DuplexSponge U C) (ls : List U) :
    OracleComp (forwardPermutationOracle C) (DuplexSponge U C) :=
  match ls with
  -- If the list is empty, return the sponge with the squeezing index set to the end of the rate
  -- segment
  | [] => pure { sponge with squeezePos := Fin.last SpongeSize.R }
  -- Otherwise, process the list one element at a time
  | x :: xs =>
    -- If the absorbing index is at the end of the rate segment, permute the state, overwrite the
    -- first unit of the state vector with the first element of the list, reset the absorbing index
    -- to one, and set the squeezing index to the end of the rate segment
    if sponge.absorbPos = SpongeSize.R then do
      let permutedState ← query (spec := forwardPermutationOracle _) () (sponge.state)
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

1. Set `squeeze_pos := R` at entry.
2. While `input` is nonempty:
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
  -- Set `squeeze_pos = R` before entering the loop.
  let sponge1 := { sponge with squeezePos := Fin.last SpongeSize.R }
  -- If the array is empty, return the sponge with the squeezing index set to the end of the rate
  -- segment
  if hEmpty : arr.isEmpty then
    return sponge1
  else
    -- If the absorbing index is exactly at the end of the rate segment, we must permute
    -- and reset the absorbing index to 0, then recurse on the same input array.
    if hFull : sponge.absorbPos = SpongeSize.R then do
      -- For termination proof
      have : 0 < sponge.absorbPos := by apply Fin.lt_def.mpr; rw [hFull]; simp
      let permutedState ← query (spec := forwardPermutationOracle _) () (sponge.state)
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
        simp; exact ⟨Array.size_pos_iff.mpr (by simpa using hEmpty), by omega⟩
      absorbFast newSponge (arr.drop chunkSize)
termination_by (arr.size, sponge.absorbPos)

/-- This is the Rust version once we fix an implementation of the permutation. -/
def absorbUnchecked [Permute C] (sponge : DuplexSponge U C) (arr : Array U) : DuplexSponge U C :=
  simulateQ' forwardPermutationOracleImpl (absorbFast sponge arr) (by sorry)

/--
### Squeeze out a vector of units from the sponge (paper version)

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
      let permutedState ← query (spec := forwardPermutationOracle _) () (sponge1.state)
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
        let permutedState ← query (spec := forwardPermutationOracle _) () sponge1.state
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
  simp at h ⊢
  exact ⟨Array.size_pos_iff.mpr (by simpa using hEmpty), h⟩

def squeezeUnchecked [Permute C] (sponge : DuplexSponge U C) (arr : Array U) :
    DuplexSponge U C × Array U :=
  simulateQ' (m := Id) forwardPermutationOracleImpl (squeezeInto sponge arr) (by sorry)

/--
### Ratchet the sponge state for domain separation
Algorithm (from Rust implementation):
1. Permute the state (ensures domain separation from previous operations)
2. Zero out the rate portion: state[0..R] = all zeros
   (This erases any information about previously absorbed elements)
3. Set squeeze_pos = R (forces permutation on next squeeze operation)
-/
def ratchet (sponge : DuplexSponge U C) :
    OracleComp (forwardPermutationOracle C) (DuplexSponge U C) := do
  let permutedState : C ← query (spec := forwardPermutationOracle C) () sponge.state
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

/-- This is the Rust version once we fix an implementation of the permutation. -/
def ratchetUnchecked [Permute C] (sponge : DuplexSponge U C) : DuplexSponge U C :=
  simulateQ' forwardPermutationOracleImpl (ratchet sponge) (by sorry)

/-- Implement DuplexSpongeInterface for DuplexSponge. -/
instance [Inhabited C] [Permute C] : DuplexSpongeInterface U (DuplexSponge U C) where
  absorbUnchecked := fun (sponge, arr) => absorbUnchecked sponge arr
  squeezeUnchecked := fun (sponge, arr) => squeezeUnchecked sponge arr
  ratchetUnchecked := ratchetUnchecked

end DuplexSponge

namespace UInt8

-- Implement SpongeUnit for UInt8

instance : Serialize UInt8 ByteArray where
  serialize byte := ByteArray.mk #[byte]

/-- Deserialize a single byte from a byte array. Gives `none` if the array is not of size 1. -/
instance : DeserializeOption UInt8 ByteArray where
  deserialize bytes :=
    if h : bytes.size = 1 then
      some bytes[0]
    else
      none

instance : Serde UInt8 ByteArray where

instance : HasSize UInt8 UInt8 where
  size := 1
  toFun := ⟨fun byte => #v[byte], by intro x y; simp⟩

instance : SpongeUnit UInt8 where

end UInt8
